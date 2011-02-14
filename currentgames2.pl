#! /usr/bin/env perl
#
# currentgames script, the new and improved version.
#
# Logchecker for ghost++ log files (English ones) that will periodically
# produce flat files (.txt, .json and .xml) with info on the currently
# hosted games. This info includes the game name, number of players needed,
# the list of player in the lobby and some of their stats, and so on.
#
# Mainly used by GhostGraz, a 12+ bot DotA pub on Nothrend (europe.battle.net).
#
# The original version was a bash + sed script that simply looked for the
# last "Need +X players" line in the log file, and provided about 3-10 sec
# accuracy.  This new script guarantees near-1 seconds accuracy, and handles
# private games much better.  Also some other fun features like country,
# stack and leaver detection have been added.
#
# By lordrt <lordrt@6v6dota.com>. Licensed under the GNU GPL 3 License

use FindBin qw($Bin $Script);
use lib "$Bin/lib";
use threads;
use threads::shared;
use Date::Format;
use File::Tail;
use File::Basename;
use Cwd qw(abs_path); 
use File::stat;
use Data::Dumper;
use Devel::StackTrace;
use JSON;

use strict;
use warnings;

my $debug = 1;

my @logfiles :shared;	# list of watched logfiles
my %currentgames :shared; # current status of each bot (hosting / channel) and list of players in the lobby
my $current;

my %dotastats :shared; # numgames, winproc and some other stats. pre-loaded daily for performance reasons.
my $dotastats_lastload = 0;

my %from :shared; # list of ip-to-country and user-to-country assignments

my %leavernames :shared; # list of ppl and ips who have left recently 
my %leaverips :shared;   # may help in detecting multis


sub get_game(**) {
  my $logfile = shift;
  my $gamename = shift;

	if (! exists($currentgames{$logfile})) {
		my %log :shared;
		$currentgames{$logfile} = \%log;
		print "NEW LOGFILE: $logfile\n";
	}
	return $currentgames{$logfile}{$gamename} if exists($currentgames{$logfile}{$gamename});

	print "CREATING NEW GAME: $gamename, log $logfile\n" if ($debug);
	my @oldnames :shared;
	my %players :shared;
	my %game :shared = (
		logfile => $logfile,
		botname => botname($logfile),
		gamename => $gamename,
		oldnames => \@oldnames, # if rehosted

		firstseen => time(),		# time when the first log line was encounterd (log time)
		lastseen => time(),			# time when the last last log line (so far) was encountered
		created => -1,					# time of game creation (available only if the CREATING line was seen)
		started => -1,					# time of game start (loading screen appears)
		stopped => -1,					# time of game en (throne falls or !end or !shutdown is issued)

		need => 10,
		reliable => 0, # if a "Need +X" line or "Creating game" line was seen, meaning we can count on Join/Leave events for need count
		owner => 'lordrt',
		hcl => '',
		players => \%players,
	);
	# detect hcl
	$game{hcl} = $1 if ($gamename =~ /Dota -([a-z]+) /i);

	$currentgames{$logfile}{$gamename} = \%game;
	return \%game;
}

=pod
Determine bot name from logfile path

Logs are generally hosted in /home/ghostXX/ghost.log
where XX is the bot number.

 ie. ghostgraz1 => /home/ghost1/ghost.log

So use basename(dirname) and do some regexp magic.
=cut
sub botname(*) {
	my $logfile = shift;
	print "Checking botname for $logfile\n";

	my $botname = basename(dirname(abs_path($logfile)));
	$botname =~ s/ghost(?:\d)/ghostgraz/;
	return $botname;
}

=pod
Determine the number of players needed to start this game

This is pretty easy if we've been following the game from the start, and
somewhat hard otherwise (esp. with private games where there is no !autostart)
=cut
sub need(*) {
	my $game = shift;
	if ($$game{reliable}) {
		# !autostart is on (either autohosted or turned on manually), or we were following the game
		# from the first (CREATING) game mark, which means we were able to reconstruct need with joins/leaves
		return $$game{need};

	} else {
		# autostart is off, and we have no refererence point. make your best guess.
		# calculate it by hand. note that this may not work corectly if this script was
		# after such a game had been in progress for some time

		my $total = 10;
		$total = 12 if ($$game{gamename} =~ /6\s*v\s*6/);
		my @sofar = grep { $$game{players}{$_}{left} <= 0 } keys %{$$game{players}};
		return $total - @sofar;
	}
}

sub sort_games() {
	# we want the latest reliable game to be sorted lowest
	# if that doesn't exist, return the latest non-reliable with 
	
	# first of all, ignore games that have already started or stopped
	# they are not current
	my ($ignore_a, $ignore_b) = ( 
			($$current{$a}{started} > 0 || $$current{$a}{stopped} > 0),
			($$current{$b}{started} > 0 || $$current{$b}{stopped} > 0)
	);
	if ($ignore_a && $ignore_b) {
		return 0;
	} elsif ($ignore_a) {
		return 1;
	} elsif ($ignore_b) {
		return -1;
	}

	# if both games are old enough for the created time to be set, always grab the newer one
	# this happens if we don't remove old games fast enough, of if the first one was somehow unhosted
	# and we failed to pick up on it
	if ($$current{$a}{created} > 0 && $$current{$b}{created} > 0) {
		return $$current{$b}{created} <=> $$current{$a}{created};
	}

	# we remain with games that have clearly not yet started (=0), or where we don't know that (=-1)
	# here, we should favor reliable games
	if ($$current{$a}{reliable} && $$current{$b}{reliable}) {
		return 0;
	} elsif ($$current{$a}{reliable}) {
		return -1;
	} elsif ($$current{$b}{reliable}) {
		return 1;
	}

	return $$current{$b}{lastseen} <=> $$current{$a}{lastseen};
}

sub current(*) {
	my $logfile = shift;
	
}

sub watchlog() {
  my $logfile = shift;
	my $botname = botname($logfile); 
#  print "Watching log '$logfile' that belongs to bot '$botname'\n";

	# setup a SIGKILL handler so that the puppetmaster() thread can kill us if our log file becomes stale
	$SIG{'KILL'} = sub { threads->exit(); };

  my $file = File::Tail->new(name => $logfile, interval => 0.5, maxinterval => 5, maxbuf => 128*1024, ignore_nonexistant => 1);
  my $line;
  while (defined($line=$file->read)) {
		# [Sat Oct  2 06:31:47 2010] [GAME: Dota -apem GhostGraz #2915] deleting player [fotisgiannak]: has left the game voluntarily
		unless ($line =~ /^\[(.+?)\] \[(.+?)\] (.*)/) {
			print "Strange log line in $logfile:\n  " . $line . "\n" if ($debug);
			next;
		}
		my ($timestamp, $context, $payload) = ($1, $2, $3);

		if ($context =~ /^QUEUED: /) {
			if ($payload =~ qr{^(/w (.*?) )?Creating (public|private) game \[(.*)\].$}) {
				my ($owner, $type, $gamename) = ($2, $3, $4);
				# attempt to create game (may fail, see a bit bellow)
				my $game = get_game($logfile, $gamename);
				if (time() - $$game{firstseen} > 10) {
					print STDERR "Warning, we found a CREATING game line, but a game with that name and bot already exists. Look's like the bot has been restarted. Deleting first game.";
					delete $currentgames{$logfile}{$gamename};
					$game = get_game($logfile, $gamename);
				}

				$$game{created} = time();
				$$game{owner} = $owner;
				$$game{reliable} = 1;

			} elsif ($payload =~ qr{^Game \[(.*?) : (.*?) : (\d+)/(\d+) : (.+)m\] is over.}) {
				my ($gamename, $owner, $numstayed, $numplayers, $duration) = ($1,$2,$3,$4,$5);
				my $game = get_game($logfile, $gamename);
				$$game{stopped} = time();
	
				# clear leavers

			} elsif ($payload =~ qr{^Unable to create game \[(.*?)\] }) {
				# game name too long, already taken, bnet having a period, ..

			} else {
				# whois whisper, whispers to root admin
				next;
			}
		
		} elsif ($context =~ /GAME: (.*)/) {
			my $gamename = $1;
			my $game = get_game($logfile, $gamename);
			$$game{firstseen} = time() unless ($$game{firstseen}); # $timestamp;
			$$game{lastseen} = time(); # $timestamp;

			if ($payload =~ /\[Local\]: (.*)/) {
				# mark the game as for-sure not started yet
				$$game{started} = 0 if $$game{started} == -1;

				# in-lobby messages from the bot
				my $message = $1;

				if ($message =~ /^Waiting for (\d) more players before the game will automatically start./) {
					$$game{need} = $1;
					$$game{reliable} = 1;
					print "[$gamename] need +" . need($game) . "\n" if ($debug);

					report();

				} elsif ($message =~ /^Waiting to start until players have been pinged/) {
					$$game{state} = "ping";
				}

			} elsif ($payload =~ /^\[Lobby\] \[(.*?)\]: /) {
				# mark the game as for-sure not started yet
				$$game{started} = 0 if $$game{started} == -1;

				# in-lobby chat
				# print "INLOBBY CHAT:\n\t$payload\n";
				next;

			} elsif ($payload =~ /^admin \[(.*?)\] sent command \[hcl\] with payload \[(.*)\]/) {
				# hcl changes in-lobby
				# todo make sure that he's root admin / owner if locked / admin in other cases
				# shouldn't be much of an issue tho
				$$game{hcl} = $1;

			} elsif ($payload =~ /^admin \[(.*?)\] sent command \[clearhcl\]/) {
				$$game{hcl} = "";

			} elsif ($payload =~ /^trying to rehost as (public|private) game \[(.*)\]/) {
				my $newtype = $1;
				my $newgamename = $2;

				push(@{$$game{oldnames}}, $gamename); # store old name in case rehost fails
				$currentgames{$logfile}{$newgamename} = $game;
				delete $currentgames{$logfile}{$gamename};

			}	elsif ($payload =~ /^started loading with (\d+) players/) {
				$$game{started} = time();
			
			} elsif ($payload =~ /^successfully encoded HCL command string \[(.*)\]/) {
				# postfix hcl so you can be sure of it (for private games)
				$$game{hcl} = $1;
			
			} elsif ($payload =~ /^player \[(.*?)\|([\d\.]+)\] joined the game/) {
				my ($playername, $ip) = ($1, $2);

				my %player :shared = ( name => $playername, joined => time(), ip => $ip, left => 0, leftreason => '' );
				$$game{players}{$playername} = \%player;
				$$game{need}-- if ($$game{reliable});

				print "[$gamename] need +" . need($game) . " after $playername joined \n" if ($debug);

				# check if known recent leaver
				

			} elsif ($payload =~ /^deleting player \[(.*?)\]: (.*)/) {
				my ($playername, $leftreason) = ($1, $2);

				# it is possible that we started reading the logs after the player had joined
				if (exists($$game{players}{$playername})) {
					# print "DELETING PLAYER: " . Dumper($$game{players}{$playername}) ."\n" if ($debug);
					$$game{players}{$playername}{left} = time();
					$$game{players}{$playername}{leftreason} = $leftreason;
				}
				if ($$game{started} <= 0) {
					$$game{need}++ if ($$game{reliable});
					print "[$gamename] need +" . need($game) . " after $playername left\n" if ($debug);

				} else {
					# whoa, a LEAVER. Log this.
					my %leaver :shared = ( name => $playername, left => time(), game => $game );
					$leavernames{$playername} = \%leaver;
					if (exists($$game{players}{$playername})) {
						$leaver{ip} = $$game{players}{$playername}{ip};
						$leaverips{$$game{players}{$playername}{ip}} = \%leaver;
					}
				}

			} elsif ($payload =~ /^\(\d+:/) {
				# in-game chat
				# mark the game as for-sure started
				$$game{started} = time() if $$game{started} == -1;

				next;
			} else {
				if ($payload =~ /is trying to join the game but is banned/) {
					$$game{started} = 0;
					next;
				} elsif ($payload =~ /^warning - the latency/) {
					$$game{started} = time() if ($$game{started} <= 0); # not perfect, but the best we can do
					next;
				}

				# more junk to ignore
#				print "Unknown [GAME: ] line:\n\t$payload\n";

				next;
			}

		} elsif ($context eq "GHOST" && $payload eq "shutting down") {
		
		} else {
			next;
		}


#    $timestamp = time2str("%c", time);

#    print "$line";
#		print "TIMESTAMP: $timestamp\nCONTEXT:$context\nPAYLOAD: $payload\n\n";

  }
}

sub report() {
	print "CURRENT GAMES for " . join(" -- ", keys %currentgames) . ":\n";
	my @currentgames;

	foreach my $logfile (sort keys %currentgames) {
		my $botname = botname($logfile);
		my $prefix = "[LOG $logfile, BOT $botname]";

		# find the current game for this bot
		$current = $currentgames{$logfile};
		my @gamenames = sort sort_games keys %$current;
		unless (@gamenames) {
			print "$prefix no games atm\n";
		} else {
			my $game = $$current{$gamenames[0]};
			if ($$game{started} > 0 || $$game{stopped} > 0 || time() - $$game{lastseen} > 12*60*3600) {
				print "$prefix games found, but are all obsolete\n";
				next;
			}

			my $copy = {};
			$$copy{gamename} = $$game{gamename};
			$$copy{botname} = $botname;
			$$copy{need} = need($game);
			$$copy{players} = {};
			my $playername;
			foreach (grep { $$game{players}{$_}{left} == 0 } keys %{ $$game{players} }) {
				$$copy{players}{$_} = {
					name => $_,
					statsdota => 'burek'
				};
			}
			# todo: check for stacks
			push(@currentgames, $copy);

#				print "[BOT $botname, LOG $logfile] " . $$game{gamename} .": +" . need($game) . "\n";
#				print "\t\tPLAYERS = " . join(", ", grep { $$game{players}{$_}{left} == 0 } keys %{ $$game{players} }) . "\n";

#				print "OTHER GAMES:\n\t" . join("\n\t", map { $$current{$_}{gamename} . ": +" . need($$current{$_}) . ", reliable: $$current{$_}{reliable}, started: $$current{$_}{started}, stopped: $$current{$_}{stopped}" } @gamenames) . "\n";  
#				print "\n";
		}
	}

	print to_json(\@currentgames, { utf8 => 1, pretty => 1 }) . "\n\n";

}

sub age(*) {
	my $logfile = shift;
	return 20201167 if (! -r $logfile);
	
	return time() - stat($logfile)->mtime;
}

sub puppetmaster() {
	my %threads;
	my $maxage = 24*3600; # ignore logfiles older than 1 day

	while (1) {
		# add new logfiles that pop up
		my @candidates = glob("testlogs/ghost*/ghost.log");
		foreach my $logfile (@candidates) {
			if (age($logfile) > $maxage) {
				print "INFO: Logfile '$logfile' hasn't been updated for more than a day; ignoring\n";
			} else {
				unless(exists($currentgames{$logfile})) {
					my $thr = threads->new(\&watchlog, $logfile);
					$thr->detach();
					$threads{$logfile} = $thr;
	
					print "INFO: Watching logfile: $logfile\n";
				}
			}
		}
		sleep(5);

		# check the old ones, some of them might not be worth watching anymore
		foreach my $logfile (keys %threads) {
			if ($logfile =~ /4/) {
				$threads{$logfile}->kill('KILL');
				print "INFO: Logfile '$logfile' hasn't been updated for more than a day; stopped watching it\n";
				

			}
		}
		my @running = threads->list(threads::running);
		print "Current threads: " . @running . "\n";

		sleep(5);
	}

	return 1;
}

my $puppetmaster = threads->new(\&puppetmaster);
#my $reporter = threads->new(\&mkfeeds);
$puppetmaster->join();
