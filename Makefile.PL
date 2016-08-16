# -*- perl -*-
BEGIN { require 5.006; }
use strict;
use warnings;
use ExtUtils::MakeMaker;
my $PERL_CORE = grep { $_ eq 'PERL_CORE=1' } @ARGV;

WriteMakefile(
  NAME         => q[Sub::Util],
  ABSTRACT     => q[Common Sub utility subroutines],
  AUTHOR       => q[Graham Barr <gbarr@cpan.org>],
  DEFINE       => q[-DPERL_EXT],
  VERSION_FROM => 'lib/Sub/Util.pm',

  # We go through the SubUtil.xs trickery to foil platforms
  # that have the feature combination of
  # (1) static builds
  # (2) allowing only one object by the same name in the static library
  # (3) the object name matching being case-blind
  # This means that we can't have the top-level util.o
  # and the extension-level Util.o in the same build.
  # One such platform is the POSIX-BC BS2000 EBCDIC mainframe platform.
  XS     => {'SubUtil.xs' => 'SubUtil.c'},
  OBJECT => 'SubUtil$(OBJ_EXT)',
  ( $PERL_CORE
    ? ()
    : (
      INSTALLDIRS      => ($] < 5.011 ? q[perl] : q[site]),
      PREREQ_PM        => {
          'Test::More' => 0,
          'List::Util' => '1.46_01',
      },
      (eval { ExtUtils::MakeMaker->VERSION(6.31) } ? (LICENSE => 'perl') : ()),
      (eval { ExtUtils::MakeMaker->VERSION(6.48) } ? (MIN_PERL_VERSION => '5.006') : ()),
      ( eval { ExtUtils::MakeMaker->VERSION(6.46) } ? (
          META_MERGE => {
            'meta-spec' => { version => 2 },
            dynamic_config => 0,
            resources => {    ##
              repository => {
                url => 'https://github.com/Scalar-List-Utils/Sub-Util.git',
                web => 'https://github.com/Scalar-List-Utils/Sub-Util',
                type => 'git',
              },
              bugtracker => {
                mailto => 'bug-Sub-Util@rt.cpan.org',
                web => 'https://rt.cpan.org/Public/Dist/Display.html?Name=Sub-Util',
              },
            },
          }
          )
        : ()
      ),
    )
  ),
);

