module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block000
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block001
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block002
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block003
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block004
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block005
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block006
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block007
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block008
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block009
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block010
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block011
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block012
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block013
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block014
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data.Block015

/-!
# Balanced table of literal group-word equalities

These are syntactic data; Initials and Certificate prove their validity.

Source: John Bray, ATLAS `HeG1-P1.M`; see the parent `source/README.md`.
The producer is untrusted; kernel checks supply every word equality.
-/

@[expose] public section

namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data
open Replay

noncomputable def db (n : Nat) : Fact :=
  (if n < 16384 then (if n < 8192 then (if n < 4096 then (if n < 2048 then Block000.db n else Block001.db n) else (if n < 6144 then Block002.db n else Block003.db n)) else (if n < 12288 then (if n < 10240 then Block004.db n else Block005.db n) else (if n < 14336 then Block006.db n else Block007.db n))) else (if n < 24576 then (if n < 20480 then (if n < 18432 then Block008.db n else Block009.db n) else (if n < 22528 then Block010.db n else Block011.db n)) else (if n < 28672 then (if n < 26624 then Block012.db n else Block013.db n) else (if n < 30720 then Block014.db n else Block015.db n))))

def initialCount : Nat := 3395
def factCount : Nat := 31124

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data
