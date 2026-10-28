module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Certificate.Block054

/-!
# Checked Tietze proof DAG

Compose the bounded acyclic replay blocks from the literal Schreier inputs.

Source: John Bray, ATLAS `HeG1-P1.M`; see the parent `source/README.md`.
The producer is untrusted; kernel checks supply every word equality.
-/

public section

namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Certificate
open Replay

open Data

theorem valid {G : Type*} [Group G] {g : Nat → G}
    (h : ValidBefore g db initialCount) : ValidBefore g db factCount := Block054.valid h

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Certificate
