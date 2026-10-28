module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.AbelianSourceDouble
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.AbelianSourceFixed

/-!
# The complete abelian branch of C.1.34

The literal commutator core of a small MS pair, when abelian, has order eight,
sixty-four or sixteen. Its section classification supplies one common quotient
marking. The doubled-natural radical inequality completes case (2); the fixed-line
omega-center and point-stabilizer theorems complete case (5). Case (1) already
includes both the block assertion and the whole natural module.

Thus every Sylow subgroup of L ∨ R containing R satisfies the complete source
alternative, with no extra action, radical or stabilizer premise. In the
order-sixteen case the point subgroup is defined by the actual conjugation
action on Q/C_Q(L), has index seven, contains that Sylow subgroup and has
two-core R. All subgroup and quotient conventions are those of `MSPairs`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31–34,
printed pp.135–137; Meierfrankenfeld–Stellmacher, “Pushing up weak BN-pairs
of rank two” (1993), Main Theorem (4), (5), (8).
-/

public section

open Subgroup
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}

/-- The full fixed-line source alternative, including the literal stabilizer
and its two-core, for the original order-sixteen commutator core. -/
theorem SmallMSPair.abelian_source_of_card_sixteen (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 16)
    (S : Subgroup G) (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    ∃ e', MSModuleAlternatives L R S 1 (ZMod 2) e' := by
  obtain ⟨e', h8 | h64 | h16⟩ := h.abelian_source_sections e hc
  · omega
  · omega
  · obtain ⟨hZ, hP⟩ := h.abelian_source_fixed_geometry e hc hcard S hS hRS
    exact ⟨e', Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨e.trans Matrix.PSL3Two.equiv⟩, h16.2.1, h16.2.2, hZ, hP⟩)))⟩

/-- C.1.34 for an abelian core of the actual small MS pair. The same marking
is used throughout the chosen source alternative, and all its additional
centralizer and point-stabilizer clauses are proved from the MS hypotheses. -/
theorem SmallMSPair.abelian_source (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R))
    (S : Subgroup G) (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    ∃ e', MSModuleAlternatives L R S 1 (ZMod 2) e' :=
  h.abelian_source_of_geometry e hc S
    (fun h64 => h.abelian_source_double_not_centralizer_core e hc h64 hS hRS)
    (fun h16 => h.abelian_source_fixed_geometry e hc h16 S hS hRS)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
