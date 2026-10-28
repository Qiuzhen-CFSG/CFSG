module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCentralSupplement
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCoreDerived
public import Theory.GroupTheory.Commutator.CentralModuloSupplement

/-!
# Derived-core reduction in the original small-quintic source

The actual core has a supplement central modulo its original quintic span U,
and the geometric argument places U in the derived core. Expanding relative
commutators therefore gives [Q,Q] = U join [C,C], for the literal full
centralizer kernel C. The remaining factor [C,C] is retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original derived core is its quintic span times the full-kernel derived subgroup. -/
theorem source_quintic_core_derived_reduction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let C := H ⊓ centralizer (U : Set G)
    ⁅H.pCoreIn 2,H.pCoreIn 2⁆ = U ⊔ ⁅C,C⁆ := by
  let U := conjugateSpanBy (localModule T M) H
  let C := H ⊓ centralizer (U : Set G)
  let Q := H.pCoreIn 2
  obtain ⟨J,hJQ,hHJ,hJC,hcomm⟩ := source_quintic_full_core_central_supplement
    hG T hempty hM hu hmany hcard e H hH hi
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hHC : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer
      (hHU.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  have hUder : U ≤ ⁅Q,Q⁆ := source_quintic_core_derived_contains_span
    hG T hempty hM hu hmany hcard e H hH hi
  exact commutator_eq_sup_of_central_modulo_supplement Q J C U hJC
    ((pCoreIn_le 2 H).trans hHC) ((pCoreIn_le 2 H).trans hHU) hcomm hUder

end CFSG.Quasithin.Chapter14.Section06
