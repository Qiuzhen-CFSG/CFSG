module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.QuotientStructure
public import Theory.GroupTheory.PCorePreimageCentralizer
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group

/-!
# Lifting competing local overgroups

A subgroup above the image of `M ∩ I` with generalized Fitting subgroup
equal to its two-core lifts through the proved two-kernel to a subgroup
with the same property in `I`. The common Sylow subgroup puts `O₂(I)`
inside this preimage, so it has nontrivial two-core. If it left `M`, it
would contradict the actual outside-overgroup exclusion 15.3.25.

This proves the overgroup part of maximality. The local image itself
must still be proved to have `F* = O₂` before obtaining the `Maximal`
field of `QuotientConditions`. The proof specializes the same preimage
argument used for the rank-two quotient, without its rank-two shadow.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43(e), printed p.1140, referring to the proof of 15.3.41, p.1138.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.ComponentAction
variable {G : Type*} [Group G] [Finite G]

/-- The overgroup bound in 15.3.43(e), by applying 15.3.25 to the actual preimage
of each competing subgroup. Characteristic two lifts through the two-kernel. -/
theorem image_maximal_overgroups
    {I L M Y S : Subgroup G} (d : ComponentAction I L)
    (hIeq : I = L ⊔ S) (hz : (center L).map L.subtype = L.pCoreIn 2)
    (hI : I ∈ outsideFamily Y S M)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hYM : Y ≤ M) (hSM : S ≤ M)
    (h25 : ∀ A ∈ outsideFamily Y S M, generalizedFitting A ≠ pCore 2 A)
    (J : Subgroup d.Quotient) (hMJ : d.image M ≤ J)
    (hJ : generalizedFitting J = pCore 2 J) : J = d.image M := by
  let q := d.quotientMap
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hS : IsPGroup 2 S := hP ▸ P.isPGroup'.map I.subtype
  have hk : IsPGroup 2 q.ker := (show q.ker = d.kernel from QuotientGroup.ker_mk' _).symm ▸
    d.kernel_isTwoGroup hS hIeq hz
  have hr : q.range = ⊤ := q.range_eq_top_of_surjective hq
  let : q.range.Normal := hr ▸ inferInstance
  let X : Subgroup I := J.comap q
  let A : Subgroup G := X.map I.subtype
  have hMX : M.subgroupOf I ≤ X := by
    intro x hx
    exact hMJ (mem_map_of_mem q hx)
  have hAI : A ≤ I := map_subtype_le _
  have hYA : Y ⊔ S ≤ A := by
    intro x hx
    have hxI : x ∈ I := hI.1.2 hx
    have hxM : x ∈ M := (sup_le hYM hSM) hx
    exact ⟨⟨x, hxI⟩, hMX hxM, rfl⟩
  have hcore : I.pCoreIn 2 ≤ A.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I)
    · exact (hP ▸ pCoreIn_le_sylow I P).trans (le_sup_right.trans hYA)
    · exact hAI.trans (I.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image I (pCore 2 I)))
  have hAcore : A.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact hI.1.1 (le_bot_iff.mp (hcore.trans he.le))
  have hCJ : centralizer (pCore 2 J : Set J) ≤ pCore 2 J := by
    rw [← hJ]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  have hCX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X :=
    q.centralizer_pCore_comap_of_normal_range hk J hCJ
  have hCA : centralizer (pCore 2 A : Set A) ≤ pCore 2 A :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2
      (Subgroup.equivMapOfInjective X I.subtype I.subtype_injective)).mp hCX
  have hFA : generalizedFitting A = pCore 2 A :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 hCA
  have hAM : A ≤ M := by
    by_contra hn
    exact h25 A ⟨⟨hAcore, hYA⟩, hn⟩ hFA
  apply le_antisymm _ hMJ
  have hXM : X ≤ M.subgroupOf I := fun x hx => hAM ⟨x, hx, rfl⟩
  calc
    J = X.map q := (map_comap_eq_self_of_surjective hq J).symm
    _ ≤ d.image M := map_mono hXM

end CFSG.Quasithin.Chapter15.Section03.RankOne.ComponentAction
