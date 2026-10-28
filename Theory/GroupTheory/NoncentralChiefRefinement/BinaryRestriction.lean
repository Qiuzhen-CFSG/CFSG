module

public import Theory.GroupTheory.NoncentralChiefRefinement.BinarySections

/-!
# Restricting chief actions to a subgroup covering the two-core quotient

Let R have full image in H/O₂(H). On each chief section below O₂(H),
O₂(H) acts trivially, so R and H have exactly the same action. Thus the
same literal chief section is R-irreducible, its R-centrality agrees with
H-centrality, and the noncentral counts on an actual chief series coincide.
This compares actors on the original quotient; it does not intersect the
chief-series terms with R.

Source application: the K-chief factors on H_C/V_H in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 13.8.31 and 13.8.28, pp.965–966.
-/

public section

open Subgroup Representation
open scoped IsMulCommutative
namespace NoncentralChiefRefinement
variable {H : Type*} [Group H] [Finite H] (A B : NormalNode H)

theorem chief_restricted_action_same (hc : A ⋖ B) (hp : IsPGroup 2 B.val)
    (R : Subgroup H)
    (hR : Function.Surjective ((QuotientGroup.mk' (pCore 2 H)).comp R.subtype)) :
    ∀ h : H, ∃ r : R, ∀ x, sectionAction A B h x = sectionAction A B r x := by
  let _ := chief_elementary A B hc hp
  let ρ := binarySectionRepresentation A B
  let _ := binarySection_irreducible A B hc
  have hk : pCore 2 H ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let σ := quotientOfLEKer ρ (pCore 2 H) hk
  intro h
  obtain ⟨r, hr⟩ := hR (QuotientGroup.mk' (pCore 2 H) h)
  refine ⟨r, fun x => ?_⟩
  have he : σ (QuotientGroup.mk' (pCore 2 H) h) =
      σ (QuotientGroup.mk' (pCore 2 H) r) := congrArg σ hr.symm
  change ρ h = ρ (r : H) at he
  exact congrArg (fun f : Module.End (ZMod 2) (Additive (Section A B)) =>
    (f (Additive.ofMul x)).toMul) he

theorem chief_restricted_irreducible (hc : A ⋖ B) (hp : IsPGroup 2 B.val)
    (R : Subgroup H)
    (hR : Function.Surjective ((QuotientGroup.mk' (pCore 2 H)).comp R.subtype))
    (D : Subgroup (Section A B))
    (hd : ∀ r : R, ∀ x, x ∈ D → sectionAction A B r x ∈ D) : D = ⊥ ∨ D = ⊤ := by
  apply chief_irreducible A B hc D
  intro h x hx
  obtain ⟨r, hr⟩ := chief_restricted_action_same A B hc hp R hR h
  rw [hr]
  exact hd r x hx

theorem chief_restricted_central_iff (hc : A ⋖ B) (hp : IsPGroup 2 B.val)
    (R : Subgroup H)
    (hR : Function.Surjective ((QuotientGroup.mk' (pCore 2 H)).comp R.subtype)) :
    IsCentral A B ↔ ∀ r : R, ∀ x, sectionAction A B r x = x := by
  rw [isCentral_iff_action]
  constructor
  · exact fun h r x => h r x
  · intro h a x
    obtain ⟨r, hr⟩ := chief_restricted_action_same A B hc hp R hR a
    rw [hr]
    exact h r x

@[expose] noncomputable def ChiefSeries.restrictedNoncentralCount (s : ChiefSeries H) (R : Subgroup H) : ℕ :=
  Nat.card {i : Fin s.length // ¬ ∀ r : R, ∀ x,
    sectionAction (s i.castSucc) (s i.succ) r x = x}

theorem ChiefSeries.restrictedNoncentralCount_eq (s : ChiefSeries H)
    (hp : IsPGroup 2 s.last.val) (R : Subgroup H)
    (hR : Function.Surjective ((QuotientGroup.mk' (pCore 2 H)).comp R.subtype)) :
    s.restrictedNoncentralCount R = s.noncentralTwoCount := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  have hpi : IsPGroup 2 (s i.succ).val := hp.to_le (CompositionSeries.le_last i.succ)
  have hh := chief_restricted_central_iff (s i.castSucc) (s i.succ) (s.step i) hpi R hR
  change (¬ _) ↔ IsPGroup 2 (Section (s i.castSucc) (s i.succ)) ∧ ¬ _
  rw [← hh]
  exact (and_iff_right (hpi.to_quotient _)).symm
end NoncentralChiefRefinement
