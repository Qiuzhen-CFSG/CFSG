module
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# The prime-core quotient of an inner-action join

If a prime-group R normalizes J and acts innerly on the centerless quotient
J/Oₚ(J), the full join JR has the same quotient by its prime core. The
literal conjugation action has range exactly the inner automorphisms;
centerlessness identifies this range with J/Oₚ(J).

The degree-five component argument uses this equivalence for the original
point component and Sylow subgroup, including the M₂₄ and J₄ models.
Source: Aschbacher--Smith, 12.9.3, printed pp.858--859.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ}

/-- An inner-acting prime-group supplement does not change the centerless
prime-core quotient of the normalized subgroup. -/
def pCoreJoinQuotientEquivOfInner (J R : Subgroup G)
    (hn : R ≤ normalizer (J : Set G)) (hp : IsPGroup p R)
    (hz : center (J ⧸ pCore p J) = ⊥)
    (hi : ∀ r : R, pCoreJoinAction p hn (inclusion le_sup_right r) ∈
      MulAut.innerSubgroup (J ⧸ pCore p J)) :
    ((J ⊔ R : Subgroup G) ⧸ pCore p (J ⊔ R : Subgroup G)) ≃* (J ⧸ pCore p J) := by
  let X := J ⊔ R
  let a := pCoreJoinAction p hn
  let I := MulAut.innerSubgroup (J ⧸ pCore p J)
  have hJI : J.subgroupOf X ≤ I.comap a := by
    intro j hj
    change a j ∈ I
    have he : j = inclusion le_sup_left (⟨j,hj⟩ : J) := rfl
    rw [he,pCoreJoinAction_on_component]
    exact ⟨QuotientGroup.mk' (pCore p J) ⟨j,hj⟩,rfl⟩
  have hRI : R.subgroupOf X ≤ I.comap a := by
    intro r hr
    exact hi ⟨r,hr⟩
  have htop : I.comap a = ⊤ := by
    apply top_unique
    have hh := sup_le hJI hRI
    rw [← subgroupOf_sup (show J ≤ X from le_sup_left)
      (show R ≤ X from le_sup_right),subgroupOf_self] at hh
    exact hh
  have hr : a.range = I := by
    apply le_antisymm
    · rintro _ ⟨x,rfl⟩
      exact (htop.symm ▸ mem_top x : x ∈ I.comap a)
    · exact inner_le_pCoreJoinAction_range p hn
  let e := MonoidHom.ofInjective (Theory.GroupTheory.conj_injective_of_center_eq_bot hz)
  exact (pCoreJoinQuotientEquivRange p hn hp hz).trans
    ((MulEquiv.subgroupCongr hr).trans e.symm)

/-- The join equivalence retains the original quotient map on J. -/
theorem pCoreJoinQuotientEquivOfInner_on_component (J R : Subgroup G)
    (hn : R ≤ normalizer (J : Set G)) (hp : IsPGroup p R)
    (hz : center (J ⧸ pCore p J) = ⊥)
    (hi : ∀ r : R, pCoreJoinAction p hn (inclusion le_sup_right r) ∈
      MulAut.innerSubgroup (J ⧸ pCore p J)) (j : J) :
    pCoreJoinQuotientEquivOfInner J R hn hp hz hi
      (QuotientGroup.mk' (pCore p (J ⊔ R : Subgroup G)) (inclusion le_sup_left j)) =
      QuotientGroup.mk' (pCore p J) j := by
  apply Theory.GroupTheory.conj_injective_of_center_eq_bot hz
  change MulAut.conj ((MonoidHom.ofInjective
    (Theory.GroupTheory.conj_injective_of_center_eq_bot hz)).symm _) = _
  rw [MonoidHom.apply_ofInjective_symm]
  exact pCoreJoinAction_on_component p hn j

/-- Inner action makes the image of J fill the literal quotient of JR. -/
theorem map_subgroupOf_pCoreJoin_eq_top_of_inner (J R : Subgroup G)
    (hn : R ≤ normalizer (J : Set G)) (hp : IsPGroup p R)
    (hz : center (J ⧸ pCore p J) = ⊥)
    (hi : ∀ r : R, pCoreJoinAction p hn (inclusion le_sup_right r) ∈
      MulAut.innerSubgroup (J ⧸ pCore p J)) :
    (J.subgroupOf (J ⊔ R)).map (QuotientGroup.mk' (pCore p (J ⊔ R : Subgroup G))) = ⊤ := by
  apply top_unique
  intro x _
  let e := pCoreJoinQuotientEquivOfInner J R hn hp hz hi
  obtain ⟨j,hj⟩ := QuotientGroup.mk'_surjective (pCore p J) (e x)
  refine ⟨inclusion le_sup_left j,j.property,?_⟩
  apply e.injective
  exact (pCoreJoinQuotientEquivOfInner_on_component J R hn hp hz hi j).trans hj
end Subgroup
