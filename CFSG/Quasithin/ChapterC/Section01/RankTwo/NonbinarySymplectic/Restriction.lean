module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.InitialReduction
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Restricting an ambient MS-pair to its literal product

For subgroups K and R of a larger group, the MS hypotheses belong to K join R.
The odd-index witness, characteristic subgroups of R, and original quotient
marking are transported through the actual subgroup inclusions. In particular,
no normality in the larger group is required.

Source: Aschbacher--Smith C.1.31 and its application in 11.5.7, pp.135 and 783.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {G : Type*} [Group G] {K R J : Subgroup G}

/-- The actual core quotient is unchanged by restricting the ambient group. -/
@[expose] noncomputable def subgroupOfCoreQuotientEquiv (hKJ : K ≤ J) :
    ((K.subgroupOf J) ⧸ pCore 2 (K.subgroupOf J)) ≃* (K ⧸ pCore 2 K) :=
  QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKJ)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKJ))

/-- This comparison preserves the original quotient map on every representative. -/
theorem subgroupOfCoreQuotientEquiv_mk (hKJ : K ≤ J) (k : K.subgroupOf J) :
    subgroupOfCoreQuotientEquiv hKJ (QuotientGroup.mk' _ k) =
      QuotientGroup.mk' (pCore 2 K) (subgroupOfEquivOfLe hKJ k) := rfl

private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) [C.Characteristic] :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y,hy,rfl⟩ := hx
  refine ⟨((e.trans a).trans e.symm) y,
    characteristic_iff_le_comap.mp inferInstance ((e.trans a).trans e.symm) hy, ?_⟩
  exact e.apply_symm_apply _

/-- Relative MS3 becomes intrinsic MS3 under the subgroup equivalence for R. -/
theorem msCharacteristic_subgroupOf (hRJ : R ≤ J)
    (hc : ∀ C : Subgroup R, C.Characteristic →
      ((C.map R.subtype).subgroupOf J).Normal → C = ⊥) :
    MSCharacteristicCondition (R.subgroupOf J) := by
  intro C hC hne hn
  let := hC
  let e := subgroupOfEquivOfLe hRJ
  let D := C.map e.toMonoidHom
  let : D.Characteristic := characteristic_map_equiv e C
  have he : (D.map R.subtype).subgroupOf J = C.map (R.subgroupOf J).subtype := by
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le D).trans hRJ)]
    change (C.map e.toMonoidHom).map R.subtype = _
    rw [map_map, map_map]
    rfl
  have hz : D = ⊥ := hc D inferInstance (he.symm ▸ hn)
  exact hne ((map_eq_bot_iff_of_injective C e.injective).mp hz)

/-- The original proper odd-index witness supplies precisely intrinsic MS2(a). -/
theorem msOddIndexRadical_subgroupOf
    (hr : ∃ A : Subgroup G, A < J ∧ Odd (A.subgroupOf J).index ∧ A.pCoreIn 2 = R) :
    MSOddIndexRadical (R.subgroupOf J) := by
  obtain ⟨A,hA,hodd,hcore⟩ := hr
  refine ⟨A.subgroupOf J, lt_top_iff_ne_top.mpr ?_, hodd, ?_⟩
  · intro he
    exact hA.not_ge (subgroupOf_eq_top.mp he)
  · change (A.subgroupOf J).pCoreIn 2 = R.subgroupOf J
    rw [pCoreIn_subgroupOf 2 A J hA.le, hcore]

/-- Construct the intrinsic input in the actual product, using the supplied
original quotient marking rather than choosing from a family disjunction. -/
@[expose] noncomputable def Input.of_join {F : Type*} [Field F] {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (hsq : IsSQTK KnownSimple.IsKnownSimple (K ⊔ R : Subgroup G))
    (hfit : generalizedFitting (K ⊔ R : Subgroup G) = pCore 2 (K ⊔ R : Subgroup G))
    (hK : (K.subgroupOf (K ⊔ R)).IsCComponent)
    (hprod : ∀ g ∈ K ⊔ R, ∃ k ∈ K, ∃ r ∈ R, k * r = g)
    (hodd : ∃ A : Subgroup G, A < K ⊔ R ∧
      Odd (A.subgroupOf (K ⊔ R)).index ∧ A.pCoreIn 2 = R)
    (hchar : ∀ C : Subgroup R, C.Characteristic →
      ((C.map R.subtype).subgroupOf (K ⊔ R)).Normal → C = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.symplecticGroup (Fin 2) F) :
    Input (K.subgroupOf (K ⊔ R)) (R.subgroupOf (K ⊔ R)) n F := by
  refine ⟨hn,hF,hsq,hfit,hK,?_,msOddIndexRadical_subgroupOf hodd,
    msCharacteristic_subgroupOf le_sup_right hchar,
    (subgroupOfCoreQuotientEquiv le_sup_left).trans e⟩
  intro g
  obtain ⟨k,hk,r,hr,he⟩ := hprod g g.property
  exact ⟨⟨k,mem_sup_left hk⟩,hk,⟨r,mem_sup_right hr⟩,hr,Subtype.ext he⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
