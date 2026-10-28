module
public import CFSG.Quasithin.ChapterI.Section03.MathieuOddCore
public import CFSG.Quasithin.ChapterI.Section03.MathieuPumpup
public import Theory.GroupAction.CentralKernelFixedComponents
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison

/-!
# Normality of a component containing a Mathieu cover

Two commuting quasisimple M₂₂ covers would give a literal M₂₂ × M₂₂
section after taking the intrinsic component quotients. The quasithin
K-group exclusion therefore prevents distinct conjugates of any ordinary
component containing such a cover. That containing component is normal;
this does not assert equality with the original cover. Restriction to the
containing component and the literal central quotient retain the original
fixed component as a Mathieu cover in the full quotient fixed subgroup.

Source: Aschbacher--Smith I.3.2 and the normality argument in 4.2.13,
printed pp.415 and 612. The exterior application uses the original cubic
residual and the ordinary component supplied by MathieuOddCore.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.MathieuPumpup

private def centralQuotientEquiv {P Q : Type*} [Group P] [Group Q]
    (e : P ≃* Q) : (P ⧸ center P) ≃* (Q ⧸ center Q) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (centerCongr e ⟨z,hz⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

private theorem ordinary_core_eq_center {X : Type*} [Group X] [Finite X]
    {B : Subgroup X} (hB : IsComponent X B) : oddTwoCore B = center B := by
  let : Group.IsSolvable (pPrimeCore 2 B) := odd_order_theorem _
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  rw [(Balance.ordinary_isTwoComponent hB).oddTwoCore_eq_solvableRadical]
  let := hB.2
  exact le_antisymm IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical _ inferInstance
      (Group.isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm))

/-- Two commuting full Mathieu covers cannot lie in a quasithin K-group. -/
theorem no_commuting_mathieu_covers
    {X : Type*} [Group X] [Finite X] (hX : IsQuasithin X)
    (hK : IsKGroup KnownSimple.IsKnownSimple X)
    (B C : Subgroup X) [IsQuasisimple B] [IsQuasisimple C]
    (eB : (B ⧸ center B) ≃* Sporadic.Mathieu.M22)
    (eC : (C ⧸ center C) ≃* Sporadic.Mathieu.M22)
    (hc : B ≤ centralizer (C : Set X)) : False := by
  let Y := B ⊔ C
  let B' := B.subgroupOf Y
  let C' := C.subgroupOf Y
  have hBN : B'.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le B.le_normalizer
      ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)))
  have hCN : C'.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
    (sup_le (hc.trans (Subgroup.centralizer_le_normalizer _)) C.le_normalizer)
  let b : B' ≃* B := subgroupOfEquivOfLe le_sup_left
  let c : C' ≃* C := subgroupOfEquivOfLe le_sup_right
  have hB' : IsComponent Y B' := ⟨hBN.isSubnormal,IsQuasisimple.of_mulEquiv b.symm⟩
  have hC' : IsComponent Y C' := ⟨hCN.isSubnormal,IsQuasisimple.of_mulEquiv c.symm⟩
  have hne : B' ≠ C' := by
    intro he
    have hBC : B = C := by
      have hm := congrArg (map Y.subtype) he
      change (B.subgroupOf Y).map Y.subtype = (C.subgroupOf Y).map Y.subtype at hm
      simpa only [map_subgroupOf_eq_of_le (show B ≤ Y from le_sup_left),
        map_subgroupOf_eq_of_le (show C ≤ Y from le_sup_right)] using hm
    have habel : IsMulCommutative B := IsMulCommutative.of_comm (by
      intro x y
      exact Subtype.ext (hc x.property y (hBC ▸ y.property)).symm)
    let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
    let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
    exact Group.IsPerfect.not_isMulCommutative B habel
  obtain ⟨e,_,_⟩ := ComponentQuotients.pair_quotient_equiv
    (Balance.ordinary_isTwoComponent hB') (Balance.ordinary_isTwoComponent hC') hne
  let eb := (QuotientGroup.quotientMulEquivOfEq (ordinary_core_eq_center hB')).trans
    ((centralQuotientEquiv b).trans eB)
  let ec := (QuotientGroup.quotientMulEquivOfEq (ordinary_core_eq_center hC')).trans
    ((centralQuotientEquiv c).trans eC)
  exact no_mathieu_square_section (hX.subgroup Y) (hK.subgroup Y)
    (ChapterA.Section02.IsSectionOf.quotient_subgroup (B' ⊔ C')
      (oddTwoCore (B' ⊔ C' : Subgroup Y))) (e.trans (eb.prodCongr ec))

/-- An ordinary component containing a full Mathieu cover is normal. This
does not identify that cover with the containing component. -/
theorem component_containing_mathieu_normal
    {X : Type*} [Group X] [Finite X] (hX : IsQuasithin X)
    (hK : IsKGroup KnownSimple.IsKnownSimple X)
    (B E : Subgroup X) [IsQuasisimple B]
    (eB : (B ⧸ center B) ≃* Sporadic.Mathieu.M22)
    (hE : IsComponent X E) (hBE : B ≤ E) : E.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro x
  by_contra hne
  let c := (MulAut.conj x).subgroupMap B
  let : IsQuasisimple (B.map (MulAut.conj x).toMonoidHom) := IsQuasisimple.of_mulEquiv c
  have hc := commutator_eq_bot_iff_le_centralizer.mp
    (hE.commutator_eq_bot_of_ne (hE.map_conj x) (Ne.symm hne))
  exact no_commuting_mathieu_covers hX hK B (B.map (MulAut.conj x).toMonoidHom)
    eB ((centralQuotientEquiv c).symm.trans eB)
    ((hBE.trans hc).trans (centralizer_le (map_mono hBE)))

/-- Restrict the original fixed component to an invariant containing group. -/
theorem fixed_component_in_overgroup
    {X : Type*} [Group X] [Finite X]
    (t : X) (B : Subgroup (centralizer ({t} : Set X))) (hB : IsComponent _ B)
    (E : Subgroup X) (hBE : B.map (centralizer ({t} : Set X)).subtype ≤ E)
    (a : MulAut E) (ha : ∀ y : E, (a y : X) = t * (y : X) * t⁻¹) :
    IsComponentIn ((B.map (centralizer ({t} : Set X)).subtype).subgroupOf E)
      a.fixedSubgroup := by
  let C := centralizer ({t} : Set X)
  let U := B.map C.subtype
  let K := U.subgroupOf E
  have hk : K ≤ a.fixedSubgroup := by
    rintro y ⟨b,hb,hby⟩
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    rw [ha]
    have hc := mem_centralizer_singleton_iff.mp b.property
    change (b : X) = (y : X) at hby
    rw [←hby,←hc,mul_inv_cancel_right]
  let f : a.fixedSubgroup →* C :=
    (E.subtype.comp a.fixedSubgroup.subtype).codRestrict C (fun y => by
      apply mem_centralizer_singleton_iff.mpr
      have hy : t * ((y : E) : X) * t⁻¹ = ((y : E) : X) := by
        rw [←ha, (MulAut.mem_fixedSubgroup _ _).mp y.property]
      exact (mul_inv_eq_iff_eq_mul.mp hy).symm)
  have he : K.subgroupOf a.fixedSubgroup = B.comap f := by
    ext y
    change ((y : E) : X) ∈ U ↔ f y ∈ B
    constructor
    · rintro ⟨b,hb,hby⟩
      have : b = f y := Subtype.ext hby
      exact this ▸ hb
    · intro hy
      exact ⟨f y,hy,rfl⟩
  refine ⟨hk,?_,?_⟩
  · rw [he]
    exact hB.1.comap f
  · let := hB.2
    let : IsQuasisimple U := IsQuasisimple.of_mulEquiv
      (B.equivMapOfInjective C.subtype C.subtype_injective)
    let : IsQuasisimple K := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hBE).symm
    exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hk).symm

/-- The literal central quotient retains a Mathieu component in its full fixed group. -/
theorem fixed_mathieu_central_quotient
    {E : Type*} [Group E] [Finite E]
    (a : MulAut E) (B : Subgroup E) (hB : IsComponentIn B a.fixedSubgroup)
    (eB : (B ⧸ center B) ≃* Sporadic.Mathieu.M22) :
    let q := QuotientGroup.mk' (center E)
    IsComponentIn (B.map q) (quotientAut (center E) a).fixedSubgroup ∧
      Nonempty (((B.map q) ⧸ center (B.map q)) ≃* Sporadic.Mathieu.M22) := by
  let := hB.quasisimple
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  let q := QuotientGroup.mk' (center E)
  have hne : B.map q ≠ ⊥ := by
    intro hb
    have hbc : B ≤ center E := by
      have hh := (map_eq_bot_iff B).mp hb
      simpa only [q,QuotientGroup.ker_mk'] using hh
    have hc : IsMulCommutative B := IsMulCommutative.of_comm (fun x y =>
      Subtype.ext (mem_center_iff.mp (hbc x.property) y).symm)
    exact Group.IsPerfect.not_isMulCommutative B hc
  let : Nontrivial (B.map q) := (nontrivial_iff_ne_bot _).mpr hne
  refine ⟨hB.map_fixed_of_central_ker a (quotientAut (center E) a) q
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    (fun x => (quotientAut_apply_mk (center E) a x).symm) hne, ?_⟩
  exact ⟨(IsQuasisimple.centralQuotientEquiv (q.subgroupMap B)
    (q.subgroupMap_surjective B)).symm.trans eB⟩

end CFSG.Quasithin.ChapterI.MathieuPumpup
