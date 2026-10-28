module
public import CFSG.Quasithin.ChapterI.Section03.InvolutionSource
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section02.Statements.UnitaryExceptionFiveFree
public import Theory.Mathieu.M22.UniversalMultiplier.Basic
public import Theory.Mathieu.PositiveLocalCubicRank
public import Theory.Quasithin.ProductLocalRank
public import Theory.GroupTheory.GeneralizedFitting.LayerImages

/-!
# The single two-component containing a local M₂₂ cover

The product M₂₂ × M₂₂ has two-local cubic rank at least three. Theorem A
excludes it as a section of a quasithin K-group: its ordinary alternative
bounds that rank by two, and the unitary exception has no factor five.
The literal O_{2',2} quotient of two distinct Mathieu two-components is
this product. Thus every such two-component is normal, ruling out the
exchanged pair in I.3.2 and leaving one involution-invariant two-component
containing the whole original local cover.

This does not identify the seed with its containing component. Proper
containing components must still be excluded in the p.612 application.
The actual consumer is the original exterior cubic in Hall.OddNormalizer.
Source: Aschbacher--Smith I.3.2, p.415; A.2.1, p.33; 4.2.13, p.612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterI.MathieuPumpup
open ChapterA.Section02
open Sporadic.Mathieu

private theorem product_semisimple {X Y : Type*} [Group X] [Group Y]
    [IsQuasisimple X] [IsQuasisimple Y] : componentLayer (X × Y) = ⊤ := by
  let B := (MonoidHom.snd X Y).ker
  let C := (MonoidHom.fst X Y).ker
  let eB : X ≃* B := {
    toFun := fun x => ⟨(x,1),rfl⟩
    invFun := fun x => x.val.1
    left_inv := fun _ => rfl
    right_inv := fun x => Subtype.ext (Prod.ext rfl x.property.symm)
    map_mul' := fun _ _ => Subtype.ext (Prod.ext rfl (one_mul _).symm) }
  let eC : Y ≃* C := {
    toFun := fun x => ⟨(1,x),rfl⟩
    invFun := fun x => x.val.2
    left_inv := fun _ => rfl
    right_inv := fun x => Subtype.ext (Prod.ext x.property.symm rfl)
    map_mul' := fun _ _ => Subtype.ext (Prod.ext (one_mul _).symm rfl) }
  have hB : IsComponent (X × Y) B :=
    ⟨(inferInstance : B.Normal).isSubnormal,IsQuasisimple.of_mulEquiv eB⟩
  have hC : IsComponent (X × Y) C :=
    ⟨(inferInstance : C.Normal).isSubnormal,IsQuasisimple.of_mulEquiv eC⟩
  apply top_unique
  intro x _
  have hb := (show B ≤ componentLayer (X × Y) from le_sSup hB) (show (x.1,1) ∈ B from rfl)
  have hc := (show C ≤ componentLayer (X × Y) from le_sSup hC) (show (1,x.2) ∈ C from rfl)
  simpa only [Prod.mk_mul_mk,mul_one,one_mul] using (componentLayer (X × Y)).mul_mem hb hc

private theorem mathieu_square_local_rank :
    3 ≤ twoLocalPrimeRank 3 (M22 × M22) := by
  have hex : ∃ U : Subgroup M22, IsTwoLocal U := by
    by_contra! hh
    have hz := twoLocalPrimeRank_eq_zero_of_no_twoLocal 3 hh
    have hp := m22_one_le_twoLocalPrimeRank_three
    omega
  have hh := Theory.Quasithin.ProductLocalRank.local_add_ordinary_le (B := M22) 3 hex
  rw [m22_primeRank_three] at hh
  have hp := m22_one_le_twoLocalPrimeRank_three
  omega

universe u
/-- The literal product of two M₂₂ groups is not a section of a quasithin K-group. -/
theorem no_mathieu_square_section {X S : Type u} [Group X] [Finite X]
    [Group S] [Finite S] (hX : IsQuasithin X)
    (hK : IsKGroup KnownSimple.IsKnownSimple X) (hS : IsSectionOf S X)
    (e : S ≃* M22 × M22) : False := by
  have hsemi : IsSemisimple S :=
    componentLayer_eq_top_of_surjective e.symm.toMonoidHom e.symm.surjective
      product_semisimple
  have hc := (ChapterA.Section02.theoremA_knownSimple hX hK S hS hsemi
    3 (by decide) (by decide)).1
  rcases hc with ⟨hr,hG⟩ | he
  · have hrS : 3 ≤ twoLocalPrimeRank 3 S :=
      mathieu_square_local_rank.trans (twoLocalPrimeRank_le_of_injective
        3 e.symm.toMonoidHom e.symm.injective)
    omega
  · apply he.five_free
    rw [Nat.card_congr e.toEquiv,Nat.card_prod,m22_order]
    decide

/-- Two two-components with the indicated intrinsic Mathieu quotients coincide. -/
theorem mathieu_twoComponent_pair_eq {X : Type u} [Group X] [Finite X]
    (hX : IsQuasithin X) (hK : IsKGroup KnownSimple.IsKnownSimple X)
    {B C : Subgroup X} (hB : B.IsTwoComponent) (hC : C.IsTwoComponent)
    (eB : (B ⧸ oddTwoCore B) ≃* M22) (eC : (C ⧸ oddTwoCore C) ≃* M22) : B = C := by
  by_contra hne
  obtain ⟨e,_,_⟩ := ChapterI.ComponentQuotients.pair_quotient_equiv hB hC hne
  exact no_mathieu_square_section hX hK
    (IsSectionOf.quotient_subgroup (B ⊔ C) (oddTwoCore (B ⊔ C : Subgroup X)))
    (e.trans (eB.prodCongr eC))

/-- A Mathieu two-component is normal in a quasithin K-group: a distinct
conjugate would supply the excluded literal Mathieu-square section. -/
theorem mathieu_twoComponent_normal {X : Type u} [Group X] [Finite X]
    (hX : IsQuasithin X) (hK : IsKGroup KnownSimple.IsKnownSimple X)
    {B : Subgroup X} (hB : B.IsTwoComponent)
    (eB : (B ⧸ oddTwoCore B) ≃* Sporadic.Mathieu.M22) : B.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro x
  let e := (MulAut.conj x).subgroupMap B
  let eq := QuotientGroup.congr _ _ e (oddTwoCore_map_equiv e)
  exact (mathieu_twoComponent_pair_eq hX hK hB
    (hB.map_equiv (MulAut.conj x)) eB (eq.symm.trans eB)).symm

/-- I.3.2 has a single invariant two-component over the original Mathieu cover. -/
theorem mathieu_involution_pumpup {X : Type u} [Group X] [Finite X]
    (hX : IsQuasithin X) (hK : IsKGroup KnownSimple.IsKnownSimple X)
    (t : X) (ht : orderOf t = 2)
    (B : Subgroup (centralizer ({t} : Set X))) (hB : IsComponent _ B)
    (eB : (B ⧸ center B) ≃* M22) :
    let D := B.map (centralizer ({t} : Set X)).subtype
    let J := componentOrbit D (oddELayer X)
    D ≤ J ∧ J.IsTwoComponent ∧ J.map (MulAut.conj t).toMonoidHom = J := by
  have hb := ChapterI.Balance.ordinary_isTwoComponent hB
  have hcore : oddTwoCore B = center B := by
    let : Group.IsSolvable (pPrimeCore 2 B) := odd_order_theorem _
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    rw [hb.oddTwoCore_eq_solvableRadical]
    let := hB.2
    exact le_antisymm IsQuasisimple.solvableRadical_le_center
      (le_solvableRadical _ inferInstance
        (Group.isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm))
  refine ⟨le_componentOrbit _ _,?_⟩
  rcases ChapterI.lemma_I_3_2 t ht B hb with hJ | ⟨J,hJ,hne,_,⟨e⟩⟩
  · exact hJ
  · let eq := e.trans ((QuotientGroup.quotientMulEquivOfEq hcore).trans eB)
    exact (hne ((normal_iff_map_conj_eq.mp
      (mathieu_twoComponent_normal hX hK hJ eq) t).symm)).elim
end CFSG.Quasithin.ChapterI.MathieuPumpup

