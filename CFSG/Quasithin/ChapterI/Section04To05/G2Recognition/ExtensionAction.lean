module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CoreCentralizer
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.ElementaryStabilizerSign
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.FactorCoordinates
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.WreathOuter
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The actual outer quotient of the involution centralizer

Conjugation on Q₁Q₂ induces an action on its central quotient. The normal
SL₂(3) factors prohibit factor interchange. An aligned elementary eight
inside Q₁Q₂ forces equal signs on the two quaternion-axis permutations
for a Sylow two-subgroup; the two-residual also has trivial sign. Thus the
whole image lies in the equal-sign subgroup of S₃ × S₃.

Self-centralization makes the kernel exactly Q₁Q₂. Its index eighteen
then proves equality with the concrete equal-sign subgroup. The resulting
quotient equivalence retains its literal conjugation formula. This does
not determine the central extension or establish ambient recognition.
The Chapter14Extension application uses the original source-local data.

Source: Aschbacher–Smith I.4(G1)–(G2), printed p.417; the normal-factor
extension analysis in Fong–Wong §2F, Nagoya Math. J.36 (1969), pp.153–154.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] G2ThreeConfiguration.H₁_normal G2ThreeConfiguration.H₂_normal

noncomputable def coreOuterAction : c.H →* BinaryFourPlus.Wreath :=
  (quaternionCoreData c).quotientWreathAction.comp MulAut.conjNormal

theorem coreOuterAction_preserves_factors (h : c.H) : (coreOuterAction c h).right = 1 := by
  apply ((quaternionCoreData c).quotientWreathAction_right_eq_one_iff _).mpr
  change ((c.H₁.pCoreIn 2).subgroupOf (quaternionCore c)).map
    (MulAut.conjNormal h).toMonoidHom = _
  let : (c.H₁.pCoreIn 2).Normal := ConjAct.normal_of_characteristic_of_normal
  apply eq_of_le_of_card_ge
  · rintro x ⟨y,hy,rfl⟩
    exact (inferInstance : (c.H₁.pCoreIn 2).Normal).conj_mem y hy h
  · exact le_of_eq (Nat.card_congr
      ((MulAut.conjNormal h : MulAut (quaternionCore c)).subgroupMap
        ((c.H₁.pCoreIn 2).subgroupOf (quaternionCore c))).toEquiv)

theorem coreOuterAction_sign (h : c.H) : BinaryFourPlus.factorSign (coreOuterAction c h) = 1 := by
  let T : Sylow 2 c.H := Classical.choice inferInstance
  obtain ⟨E,_,he,hc,hEQ,hnorm,_,_,_,_⟩ := exists_seed_in_quaternionCore c T
  let D := E.subgroupOf (quaternionCore c)
  let e : D ≃* E := subgroupOfEquivOfLe hEQ
  let _ := he
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  have hD : Nat.card D = 8 := (Nat.card_congr e.toEquiv).trans hc
  let s := BinaryFourPlus.factorSign.comp (coreOuterAction c)
  have hT : (T : Subgroup c.H) ≤ s.ker := by
    intro t ht
    exact (quaternionCoreData c).quotientWreathAction_factorSign_one_of_elementary_eight
      D hD (MulAut.conjNormal t) (fun x hx => (mem_normalizer_iff.mp (hnorm ht) x).mp hx)
  have hp : IsPGroup 2 (Units ℤ) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_eq_fintype_card]; decide)
  have hR : pResidual 2 c.H ≤ s.ker :=
    sInf_le ⟨inferInstance,(hp.to_subgroup s.range).of_equiv
      (QuotientGroup.quotientKerEquivRange s).symm⟩
  have ht : (⊤ : Subgroup c.H) ≤ s.ker := by
    rw [← pResidual_sup_sylow_eq_top T]
    exact sup_le hR hT
  exact ht (mem_top h)

/-- The outer action has exactly the original quaternion subgroup as kernel. -/
theorem coreOuterAction_kernel : (coreOuterAction c).ker = quaternionCore c := by
  let Q := quaternionCore c
  let d := quaternionCoreData c
  let a : c.H →* MulAut Q := MulAut.conjNormal
  apply le_antisymm
  · intro h hh
    have hinner : a h ∈ MulAut.innerSubgroup Q := by
      rw [← d.quotientWreathAction_ker]
      exact hh
    obtain ⟨q,hq⟩ := hinner
    have ha : a (q : c.H) = MulAut.conj q := by ext x; rfl
    have hk : a ((q : c.H)⁻¹*h)=1 := by rw [map_mul,map_inv,ha,hq,inv_mul_cancel]
    have hz : (q : c.H)⁻¹*h ∈ centralizer (Q : Set c.H) := by
      intro x hx
      have he := congrArg (fun b : MulAut Q => (b ⟨x,hx⟩ : c.H)) hk
      change ((q : c.H)⁻¹*h)*x*((q : c.H)⁻¹*h)⁻¹=x at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hm := Q.mul_mem q.property (core_self_centralizing c hz)
    simpa only [mul_inv_cancel_left] using hm
  · intro h hh
    change a h ∈ d.quotientWreathAction.ker
    rw [d.quotientWreathAction_ker]
    exact ⟨⟨h,hh⟩,by ext x; rfl⟩

/-- The concrete equal-sign, factor-preserving subgroup of S₃ wr C₂. -/
def diagonalSign : Subgroup BinaryFourPlus.Wreath :=
  (RegularWreathProduct.rightHom : BinaryFourPlus.Wreath →* BinaryFourPlus.C2).ker ⊓
    BinaryFourPlus.factorSign.ker

theorem diagonalSign_card : Nat.card diagonalSign = 18 := by
  let : DecidableEq BinaryFourPlus.Wreath :=
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) BinaryFourPlus.C2).injective.decidableEq
  let : Fintype BinaryFourPlus.Wreath := Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) BinaryFourPlus.C2).symm
  change Nat.card {w : BinaryFourPlus.Wreath // w.right = 1 ∧ BinaryFourPlus.factorSign w = 1} = 18
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The literal outer action fills the equal-sign subgroup. -/
theorem coreOuterAction_range : (coreOuterAction c).range = diagonalSign := by
  apply eq_of_le_of_card_ge
  · rintro x ⟨h,rfl⟩
    exact ⟨coreOuterAction_preserves_factors c h,coreOuterAction_sign c h⟩
  · rw [← index_ker,coreOuterAction_kernel c,quaternionCore_index c,diagonalSign_card]

noncomputable def coreQuotientEquiv : (c.H ⧸ quaternionCore c) ≃* diagonalSign :=
  (QuotientGroup.quotientMulEquivOfEq (coreOuterAction_kernel c).symm).trans
    ((QuotientGroup.quotientKerEquivRange (coreOuterAction c)).trans
      (MulEquiv.subgroupCongr (coreOuterAction_range c)))

theorem coreQuotientEquiv_mk (h : c.H) :
    (coreQuotientEquiv c (QuotientGroup.mk' (quaternionCore c) h) : BinaryFourPlus.Wreath) =
      (quaternionCoreData c).quotientWreathAction (MulAut.conjNormal h) := rfl

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
