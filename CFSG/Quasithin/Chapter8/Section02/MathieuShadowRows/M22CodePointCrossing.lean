module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodePointCrossing
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePointSection
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointCrossing
/-!
# The selected M22 point closure crosses the original join core

The actual point hexad vector lies in the selected quintet four-space.
Its native pointwise kernel therefore preserves the same quintet cocode
line, putting the original point commutator in the selected hyperplane.
The orders 32 and 16 show that this commutator escapes the selected
intersection, and the retained selected pair forces its relative normal
closure outside the original join core.

The supplied conjugator, whole-code coordinates and full residual map
remain unchanged. Source: Aschbacher--Smith 8.2.12, printed p.722,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode MathieuCode.Hexad
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE MathieuCode.NormalizedShadowRows
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

omit [Finite G] in
private theorem marked_commutator_le_hyperplane
    (V X B : Subgroup G) [IsElementaryAbelian 2 V]
    (hXV : X ≤ normalizer (V : Set G))
    {D : Finset (Fin 22)} (hD : D ∈ m22Blocks)
    (hU : m22HexadVector hD ∈ M22Quintet.V4)
    (e : Additive V ≃ₗ[ZMod 2] M22Code) (q : X →* MathieuCode.m22PairStabilizer)
    (hq : ∀ x, q x ∈ (m22HexadPointwiseKernel D).map m22ToPairStabilizer)
    (he : ∀ x v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hXV x)) v) =
        m22OuterCodeRepresentation (q x) (e v))
    (hB : ∀ v : Additive V, (v.toMul : G) ∈ B ↔ e v ∈ ChiefFlag.quintetHyperplane) :
    ⁅V,X⁆ ≤ B := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro x hx v hv
  have hc : ⁅x,v⁆ ∈ V := V.mul_mem (le_normalizer_iff.mp hXV x hx v hv) (V.inv_mem hv)
  let w : Additive V := Additive.ofMul ⟨v,hv⟩
  have hec : e (Additive.ofMul (⟨⁅x,v⁆,hc⟩ : V)) =
      m22OuterCodeRepresentation (q ⟨x,hx⟩) (e w)-e w := by
    rw [←he,←map_sub]
    apply congrArg e
    apply Additive.toMul.injective
    apply Subtype.ext
    change ⁅x,v⁆ = (x*v*x⁻¹)/v
    simp only [commutatorElement_def,div_eq_mul_inv,mul_assoc]
  apply (hB (Additive.ofMul (⟨⁅x,v⁆,hc⟩ : V))).mpr
  rw [hec]
  apply M22CodePointCrossing.commutator_le_hyperplane hD hU
  exact Coinvariants.sub_mem_ker
    (ρ := m22OuterCodeRepresentation.comp ((m22HexadPointwiseKernel D).map m22ToPairStabilizer).subtype)
    ⟨q ⟨x,hx⟩,hq ⟨x,hx⟩⟩ (e w)

/-- The original point five-space lies in the same selected pair hyperplane;
the original point vector, whole-code marking and residual map are retained. -/
theorem m22_point_selected_hyperplane
    (L V B : Subgroup G) [IsElementaryAbelian 2 V] (z : V)
    (hLN : L ≤ normalizer (V : Set G))
    {D : Finset (Fin 22)} (hD : D ∈ m22Blocks)
    (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (f : Centralizer.localResidual L z →* MulAction.stabilizer M22 D)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hz : e (Additive.ofMul z) = m22HexadVector hD)
    (hzU : e (Additive.ofMul z) ∈ M22Quintet.V4)
    (he : ∀ r v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion
        (((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN) r)) v) =
        m22CodeRepresentation (f r).val (e v))
    (hB : ∀ v : Additive V, (v.toMul : G) ∈ B ↔ e v ∈ ChiefFlag.quintetHyperplane) :
    Centralizer.commutatorSpace L V z ≤ B := by
  let R := Centralizer.localResidual L z
  let X := Centralizer.localTwoCore L z
  let S := MulAction.stabilizer M22 D
  let i := inclusion (Centralizer.localTwoCore_le L z)
  let q := m22ToPairStabilizer.comp (S.subtype.comp (f.comp i))
  have hq (x : X) : q x ∈ (m22HexadPointwiseKernel D).map m22ToPairStabilizer := by
    have hi : i x ∈ pCore 2 R := by
      obtain ⟨r,hr,heq⟩ := x.property
      exact (show r = i x from Subtype.ext heq) ▸ hr
    have hs : f (i x) ∈ pCore 2 S := (f.comap_pCore_of_ker_isPGroup hf hk).ge hi
    have hpoint : (f (i x)).val ∈ m22HexadPointwiseKernel D := by
      rw [←M22CodePointCrossing.inner_hexad_core hD]
      exact mem_map_of_mem S.subtype hs
    exact mem_map_of_mem m22ToPairStabilizer hpoint
  exact marked_commutator_le_hyperplane V X B
    (((Centralizer.localTwoCore_le L z).trans
      ((Centralizer.localResidual_le L z).trans inf_le_left)).trans hLN)
    hD (hz ▸ hzU) e q hq (fun x v => he (i x) v) hB

/-- The same supplied selected pair crosses the actual C_G(z)-closure out
of Q. Its point-hyperplane incidence and noncontainment in U are proved
from the retained code coordinates. -/
theorem selected_m22_point_closure_crossing
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    {H M I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Offenders.Parabolic.Construction.Selected H T M V I 1 i S)
    (hT : HypothesisE322 V T) (L Q : Subgroup G) (z : V)
    (hLN : L ≤ normalizer (V : Set G)) (hVQ : V ≤ Q)
    (hQC : Q ≤ centralizer (V : Set G))
    (hUeq : V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hzU : (z : G) ∈ V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G))
    {D : Finset (Fin 22)} (hD : D ∈ m22Blocks)
    (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (f : Centralizer.localResidual L z →* MulAction.stabilizer M22 D)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hz : e (Additive.ofMul z) = m22HexadVector hD)
    (he : ∀ r v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion
        (((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN) r)) v) =
        m22CodeRepresentation (f r).val (e v))
    (hU : ∀ v : Additive V, (v.toMul : G) ∈ V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) ↔
        e v ∈ M22Quintet.V4)
    (hB : ∀ v : Additive V, (v.toMul : G) ∈ V ⊓ I.pCoreIn 2 ↔
      e v ∈ ChiefFlag.quintetHyperplane) :
    ¬ (Centralizer.sourceClosure L V z).map
      (centralizer ({(z : G)} : Set G)).subtype ≤ Q := by
  let U := V ⊓ centralizer (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  let j : U ≃ M22Quintet.V4 := {
    toFun u := ⟨e (Additive.ofMul (inclusion (show U ≤ V from inf_le_left) u)),
      (hU _).mp u.property⟩
    invFun w := ⟨(e.symm w).toMul,(hU _).mpr (by rw [e.apply_symm_apply]; exact w.property)⟩
    left_inv u := by apply Subtype.ext; exact congrArg (fun v : Additive V => (v.toMul : G)) (e.symm_apply_apply _)
    right_inv w := by apply Subtype.ext; exact e.apply_symm_apply _ }
  have hUc : Nat.card U = 16 := by
    rw [Nat.card_congr j,Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod,M22CodeFourSpace.finrank_four]
    decide
  have hWc := (m22_point_hexad_section L V z hLN hD e f hf hk hz he).1
  have hWB := m22_point_selected_hyperplane L V (V ⊓ I.pCoreIn 2) z hLN hD e f hf hk hz
    ((hU (Additive.ofMul z)).mp hzU) he hB
  apply HermitianSource.selected_point_closure_crossing s hT L Q z hLN hVQ hQC hUeq hzU hWB
  intro hn
  have hc := Nat.card_le_card_of_injective (inclusion hn) (inclusion_injective hn)
  change Nat.card (Centralizer.commutatorSpace L V z) ≤ Nat.card U at hc
  rw [hWc,hUc] at hc
  omega

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
