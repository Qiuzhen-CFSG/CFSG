module
public import CFSG.Quasithin.ChapterG.Section11.WholePairNatural
public import CFSG.Quasithin.ChapterG.Section11.LowRank
public import Theory.Representation.OrthogonalFourPlusMatrix.SmallDisplacementDegree
public import Theory.Representation.OrthogonalFourPlusMatrix.OuterElementaryRank
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OrthogonalFour.TensorModel

/-!
# Whole tensor pairs with an actor of at least half the degree

The G.9 tensor recognition and a nonzero displacement of rank at most two
force the common field to have order four. An elementary actor of order at
least sixteen is then inside the component join, where every nonidentity
element has displacement rank at least four. This excludes the pair on the
original G.10 inputs, without any strict-intersection involution premise.

Adapted from the original larger-actor argument in Chapter14, with its
rank-two flag removed. The HS source applies it to its rank-three flag.
Source: Aschbacher--Smith G.9.3(15), G.11.7, 14.3.24, pp.354,368,1000.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section11.LargeWhole
open Section09 Section09.TwoComponents
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
    {v : V} {W : Submodule (ZMod 2) V} {X L H : Subgroup G}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
open ClassicalOrthogonal.FourPlusMatrix
attribute [local instance 2000] instAlgebraZModGaloisField

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem tensor_matrix_coordinates {n : ℕ} {H : Subgroup G}
    (hq : Quasiequivalent (ρ.comp H.subtype) (fourOrthogonal n)) :
    ∃ e : H ≃* PairSL (F := GaloisField 2 n),
      ∃ f : V ≃ₗ[ZMod 2] Mat (F := GaloisField 2 n),
      ∀ (l : H) w, f (ρ l w) = representation (e l) (f w) := by
  obtain ⟨e,f,hf⟩ := hq
  refine ⟨e.trans elementaryEquiv.symm,f.trans (coordinates.restrictScalars (ZMod 2)),?_⟩
  intro l w
  change coordinates (f (ρ l w)) =
    representation (elementaryEquiv.symm (e l)) (coordinates (f w))
  have hl := hf l w
  change f (ρ l w) = fourOrthogonal n (e l) (f w) at hl
  rw [hl]
  change coordinates ((e l).val.val (f w)) = _
  generalize hb : e l = b
  obtain ⟨g,rfl⟩ := elementaryEquiv.surjective b
  rw [MulEquiv.symm_apply_apply]
  exact toOrthogonal_coordinates g (f w)

set_option backward.isDefEq.respectTransparency false in
/-- A whole component pair contradicts the original larger actor. The
low-rank witness forces GF(4), and the large elementary actor is then inner,
where every nonidentity displacement has binary rank at least four. -/
theorem not_component_pair
    (h : Section10.Hypothesis ρ B v W X X₀)
    (hw : LowRankWitness ρ v X)
    (hlarge : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (Additive X))
    (h9 : ComponentHypothesis KnownSimple.IsKnownSimple ρ
      X L H
      (finrank (ZMod 2) (Additive X)))
    (hne : H ≠ L) : False := by
  let : H.Normal := h9.normal_H
  obtain ⟨L₂,h₂,hH,hne₂,⟨e⟩,hz,hm,td,hk⟩ :=
    WholePair.component_pair_data h9 hne (AlternatingForm.even_finrank B h.alternating h.nondegenerate)
  obtain ⟨ho,hn,hq⟩ := WholePairNatural.recognition h9 h₂ hH hne₂ e hz td hm hk
  obtain ⟨a,ha,ha2,hpos,hr,_⟩ := hw.exists_involution h.point_ne_zero
  obtain ⟨b,f,hf⟩ := tensor_matrix_coordinates hq
  have hn2 : td.n = 2 := by
    have hh := LowRankDegree.field_degree_eq_two_of_small_equivariant
      ρ H b f hf
      (by rw [GaloisField.finrank 2 (by omega : td.n ≠ 0)]; omega) a hpos hr
    rwa [GaloisField.finrank 2 (by omega : td.n ≠ 0)] at hh
  have hd : finrank (ZMod 2) V = 8 := by
    rw [td.degree_eq,hk,hn2]
    norm_num
  have hF : Nat.card Binary.F = 2^td.n := by
    rw [hn2,Nat.card_eq_fintype_card,Representation.SL2FourNatural.card_field]
    norm_num
  let : Finite td.F := Module.finite_iff_finite.mp td.finiteField
  let : Fintype td.F := Fintype.ofFinite td.F
  let c : td.F ≃ₐ[ZMod 2] Binary.F := FiniteField.algEquivOfCardEq 2
    (by simpa only [Nat.card_eq_fintype_card] using td.field_card.trans hF.symm)
  have hoF : Nat.card L = Nat.card SL(2,Binary.F) := by
    rw [ho,BenderSuzuki.External.huppert614_card_specialLinearGroup,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,
      GaloisField.card 2 td.n (by omega),hF]
  let : IsQuasisimple L := h9.component.2
  let : IsQuasisimple L₂ := h₂.2
  obtain ⟨eH,f₀,hf₀⟩ := NaturalRecognition.tensor_natural_of_order td
    (h9.component.commutator_eq_bot_of_ne h₂ hne₂)
    (component_pair_disjoint_of_center_eq_bot h9.component h₂ hne₂ hz) hH
    c hk hoF ((Nat.card_congr e.toEquiv).symm.trans hoF)
  let E := f₀.trans (RankTwo.OrthogonalFour.tensorCoordinates.restrictScalars (ZMod 2))
  have hE (h : H) (w : V) :
      E (ρ h w) = Binary.action (eH h) (E w) := by
    change RankTwo.OrthogonalFour.tensorCoordinates (f₀ (ρ h w)) =
      Binary.action (eH h) (RankTwo.OrthogonalFour.tensorCoordinates (f₀ w))
    exact (congrArg RankTwo.OrthogonalFour.tensorCoordinates (hf₀ h w)).trans
      (RankTwo.OrthogonalFour.tensorCoordinates_equivariant (eH h) (f₀ w))
  have hc : 16 ≤ Nat.card X := by
    rw [h9.card_actor]
    change 2^4 ≤ 2 ^ finrank (ZMod 2) (Additive X)
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr
    have hh := hlarge
    omega
  have hXH := elementary_le_marked_determinant_of_card_ge_sixteen
    ρ h.faithful H eH E hE
    X hc
  let aH : H := ⟨a,hXH ha⟩
  have hane : eH aH ≠ 1 := by
    intro he
    have haa : a = 1 := congrArg Subtype.val (eH.injective (he.trans eH.map_one.symm))
    simp only [haa,orderOf_one] at ha2
    omega
  let τ := Binary.action.comp eH.toMonoidHom
  have he (h : H) (w : V) :
      E ((ρ.comp H.subtype) h w) = τ h (E w) := hE h w
  have heq := RankTwo.finrank_movedSpace_transport
    (ρ.comp H.subtype) τ (MulEquiv.refl H) E he aH
  have hb := Displacement.displacement_rank_four (eH aH) hane
  change 4 ≤ finrank (ZMod 2) (RankTwo.movedSpace τ aH) at hb
  have hb' := hb.trans_eq heq.symm
  change 4 ≤ finrank (ZMod 2) (RankTwo.movedSpace ρ a) at hb'
  omega

end CFSG.Quasithin.ChapterG.Section11.LargeWhole
