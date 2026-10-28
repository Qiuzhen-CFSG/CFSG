module
public import CFSG.Quasithin.ChapterG.Section11.WholePairNatural
public import Theory.Representation.OrthogonalFourPlusMatrix.LowRankDegree
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OrthogonalFour
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric
public import CFSG.Quasithin.ChapterG.Section11.LowRank

/-!
# Excluding the whole tensor pair from the strict source

The genuine two-dimensional factor recognition constructs the natural
orthogonal action on the original normal component join. Binary rank two
forces its common field to be F4. New natural coordinates over the concrete
F4 used by the orthogonal-four calculation then yield a conjugate product
of order five, contradicting the original type-a2 product bound.

`StrictWholeExclusion` applies this to the literal original strict quotient.
No whole-action catalogue or normalizer-classification premise is assumed.
Source: Aschbacher--Smith G.11.7 and 6.2.19, printed pp.368,691.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11.WholePairExclusion
open Section09 Section09.TwoComponents ClassicalOrthogonal.FourPlusMatrix
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X L H : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem matrix_coordinates {n : ℕ}
    (hq : Quasiequivalent (ρ.comp H.subtype) (fourOrthogonal n)) :
    ∃ e : H ≃* PairSL (F := GaloisField 2 n),
      ∃ f : V ≃ₗ[ZMod 2] Mat (F := GaloisField 2 n),
      ∀ (l : H) w, f (ρ l w)=representation (e l) (f w) := by
  obtain ⟨e,f,hf⟩ := hq
  refine ⟨e.trans elementaryEquiv.symm,f.trans (coordinates.restrictScalars (ZMod 2)),?_⟩
  intro l w
  change coordinates (f (ρ l w))=representation (elementaryEquiv.symm (e l)) (coordinates (f w))
  have hl := hf l w
  change f (ρ l w)=fourOrthogonal n (e l) (f w) at hl
  rw [hl]
  change coordinates ((e l).val.val (f w))=_
  generalize hb : e l=b
  obtain ⟨g,rfl⟩ := elementaryEquiv.surjective b
  rw [MulEquiv.symm_apply_apply]
  exact toOrthogonal_coordinates g (f w)

/-- The original type-a2 rank-two involution excludes every whole tensor pair. -/
theorem false_of_component_pair
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : ComponentHypothesis KnownSimple.IsKnownSimple ρ X L H
      (finrank (ZMod 2) (Additive X))) (hne : H≠L)
    (a : G) (ha : a^2=1) (hr : finrank (ZMod 2) (RankTwo.movedSpace ρ a)=2)
    (htype : ∀ u, B u (ρ a u)=0) : False := by
  let := h9.normal_H
  obtain ⟨L₂,h₂,hH,hne₂,⟨e⟩,hz,hm,T,hk⟩ := WholePair.component_pair_data h9 hne
    (AlternatingForm.even_finrank B h.alternating h.nondegenerate)
  obtain ⟨ho,hn,hq⟩ := WholePairNatural.recognition h9 h₂ hH hne₂ e hz T hm hk
  obtain ⟨b,f,hf⟩ := matrix_coordinates hq
  have hn2 : T.n=2 := by
    have hh := LowRankDegree.field_degree_eq_two_of_equivariant ρ H b f hf
      (by rw [GaloisField.finrank 2 (by omega : T.n≠0)];omega) a hr
    rwa [GaloisField.finrank 2 (by omega : T.n≠0)] at hh
  have hF : Nat.card Binary.F=2^T.n := by
    rw [hn2,Nat.card_eq_fintype_card,SL2FourNatural.card_field]
    norm_num
  let : Finite T.F := Module.finite_iff_finite.mp T.finiteField
  let : Fintype T.F := Fintype.ofFinite T.F
  let c : T.F ≃ₐ[ZMod 2] Binary.F := FiniteField.algEquivOfCardEq 2
    (by simpa only [Nat.card_eq_fintype_card] using T.field_card.trans hF.symm)
  have hoF : Nat.card L=Nat.card SL(2,Binary.F) := by
    rw [ho,BenderSuzuki.External.huppert614_card_specialLinearGroup,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,
      GaloisField.card 2 T.n (by omega),hF]
  let : IsQuasisimple L := h9.component.2
  let : IsQuasisimple L₂ := h₂.2
  obtain ⟨b',f',hf'⟩ := NaturalRecognition.tensor_natural_of_order T
    (h9.component.commutator_eq_bot_of_ne h₂ hne₂)
    (component_pair_disjoint_of_center_eq_bot h9.component h₂ hne₂ hz) hH
    c hk hoF ((Nat.card_congr e.toEquiv).symm.trans hoF)
  have hp := RankTwo.Symmetric.smallConjugateProducts_of_type_a2
    B ρ h.alternating h.nondegenerate h.faithful h.preserves a ha hr htype
  exact RankTwo.OrthogonalFour.exclusion_of_tensor_model ρ H b' f' hf' a ha hr hp
end CFSG.Quasithin.ChapterG.Section11.WholePairExclusion
