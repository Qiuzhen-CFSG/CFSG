module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesWholeForms
public import CFSG.Quasithin.ChapterG.Section11.WholePairNatural
public import Theory.Representation.OrthogonalFourPlusMatrix.SmallDisplacementDegree
public import Theory.Representation.OrthogonalFourPlusMatrix.OuterElementaryRank
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OrthogonalFour.TensorModel

/-!
# Excluding whole component pairs for the original larger actor

The actual G.9 component hypothesis recognizes the action of the normal
component join as a determinant tensor over a common finite field. The
original low-displacement witness forces that field to be GF(4), so the
module has binary degree eight. The larger-actor inequality gives an
actor of order at least sixteen. The determinant-normalizer theorem puts
that very actor inside the component join, where every nonidentity element
has displacement rank at least four, contradicting the original witness.

This discharges the whole two-component branch without the strict D
consumer's extra involution hypotheses. The refined degree alternatives
feed the original component consumer and retain the full dotted G₂(2)
isomorphism. The marked S₈ action and single nonbinary symplectic component
remain source obligations.

Source: Aschbacher–Smith G.9.3(15), G.11.7 and 14.3.14,
printed pp.354,356,368,994 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterG.Section11 ChapterG.Section09 ChapterG.Section09.TwoComponents
namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s
open ClassicalOrthogonal.FourPlusMatrix
attribute [local instance 2000] instAlgebraZModGaloisField

omit s [Finite G] [IsElementaryAbelian 2 (rankTwoSeed T M)] in
private theorem tensor_matrix_coordinates {n : ℕ} {H : Subgroup F.TerminalHdot}
    (hq : Quasiequivalent (F.terminalRepresentation.comp H.subtype) (fourOrthogonal n)) :
    ∃ e : H ≃* PairSL (F := GaloisField 2 n),
      ∃ f : Additive F.Uhat ≃ₗ[ZMod 2] Mat (F := GaloisField 2 n),
      ∀ (l : H) w, f (F.terminalRepresentation l w) = representation (e l) (f w) := by
  obtain ⟨e,f,hf⟩ := hq
  refine ⟨e.trans elementaryEquiv.symm,f.trans (coordinates.restrictScalars (ZMod 2)),?_⟩
  intro l w
  change coordinates (f (F.terminalRepresentation l w)) =
    representation (elementaryEquiv.symm (e l)) (coordinates (f w))
  have hl := hf l w
  change f (F.terminalRepresentation l w) = fourOrthogonal n (e l) (f w) at hl
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
theorem not_whole_component_pair {L H : Subgroup F.TerminalHdot}
    (h9 : ComponentHypothesis KnownSimple.IsKnownSimple F.terminalRepresentation
      (F.terminalDot (F.X g)) L H
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))
    (hne : H ≠ L) : False := by
  let : H.Normal := h9.normal_H
  obtain ⟨L₂,h₂,hH,hne₂,⟨e⟩,hz,hm,td,hk⟩ :=
    WholePair.component_pair_data h9 hne s.even_degree
  obtain ⟨ho,hn,hq⟩ := WholePairNatural.recognition h9 h₂ hH hne₂ e hz td hm hk
  obtain ⟨a,ha,ha2,hpos,hr,_⟩ := s.low_rank_witness.exists_involution s.hypothesis.point_ne_zero
  obtain ⟨b,f,hf⟩ := tensor_matrix_coordinates hq
  have hn2 : td.n = 2 := by
    have hh := LowRankDegree.field_degree_eq_two_of_small_equivariant
      F.terminalRepresentation H b f hf
      (by rw [GaloisField.finrank 2 (by omega : td.n ≠ 0)]; omega) a hpos hr
    rwa [GaloisField.finrank 2 (by omega : td.n ≠ 0)] at hh
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 8 := by
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
  have hE (h : H) (w : Additive F.Uhat) :
      E (F.terminalRepresentation h w) = Binary.action (eH h) (E w) := by
    change RankTwo.OrthogonalFour.tensorCoordinates (f₀ (F.terminalRepresentation h w)) =
      Binary.action (eH h) (RankTwo.OrthogonalFour.tensorCoordinates (f₀ w))
    exact (congrArg RankTwo.OrthogonalFour.tensorCoordinates (hf₀ h w)).trans
      (RankTwo.OrthogonalFour.tensorCoordinates_equivariant (eH h) (f₀ w))
  have hc : 16 ≤ Nat.card (F.terminalDot (F.X g)) := by
    rw [h9.card_actor]
    change 2^4 ≤ 2 ^ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr
    have hh := s.half_degree_le_actor
    omega
  have hXH := elementary_le_marked_determinant_of_card_ge_sixteen
    F.terminalRepresentation s.hypothesis.faithful H eH E hE
    (F.terminalDot (F.X g)) hc
  let aH : H := ⟨a,hXH ha⟩
  have hane : eH aH ≠ 1 := by
    intro he
    have haa : a = 1 := congrArg Subtype.val (eH.injective (he.trans eH.map_one.symm))
    simp only [haa,orderOf_one] at ha2
    omega
  let τ := Binary.action.comp eH.toMonoidHom
  have he (h : H) (w : Additive F.Uhat) :
      E ((F.terminalRepresentation.comp H.subtype) h w) = τ h (E w) := hE h w
  have heq := RankTwo.finrank_movedSpace_transport
    (F.terminalRepresentation.comp H.subtype) τ (MulEquiv.refl H) E he aH
  have hb := Displacement.displacement_rank_four (eH aH) hane
  change 4 ≤ finrank (ZMod 2) (RankTwo.movedSpace τ aH) at hb
  have hb' := hb.trans_eq heq.symm
  change 4 ≤ finrank (ZMod 2) (RankTwo.movedSpace F.terminalRepresentation a) at hb'
  omega

/-- All whole component pairs are excluded for the original larger actor.
Only the exceptional marked S₈ action and a single nonbinary symplectic
component remain beyond the desired numerical alternatives. -/
theorem degree_cases_or_full_four_or_symplectic :
    ((finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
        2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
        Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 4 ∧
        Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) ∧
        FullLinearFour.MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        ∃ L : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot L ∧
          ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L ∧
          ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
            F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
            (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
          (componentOrbit L ⊤ = L ∧ IsSimpleGroup L ∧
            ∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSp L 2 (2^n))) := by
  rcases s.degree_cases_or_full_four_or_symplectic_or_pair with
    good | full | ⟨hd,L,hL,hm,ho,h9,hsingle | hpair⟩
  · exact Or.inl good
  · exact Or.inr (Or.inl full)
  · exact Or.inr (Or.inr ⟨hd,L,hL,hm,ho,h9,hsingle⟩)
  · obtain ⟨L₂,h₂,hne,hjoin,_⟩ := hpair
    have hproper : componentOrbit L ⊤ ≠ L := by
      intro he
      have hle : L₂ ≤ L := by rw [←he,hjoin]; exact le_sup_right
      exact hne (h₂.eq_of_le hL hle)
    exact (s.not_whole_component_pair h9 hproper).elim

/-- Apply the refined numerical alternatives to the actual component consumer.
The successful degree-six branch still identifies the full dotted G₂(2). -/
theorem component_or_full_four_or_symplectic
    (hfour : finrank (ZMod 2) (Additive F.Uhat) = 4 →
      ∀ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D →
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ → SmallComponentImage D)
    (hsix : ∀ K : Subgroup G, ComponentLift F g K →
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 6)) → False) :
    ((∃ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D ∧
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧ Nonempty (D ≃* alternatingGroup (Fin 5))) ∨
      (∃ K : Subgroup G, ComponentLift F g K ∧ (F.terminalDot K).Normal ∧
        Nonempty (F.terminalDot K ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∧
        F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
          pCore 2 (K.subgroupOf F.H))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 4 ∧
        Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) ∧
        FullLinearFour.MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        ∃ L : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot L ∧
          ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L ∧
          ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
            F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
            (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
          (componentOrbit L ⊤ = L ∧ IsSimpleGroup L ∧
            ∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSp L 2 (2^n))) := by
  rcases s.degree_cases_or_full_four_or_symplectic with hd | hr
  · exact Or.inl (source_component_large_actor_of_degree_cases s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card
      (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis hd hfour hsix)
  · exact Or.inr hr

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
