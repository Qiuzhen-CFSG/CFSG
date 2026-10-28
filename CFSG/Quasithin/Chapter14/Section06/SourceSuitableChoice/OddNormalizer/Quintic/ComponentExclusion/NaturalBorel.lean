module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExclusion.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BlockRigidity.NaturalLayer
public import Theory.GroupAction.OddIndexInvolutionLayers

/-!
# The terminal natural-block contradiction in original 14.6.15

The marked natural module identifies the actual two-core quotient and
the image of B under its projection. Its Borel has odd index, and the
natural module has no Borel-fixed vectors. Odd-index averaging through
the two central layers above the module shows that every involution in
Z(B) centralizes J. The original Z is such a subgroup, so J lies in
Mc = C_G(Z), contradicting the extracted component's escape.

The marked model is an explicit remaining classification premise. This
module proves its terminal consequence; it does not assert that C.2.7
has already supplied the model.

Source: Aschbacher--Smith, 14.6.15, printed p.1035.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BlockRigidity
variable {G : Type*} [Group G] [Finite G]

/-- A genuine natural module and the literal core-quotient image of B.
There is no centralizer or terminal contradiction field. -/
structure NaturalBorelModel (J B : Subgroup G) where
  field : ChapterB.QuasisimpleSource.BinaryField
  large : 2 < Nat.card field.Carrier
  action : SL(2,field.Carrier) →* MulAut (Multiplicative (Fin 2 → field.Carrier))
  model : ChapterC.BlockModuleModel J action
  natural : ∀ (g : SL(2,field.Carrier)) (v : Multiplicative (Fin 2 → field.Carrier)),
    Multiplicative.toAdd (action g v) = g.val *ᵥ Multiplicative.toAdd v
  core_le : pCore 2 J ≤ B.subgroupOf J
  borel : (B.subgroupOf J).map
    (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))) =
      Matrix.SpecialLinearGroup.rankOneBorel field.Carrier

private theorem involution_centralizes_of_model {J B : Subgroup G}
    (hf : generalizedFitting J = pCore 2 J) (b : NaturalBorelModel J B)
    (z : G) (hz2 : z ^ 2 = 1) (hzJ : z ∈ J)
    (hzB : z ∈ centralizer (B : Set G)) : z ∈ centralizer (J : Set G) := by
  let Q := J.pCoreIn 2
  let U := (ChapterC.blockU J).map J.subtype
  have hJQ : J ≤ normalizer (Q : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hself : J ⊓ centralizer (Q : Set G) ≤ Q := by
    intro x hx
    have hc : (⟨x,hx.1⟩ : J) ∈ centralizer (pCore 2 J : Set J) := by
      intro y hy
      exact Subtype.ext (hx.2 y (mem_map_of_mem J.subtype hy))
    rw [←hf] at hc
    exact mem_map_of_mem J.subtype (hf ▸ centralizer_generalizedFitting_le J hc)
  have hQU : ⁅J,Q⁆ ≤ U := by
    have ht : (⊤ : Subgroup J).map J.subtype = J := by
      rw [←MonoidHom.range_eq_map,range_subtype]
    have he : ⁅J,Q⁆ = (⁅(⊤ : Subgroup J),pCore 2 J⁆).map J.subtype := by
      rw [map_commutator,ht]
      rfl
    rw [he,commutator_comm]
    exact le_rfl
  have hfixed : U ⊓ centralizer ((B.subgroupOf J).map J.subtype : Set G) ≤
      centralizer (J : Set G) := by
    rintro x ⟨⟨u,hu,rfl⟩,hx⟩ y hy
    have hc : u ∈ center J := borel_centralizer_blockU_le_center b.action b.model
      b.natural (B.subgroupOf J) b.borel b.large ⟨hu,?_⟩
    · exact congrArg Subtype.val (mem_center_iff.mp hc ⟨y,hy⟩)
    · intro v hv
      exact Subtype.ext (hx v (mem_map_of_mem J.subtype hv))
  have hQB : Q ≤ B := by
    rintro x ⟨y,hy,rfl⟩
    exact b.core_le hy
  exact OddIndexInvolutionLayers.involution_fixed_of_layers J Q U hJQ hself hQU
    (B.subgroupOf J) (borel_odd_index b.action b.model _ b.core_le b.borel) hfixed
    z hz2 (J.le_normalizer hzJ) (centralizer_le hQB hzB)
    (centralizer_le (by rw [subgroupOf_map_subtype]; exact inf_le_left) hzB)

variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)

local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : EscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))

/-- The source involution subgroup lies in the center of J, using the
literal Borel image and natural action rather than an assumed center equality. -/
theorem point_le_component_center (h : d.K1 ≤ j.J)
    (b : NaturalBorelModel j.J (borelIntersection s d j)) :
    centralInvolutions T ≤ (center j.J).map j.J.subtype := by
  have hZJ : centralInvolutions T ≤ j.J := by
    have hh := point_le_intersection s d j h
    rw [contained_intersection s d j h] at hh
    exact hh.trans inf_le_left
  have hBZ : borelIntersection s d j ≤ centralizer (centralInvolutions T : Set G) :=
    (inf_le_right.trans inf_le_left).trans_eq (partner_eq_centralizer s)
  intro z hz
  have hc := involution_centralizes_of_model j.characteristic_component b z
    (elemPow_eq_one_of_isElementaryAbelian z (a.kernel_le hz)) (hZJ hz)
    (le_centralizer_iff.mp hBZ hz)
  refine ⟨⟨z,hZJ hz⟩,mem_center_iff.mpr ?_,rfl⟩
  intro x
  exact Subtype.ext (hc x x.property)

/-- The final centralizer contradiction, conditional only on the model
comparison and the preceding containment branch. -/
theorem false_of_natural_borel (h : d.K1 ≤ j.J)
    (b : NaturalBorelModel j.J (borelIntersection s d j)) : False := by
  apply j.outside
  apply le_inf _ j.component_le
  apply le_trans _ (partner_eq_centralizer s).ge
  apply le_centralizer_iff.mpr
  intro z hz x hx
  obtain ⟨z',hz',rfl⟩ := point_le_component_center s d j h b hz
  exact congrArg Subtype.val (mem_center_iff.mp hz' ⟨x,hx⟩)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion
