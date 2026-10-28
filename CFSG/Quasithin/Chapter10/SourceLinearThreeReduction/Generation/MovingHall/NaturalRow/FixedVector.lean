module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.Inputs
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.BinaryConjugationSection.FixedGeneration
public import Theory.Representation.CentralCoverFixedGeneration
public import Theory.Representation.SL2OrthogonalCover.FullFixed.Quotients

/-!
# A noncentral fixed vector in the original natural cover

The original component quotient acts on the fully moved subgroup [V,L],
since its two-core centralizes V. Its given natural section is a central
cover. A two-group normalizing the original component and V has a nonzero
fixed quotient vector; the general-field orthogonal-cover theorem lifts it
to an actual fixed vector with nonzero coordinates. The central kernel is
retained, and no splitting or field-four assumption is used.

This adapts the natural-cover argument of `SourceA5PointFixedSpan` to the
specified even-field marking. The original half-Sylow application in
`NaturalTerminal.SeedCentralizer` detects every odd-order orbit element.
Source: Aschbacher–Smith I.2.3, 10.1.2(5), and 10.2.3, pp.742,745–746.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

set_option backward.isDefEq.respectTransparency false in
theorem source_natural_moved_noncentral_fixed_vector
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (P : Subgroup G) (hPM : P ≤ D.maximalLocal) (hPL : P ≤ normalizer (L : Set G))
    (hP : IsPGroup 2 P) :
    ∃ w : (⁅D.fullModule,L⁆ : Subgroup G),
      (w:G) ∈ centralizer (P : Set G) ∧ c.coordinates w ≠ 1 := by
  let W := ⁅D.fullModule,L⁆
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  obtain ⟨σ,hσ⟩ := BinaryConjugationSection.exists_action_of_central_kernel
    L W (normalizer_commutator_ge_right _ _) q hq (by
      intro l hl
      have hp : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
        (e.injective (hl.trans e.map_one.symm))
      exact centralizer_le hWV (source_component_core_centralizes_fullModule D
        (mem_map_of_mem L.subtype hp)))
  have hPW : P ≤ normalizer (W : Set G) := by
    intro p hp
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule (hPM hp)),
      mem_normalizer_iff_map_conj_eq.mp (hPL hp)]
  have hPZ : P ≤ normalizer (sourceMovedFixed D : Set G) :=
    (le_inf hPL hPW).trans (source_original_moved_fixed_normalizer D)
  obtain ⟨π,hπ,hπc⟩ := c.exists_cover_of_fully_moved SL2.BinarySmall.natural q hq σ hσ
    inf_le_right (source_full_moved_eq_commutator D)
  let τ := BinaryConjugationSection.originalNormalizerAction hPW
  obtain ⟨η,hηc⟩ := c.exists_original_quotient_action hPW hPZ
  let a : P →* MulAut SL(2,F) :=
    (MulAut.congr e).toMonoidHom.comp
      ((quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp (inclusion hPL)))
  have ha (p : P) (l : L) : a p (q l) = q (L.normalizerMonoidHom (inclusion hPL p) l) := by
    change e (quotientAut (pCore 2 L)
      (L.normalizerMonoidHom (inclusion hPL p)) (e.symm (e (QuotientGroup.mk' _ l)))) = _
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have ht := BinaryConjugationSection.originalNormalizerAction_compatible q hq σ hσ hPL hPW a ha
  have hη (p : P) (w : Additive W) : π (τ p w) = η p (π w) := by
    rw [hπc,hπc,hηc]
    exact congrArg (fun x => (c.coordinates x).toAdd)
      (BinaryConjugationSection.originalNormalizerAction_apply hPW p w)
  have hqa := BinaryConjugationSection.quotient_action_compatible π hπ.1 τ η a ht hη
  obtain ⟨v,_,hv,hvf⟩ := BinaryOffender.PermutedSupports.exists_nonzero_fixed η ⊤
    (hP.of_injective (⊤ : Subgroup P).subtype Subtype.val_injective)
    ⊤ top_ne_bot (le_subspaceStabilizer η ⊤ (fun _ _ _ _ => Submodule.mem_top))
  obtain ⟨w,hw,hwf⟩ := SL2OrthogonalCover.FullFixed.fixed_lift_of_cover
    degree hdegree hF π hπ a η τ hqa ht hη (fun p => hvf ⟨p,mem_top p⟩)
  refine ⟨w.toMul,?_,?_⟩
  · intro p hp
    have hh := BinaryConjugationSection.originalNormalizerAction_apply_coe hPW ⟨p,hp⟩ w
    rw [hwf] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  · intro hz
    apply hv
    rw [←hw,hπc,hz]
    rfl
end CFSG.Quasithin.Chapter10.MovingHall
