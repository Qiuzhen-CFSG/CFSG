module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.Alternatives
public import Theory.Representation.SL2OrthogonalCover.Universal
public import Theory.Representation.FirstCohomologyDuality.Indecomposable
public import Theory.Representation.BinaryOffender.InvolutionFixed
public import Theory.Representation.BinaryConjugationSection.Cover
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global

/-!
# Fixed vectors outside the original component kernel

A full local involution normalizing the moved factor has a fixed vector outside
its original component-fixed part. The proof keeps the literal quotient map:
the natural branch uses the binary SL₂ central-cover bound (kernel degree at
most two), while the deleted branch has trivial fixed kernel. The full actor
is the actual normalizer action on the moved factor; it is never replaced by
A₅. Source: Aschbacher–Smith 10.1.1, printed p.741, and 10.2.12, p.754.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement


open Representation Subgroup



open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
/-- Apply the binary dimension argument to the literal ambient normalizer action. -/
theorem involution_fixed_not_le_of_projection
    (W Z : Subgroup G) [IsElementaryAbelian 2 W]
    (p : Additive W →ₗ[ZMod 2] V) (hp : Function.Surjective p)
    (hker : ∀ w : Additive W, p w = 0 ↔ (w.toMul : G) ∈ Z)
    (hbound : Module.finrank (ZMod 2) p.ker ≤ 2)
    (hdim : Module.finrank (ZMod 2) V = 4)
    {b : G} (hb : b ∈ normalizer (W : Set G)) (ho : orderOf b = 2) :
    ¬ W ⊓ centralizer ({b} : Set G) ≤ Z := by
  let τ := (ChapterE.automizerRepresentation W).comp W.normalizerMonoidHom.rangeRestrict
  let bN : normalizer (W : Set G) := ⟨b,hb⟩
  have hbo : orderOf bN = 2 := (Subgroup.orderOf_coe bN).symm.trans ho
  have hd := p.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hp,finrank_top,hdim] at hd
  obtain ⟨w,hw,hwn⟩ := exists_fixed_outside_of_finrank_quotient_four
    τ bN hbo p.ker hbound hd.symm
  intro hc
  apply hwn
  apply (hker w).mpr
  apply hc
  refine ⟨w.toMul.property,mem_centralizer_singleton_iff.mpr ?_⟩
  have hf := (mem_fixedSpace_zpowers_iff τ bN w).mp hw
  have he := congrArg (fun v : Additive W => (v.toMul : G)) hf
  change b * (w.toMul : G) * b⁻¹ = w.toMul at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end CFSG.Quasithin.Chapter10


open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Theory.GroupTheory
open Representation.OneCohomology
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
local instance originalFixedVectorsElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance originalFixedVectorsFieldFourAlgebra :
    Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

/-- A normalizing involution fixes a noncentral vector in the original natural cover. -/
theorem source_a5_original_natural_involution_fixed_not_le
    (f : alternatingGroup (Fin 5) ≃*
      SL(2,Representation.OrthogonalFourMinus.FiniteModel.Field 1))
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (Representation.SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    {b : G} (hb : b ∈ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (ho : orderOf b = 2) :
    ¬ (⁅D.fullModule,L⁆ : Subgroup G) ⊓ centralizer ({b} : Set G) ≤ centralizer (L : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let r := f.toMonoidHom.comp q
  have hr : Function.Surjective r := f.surjective.comp
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨σ,hfaith,hσ⟩ := source_a5_original_moved_action D e
  let τ := σ.comp f.symm.toMonoidHom
  have hτ : ∀ (l : L) (w : Additive W),
      ((τ (r l) w).toMul : G) = l * w.toMul * (l : G)⁻¹ := by
    intro l w
    change ((σ (f.symm (f (q l))) w).toMul : G) = _
    rw [f.symm_apply_apply]
    exact hσ l w
  obtain ⟨p,hp,hcoord⟩ := c.exists_cover_of_fully_moved
    Representation.SL2.BinarySmall.natural r hr τ hτ inf_le_right
      (source_full_moved_eq_commutator D)
  have hF : Nat.card (Representation.OrthogonalFourMinus.FiniteModel.Field 1) = 2 ^ 2 :=
    GaloisField.card 2 2 (by decide)
  have hk := finrank_ker_le_H1_of_cover p hp
  change Module.finrank (ZMod 2) p.toLinearMap.ker ≤
      Module.finrank (ZMod 2) (H1
        (Representation.SL2OrthogonalCover.binaryNatural
          (F := Representation.OrthogonalFourMinus.FiniteModel.Field 1)).dual) at hk
  rw [Representation.SL2OrthogonalCover.binary_dual_H1_finrank 2 (by decide) hF] at hk
  have hd : Module.finrank (ZMod 2)
      (Fin 2 → Representation.OrthogonalFourMinus.FiniteModel.Field 1) = 4 := by
    rw [Module.finrank_pi_fintype,Representation.SL2NaturalH1.field_finrank 2 hF]
    decide
  have hker : ∀ w : Additive W, p w = 0 ↔ (w.toMul : G) ∈ sourceMovedFixed D := by
    intro w
    rw [hcoord w]
    exact c.coordinates_eq_one_iff w.toMul
  intro hc
  exact involution_fixed_not_le_of_projection W (sourceMovedFixed D) p.toLinearMap hp.1
    hker hk hd hb ho (le_inf inf_le_left hc)

/-- The chosen original A₅ factor has a noncentral fixed vector for every normalizing involution. -/
theorem source_a5_original_involution_fixed_not_le_of_irreducible
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {b : G} (hb : b ∈ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (ho : orderOf b = 2) :
    ¬ (⁅D.fullModule,L⁆ : Subgroup G) ⊓ centralizer ({b} : Set G) ≤ centralizer (L : Set G) := by
  rcases source_a5_original_module_alternatives_of_irreducible D e hi with
    ⟨f,⟨c⟩⟩ | ⟨hz,_⟩
  · exact source_a5_original_natural_involution_fixed_not_le D e f c hb ho
  · let W := ⁅D.fullModule,L⁆
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    let ρ := originalMovedQuotientAction D e
    let c := originalMovedQuotientSection D e
    have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
    obtain ⟨σ,_,hσ⟩ := source_a5_original_moved_action D e
    obtain ⟨p,hp,hcoord⟩ := c.exists_cover_of_fully_moved ρ q hq σ hσ inf_le_right
      (source_full_moved_eq_commutator D)
    have hker : ∀ w : Additive W, p w = 0 ↔ (w.toMul : G) ∈ sourceMovedFixed D := by
      intro w
      rw [hcoord w]
      exact c.coordinates_eq_one_iff w.toMul
    have hk : p.toLinearMap.ker = ⊥ := by
      ext w
      change p w = 0 ↔ w = 0
      rw [hker,hz,mem_bot]
      exact ⟨fun h => Additive.toMul.injective (Subtype.ext h),
        fun h => congrArg (fun v : Additive W => (v.toMul : G)) h⟩
    have hkdim : Module.finrank (ZMod 2) p.toLinearMap.ker ≤ 2 := by
      rw [hk,finrank_bot]
      decide
    have hd := (source_a5_original_quotient_alternatives_of_irreducible D e hi).1
    intro hc
    exact involution_fixed_not_le_of_projection W (sourceMovedFixed D) p.toLinearMap hp.1
      hker hkdim hd hb ho (le_inf inf_le_left hc)

end CFSG.Quasithin.Chapter10
