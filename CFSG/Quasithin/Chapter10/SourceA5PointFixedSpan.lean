module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.Alternatives
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.BinaryConjugationSection.FixedGeneration
public import Theory.Representation.CentralCoverFixedGeneration
public import Theory.Representation.SL2OrthogonalCover.FullFixed.Quotients
public import Theory.Representation.Quotient
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import CFSG.Quasithin.Chapter10.SourceA5ElementComponent

/-!
# Fixed spans in the original A5 point centralizer

For W=[D.fullModule,L], every two-subgroup P of M normalizing L has
C_W(P) whose L-orbit generates W. The natural row lifts fixed quotient
vectors uniquely through the singular vectors of the universal orthogonal
cover; the deleted row uses projectivity. Irreducibility and full movement
then give the whole original numerator, retaining its literal conjugation
and quotient maps. The last results specialize to P=C_T(v) and the actual
containing-component orbit used by the constrained inspection.

Source: Aschbacher–Smith10.2.9, printed p.751, with the natural-cover
geometry of I.2.3. Chosen irreducibility remains the separate original
module-classification input.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
local instance pointFixedSpanElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance pointFixedSpanFieldFourAlgebra : Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

private theorem original_marking_irreducible
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    (f : alternatingGroup (Fin 5) ≃* J) (ρ : Representation (ZMod 2) J V)
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (ρ.comp (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) :
    ρ.IsIrreducible := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hc : Representation.IsIrreducible (ρ.comp (f.toMonoidHom.comp q)) :=
    (originalMovedQuotientSection D e).irreducible_of_same_section c
      ((irreducible_comp_surjective_iff q hq (originalMovedQuotientAction D e)).mpr hi)
  exact (irreducible_comp_surjective_iff (f.toMonoidHom.comp q)
    (f.surjective.comp hq) ρ).mp hc

private theorem original_fixed_span
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (f : alternatingGroup (Fin 5) ≃* J) (ρ : Representation (ZMod 2) J V)
    [ρ.IsIrreducible]
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (ρ.comp (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (P : Subgroup G) (hPM : P ≤ D.maximalLocal) (hPL : P ≤ normalizer (L : Set G))
    (hP : IsPGroup 2 P)
    (hlift : ∀ (σ : Representation (ZMod 2) J (Additive (⁅D.fullModule,L⁆ : Subgroup G)))
      (q : σ.IntertwiningMap ρ), IsCover q →
      ∀ (a : P →* MulAut J) (η : Representation (ZMod 2) P V)
        (τ : Representation (ZMod 2) P (Additive (⁅D.fullModule,L⁆ : Subgroup G))),
      (∀ p j v, η p (ρ j v) = ρ (a p j) (η p v)) →
      (∀ p j w, τ p (σ j w) = σ (a p j) (τ p w)) →
      (∀ p w, q (τ p w) = η p (q w)) →
      ∀ v, (∀ p, η p v = v) → ∃ w, q w = v ∧ ∀ p, τ p w = w) :
    conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) L = ⁅D.fullModule,L⁆ := by
  let W := ⁅D.fullModule,L⁆
  let q := f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  have hq : Function.Surjective q := f.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨σ₀,_,hσ₀⟩ := source_a5_original_moved_action D e
  let σ := σ₀.comp f.symm.toMonoidHom
  have hσ : ∀ (l : L) (w : Additive W), ((σ (q l) w).toMul : G) = l*w.toMul*(l : G)⁻¹ := by
    intro l w
    change ((σ₀ (f.symm (f (e (QuotientGroup.mk' (pCore 2 L) l)))) w).toMul : G) = _
    rw [f.symm_apply_apply]
    exact hσ₀ l w
  have hPW : P ≤ normalizer (W : Set G) := by
    intro p hp
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule (hPM hp)),
      mem_normalizer_iff_map_conj_eq.mp (hPL hp)]
  have hPZ : P ≤ normalizer (sourceMovedFixed D : Set G) :=
    (le_inf hPL hPW).trans (source_original_moved_fixed_normalizer D)
  obtain ⟨π,hπ,hπc⟩ := c.exists_cover_of_fully_moved ρ q hq σ hσ inf_le_right
    (source_full_moved_eq_commutator D)
  let τ := BinaryConjugationSection.originalNormalizerAction hPW
  obtain ⟨η,hηc⟩ := c.exists_original_quotient_action hPW hPZ
  let a : P →* MulAut J :=
    (MulAut.congr (e.trans f)).toMonoidHom.comp
      ((quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp (inclusion hPL)))
  have ha (p : P) (l : L) : a p (q l) = q (L.normalizerMonoidHom (inclusion hPL p) l) := by
    change (e.trans f) (quotientAut (pCore 2 L)
      (L.normalizerMonoidHom (inclusion hPL p)) ((e.trans f).symm ((e.trans f) (QuotientGroup.mk' _ l)))) = _
    rw [(e.trans f).symm_apply_apply,quotientAut_apply_mk]
    rfl
  have ht := BinaryConjugationSection.originalNormalizerAction_compatible q hq σ hσ hPL hPW a ha
  have hη (p : P) (w : Additive W) : π (τ p w) = η p (π w) := by
    rw [hπc,hπc,hηc]
    exact congrArg (fun x => (c.coordinates x).toAdd)
      (BinaryConjugationSection.originalNormalizerAction_apply hPW p w)
  have hqa := BinaryConjugationSection.quotient_action_compatible π hπ.1 τ η a ht hη
  apply BinaryConjugationSection.conjugateSpan_eq_of_fixed_generation q hq σ hσ τ
    (BinaryConjugationSection.originalNormalizerAction_apply_coe hPW)
    (normalizer_commutator_ge_right _ _)
  intro K hK hfix
  exact eq_top_of_contains_fixed_of_cover π hπ η τ hP
    (hlift σ π hπ a η τ hqa ht hη) K hK hfix
end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
local instance pointFixedSpanNaturalElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance pointFixedSpanNaturalFieldFourAlgebra : Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

/-- Every two-subgroup normalizing the original natural-cover action has a
fixed space whose literal component orbit generates the original moved factor. -/
theorem source_a5_natural_moved_fixed_span
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (f : alternatingGroup (Fin 5) ≃* SL(2,Representation.OrthogonalFourMinus.FiniteModel.Field 1))
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (Representation.SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (P : Subgroup G) (hPM : P ≤ D.maximalLocal) (hPL : P ≤ normalizer (L : Set G))
    (hP : IsPGroup 2 P) :
    conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) L = ⁅D.fullModule,L⁆ := by
  let : (Representation.SL2.BinarySmall.natural (K := Representation.OrthogonalFourMinus.FiniteModel.Field 1)).IsIrreducible :=
    original_marking_irreducible D e hi f _ c
  apply original_fixed_span D e f _ c P hPM hPL hP
  intro σ q hq a η τ ha ht hqt v hv
  exact Representation.SL2OrthogonalCover.FullFixed.fixed_lift_of_cover
    (F := Representation.OrthogonalFourMinus.FiniteModel.Field 1) 2 (by decide)
    (GaloisField.card 2 2 (by decide))
    q hq a η τ ha ht hqt hv

/-- The projective deleted marking has no central covering obstruction, so
its original two-group fixed vectors generate the moved factor as well. -/
theorem source_a5_deleted_moved_fixed_span
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hz : sourceMovedFixed D = ⊥)
    (f : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5))
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (P : Subgroup G) (hPM : P ≤ D.maximalLocal) (hPL : P ≤ normalizer (L : Set G))
    (hP : IsPGroup 2 P) :
    conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) L = ⁅D.fullModule,L⁆ := by
  let c' : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) := by
    rw [hz]; exact c
  let : Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.IsIrreducible :=
    original_marking_irreducible D e hi f _ c'
  let : Module.Projective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5)))
      Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.asModule :=
    BinaryPermutation.alternatingFive_natural_projective
  apply original_fixed_span D e f _ c' P hPM hPL hP
  intro σ q hq a η τ _ _ hqt v hv
  obtain ⟨w,hw⟩ := hq.1 v
  refine ⟨w,hw,fun p => ?_⟩
  apply q.injective_of_projective_of_fixed_kernel hq.1
    (fun x hx j => hq.2.1 hx j) hq.2.2
  rw [hqt,hw,hv]

/-- The actual selected irreducible setup supplies fixed-span generation in
both A5 rows; the original two-subgroup and conjugation maps are retained. -/
theorem source_a5_moved_fixed_span
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (P : Subgroup G) (hPM : P ≤ D.maximalLocal) (hPL : P ≤ normalizer (L : Set G))
    (hP : IsPGroup 2 P) :
    conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) L = ⁅D.fullModule,L⁆ := by
  rcases source_a5_original_module_alternatives_of_irreducible D e hi with
    ⟨f,⟨c⟩⟩ | ⟨hz,f,⟨c⟩⟩
  · exact source_a5_natural_moved_fixed_span D e hi f c P hPM hPL hP
  · exact source_a5_deleted_moved_fixed_span D e hi hz f c P hPM hPL hP
/-- The point centralizer's actual Sylow subgroup supplies the fixed
vectors needed for the source 10.2.9 component-orbit construction. -/
theorem source_a5_point_centralizer_fixed_span
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G)) :
    conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
      (((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G)) L = ⁅D.fullModule,L⁆ := by
  apply source_a5_moved_fixed_span D e hi _
    (inf_le_left.trans (le_normalizer_componentOrbit L T))
    ((inf_le_inf (le_normalizer_componentOrbit L T) le_rfl).trans
      (source_nonnormal_element_centralizer_stabilizes D hn hvL hv0))
    (T.isPGroup'.to_le inf_le_left)

/-- The orbit used by the containing-component inspection contains the
entire original moved factor. This discharges its fixed-span premise. -/
theorem source_a5_point_component_fixed_span_contains
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (I : Subgroup G) (hLI : L ≤ I) :
    ⁅D.fullModule,L⁆ ≤ conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
      (((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G)) I := by
  have hs := source_a5_point_centralizer_fixed_span D e hi hn hvL hv0
  calc
    ⁅D.fullModule,L⁆ = conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
        (((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G)) L := hs.symm
    _ ≤ _ := conjugateSpanBy_mono le_rfl hLI

/-- In the literal constrained orbit, the earlier moved-factor centralizer
bound implies the centralizer bound required by the FF-module inspection. -/
theorem source_a5_point_component_fixed_span_centralizer_le
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (I : Subgroup G) (hLI : L ≤ I) :
    centralizer (↑(conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
      (((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G)) I) : Set G) ≤ D.maximalLocal :=
  (centralizer_le (source_a5_point_component_fixed_span_contains D e hi hn hvL hv0 I hLI)).trans hCW

end CFSG.Quasithin.Chapter10
