module
public import CFSG.Quasithin.Chapter10.SourceA5MovedSeedModels
public import CFSG.Quasithin.Chapter10.SourceA5MovedNaturalOrbit
public import CFSG.Quasithin.Chapter10.SourceA5MovedMixedOrbit
public import CFSG.Quasithin.Chapter10.SourceA5LocalCentralQuotient.OrbitModel

/-!
# The two literal models of the original proper moved local quotient

A proper seed on which both A₅ factors act has one of four marked constituent
models. Homogeneity makes its central orbit the natural pair or the mixed
pair. Descent through the original central quotient preserves the specified
A₅ × A₅ marking and the unchanged local actor. The resulting action is faithful,
its marked product is normal, and the original source cubic bound still holds.

The final consumer constructs all quotient and orbit witnesses from the original
setup. In particular, no seed classification or intertwining witness remains
as a premise.

Source: Aschbacher–Smith, D.3.5, printed pp.195–196, and 3.2.2(3).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.AlternatingFiveMovedPair
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
local notation "Alt" => alternatingGroup (Fin 5)
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
local instance movedLocalElementary (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 D.moduleSubgroup := D.module_elementary

/-- The actual marked local quotient is a natural or mixed pair whenever the
original proper seed has both product factors active. -/
theorem source_a5_moved_local_quotient_model_alternatives
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* Alt)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hproper : D.seed ≠ D.moduleSubgroup)
    (hleft : ∃ g, originalA5SeedAction D e hn ht htn (g,1) ≠ 1)
    (hright : ∃ g, originalA5SeedAction D e hn ht htn (1,g) ≠ 1)
    (base : Alt ≃* SL2FourNatural.SL) :
    let U := D.moduleSubgroup.subgroupOf (localJoin T L)
    let := (source_parabolic_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set (localJoin T L)))
    ∀ (τ : Representation (ZMod 2)
        ((localJoin T L) ⧸ centralizer (U : Set (localJoin T L)))
        (Additive (sourceLocalCentralQuotient D)))
      (i : Alt × Alt →* ((localJoin T L) ⧸ centralizer (U : Set (localJoin T L)))),
      (∀ x : localOrbit T L,
        i (originalA5ProductProjection D e hn ht htn x) =
          q (inclusion (show localOrbit T L ≤ localJoin T L from le_sup_left) x)) →
      (∀ (m : localJoin T L) (v : D.moduleSubgroup),
        τ (q m) (Additive.ofMul (QuotientGroup.mk' (sourceLocalCentralizer D) v)) =
          Additive.ofMul (QuotientGroup.mk' (sourceLocalCentralizer D)
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.join_normalizes_module m.property) v).mp
                v.property⟩)) →
      Nonempty (Representation.Equiv (τ.comp i)
        (Natural.action.comp (base.prodCongr base).toMonoidHom)) ∨
      Nonempty (Representation.Equiv (τ.comp i)
        (Mixed.action.comp (base.prodCongr base).toMonoidHom)) := by
  dsimp only
  let := (source_parabolic_module_reduced D).normal
  intro τ i hi hτ
  have hnmodel (b : Bool)
      (eb : (originalA5SeedAction D e hn ht htn).Equiv
        ((NaturalTypes.model b).comp (base.prodCongr base).toMonoidHom)) :
      Nonempty (Representation.Equiv (τ.comp i)
        (Natural.action.comp (base.prodCongr base).toMonoidHom)) := by
    obtain ⟨a⟩ := source_a5_moved_natural_central_orbit D e hn ht htn hproper base b eb
    exact source_local_quotient_model_equiv D e hn ht htn
      (Natural.action.comp (base.prodCongr base).toMonoidHom) τ hτ i hi a
  rcases source_a5_moved_seed_fixed_model_alternatives D e hn ht htn
      hproper hleft hright base with h0 | h1 | hnd | hdn
  · obtain ⟨a⟩ := h0
    exact Or.inl (hnmodel false a)
  · obtain ⟨a⟩ := h1
    exact Or.inl (hnmodel true a)
  · exact Or.inr (source_a5_moved_mixed_local_quotient D e hn ht htn hproper base
      (Or.inl hnd) τ i hi hτ)
  · exact Or.inr (source_a5_moved_mixed_local_quotient D e hn ht htn hproper base
      (Or.inr hdn) τ i hi hτ)

/-- Original source data supply a faithful cubic-bounded local action, a normal
marked product embedding, and one of the two literal full orbit models.
Both exact original quotient diagrams are retained in the conclusion. -/
theorem source_a5_moved_local_central_quotient_models
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* Alt)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hproper : D.seed ≠ D.moduleSubgroup)
    (hleft : ∃ g, originalA5SeedAction D e hn ht htn (g,1) ≠ 1)
    (hright : ∃ g, originalA5SeedAction D e hn ht htn (1,g) ≠ 1)
    (base : Alt ≃* SL2FourNatural.SL)
    (hbound : SourceLocalModuleCubicBound D) :
    let U := D.moduleSubgroup.subgroupOf (localJoin T L)
    let := (source_parabolic_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set (localJoin T L)))
    ∃ (τ : Representation (ZMod 2)
        ((localJoin T L) ⧸ centralizer (U : Set (localJoin T L)))
        (Additive (sourceLocalCentralQuotient D)))
      (i : Alt × Alt →* ((localJoin T L) ⧸ centralizer (U : Set (localJoin T L)))),
      Function.Injective τ ∧ BinaryOffender.cubicRatio τ ≤ 2 ∧
      Function.Injective i ∧ i.range.Normal ∧
      (∀ x : localOrbit T L,
        i (originalA5ProductProjection D e hn ht htn x) =
          q (inclusion (show localOrbit T L ≤ localJoin T L from le_sup_left) x)) ∧
      (∀ (m : localJoin T L) (v : D.moduleSubgroup),
        τ (q m) (Additive.ofMul (QuotientGroup.mk' (sourceLocalCentralizer D) v)) =
          Additive.ofMul (QuotientGroup.mk' (sourceLocalCentralizer D)
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.join_normalizes_module m.property) v).mp
                v.property⟩)) ∧
      (Nonempty (Representation.Equiv (τ.comp i)
        (Natural.action.comp (base.prodCongr base).toMonoidHom)) ∨
       Nonempty (Representation.Equiv (τ.comp i)
        (Mixed.action.comp (base.prodCongr base).toMonoidHom))) := by
  dsimp only
  let := (source_parabolic_module_reduced D).normal
  obtain ⟨τ,i,hfaithful,hcubic,hinjective,hnormal,hi,hτ⟩ :=
    source_a5_local_central_quotient_data D e hn ht htn hbound
  exact ⟨τ,i,hfaithful,hcubic,hinjective,hnormal,hi,hτ,
    source_a5_moved_local_quotient_model_alternatives D e hn ht htn
      hproper hleft hright base τ i hi hτ⟩

end CFSG.Quasithin.Chapter10
