module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalCentralizerControl
public import Theory.Representation.AlternatingFiveMovedPair.SeparatedCentralizer

/-!
# Actual separated coordinates kill the original A₅-pair centralizer

The original projection diagram identifies the marked pair with the literal
orbit image in the full actor. Restricting the faithful full-quotient action
to its centralizer gives a faithful commuting action. Natural or deleted
coordinates with multiplicity at most two put this centralizer in the two
small multiplicity general linear groups. Its order is prime to fifteen, so
it is a two-group and reducedness makes it trivial.

The final consumers retain both original quotient diagrams and conclude
full/local equality, then original moved-quotient irreducibility and conjugate
cross-centralization. Coordinate existence and the multiplicity bound remain
explicit inputs of their independent source producers. Source:
Aschbacher–Smith D.3.9 and the separated case of D.3.21, pp.199–201,206.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
open Representation.AlternatingFiveMovedPair.SeparatedCentralizer

/-- Bounded copies of either fixed binary model, on the original marked pair. -/
def SourceA5SmallSeparatedCoordinates {Q W : Type*} [Group Q]
    [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) Q W) (i : Alt × Alt →* Q) : Prop :=
  (∃ k : ℕ, k ≤ 2 ∧ ∃ c : W ≃ₗ[ZMod 2] ((Fin k → Natural) × (Fin k → Natural)),
    ∀ d v, c (τ (i d) v) =
      (fun j => natural d.1 ((c v).1 j), fun j => natural d.2 ((c v).2 j))) ∨
  (∃ k : ℕ, k ≤ 2 ∧ ∃ c : W ≃ₗ[ZMod 2] ((Fin k → Deleted) × (Fin k → Deleted)),
    ∀ d v, c (τ (i d) v) =
      (fun j => deleted d.1 ((c v).1 j), fun j => deleted d.2 ((c v).2 j)))

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
local instance originalSeparatedCentralizerFullElementary : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The original quotient diagram determines the literal orbit image. -/
theorem source_a5_original_marked_orbit_range
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    ∀ i : Alt × Alt →* (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)),
      (∀ x : localOrbit T L,
        i (originalA5ProductProjection D e hn ht htn x) =
          q (inclusion (localOrbit T L).le_normalizer x)) →
      i.range = ((localOrbit T L).subgroupOf D.maximalLocal).map q := by
  dsimp only
  let := (source_full_module_reduced D).normal
  intro i hdiagram
  ext y
  constructor
  · rintro ⟨a,rfl⟩
    obtain ⟨x,rfl⟩ := originalA5ProductProjection_surjective D e hn ht htn a
    rw [hdiagram]
    exact ⟨inclusion (localOrbit T L).le_normalizer x,x.property,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨originalA5ProductProjection D e hn ht htn ⟨x,hx⟩,hdiagram ⟨x,hx⟩⟩

/-- Bounded actual pair coordinates force the original actor centralizer to vanish. -/
theorem source_a5_original_actor_centralizer_eq_bot_of_bounded_coordinates
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    ∀ (τ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
        (Additive D.fullCentralQuotient))
      (i : Alt × Alt →* (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))),
      Function.Injective τ →
      (∀ x : localOrbit T L,
        i (originalA5ProductProjection D e hn ht htn x) =
          q (inclusion (localOrbit T L).le_normalizer x)) →
      SourceA5SmallSeparatedCoordinates τ i →
      centralizer (J : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))) = ⊥ := by
  dsimp only
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).normal
  let Q := D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)
  let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
  let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
  let C := centralizer (J : Set Q)
  intro τ i hτ hi hcoords
  have hr : i.range = J := source_a5_original_marked_orbit_range D e hn ht htn i hi
  let ρ := τ.comp C.subtype
  have hfaith : Function.Injective ρ := hτ.comp Subtype.val_injective
  have hcomm (a : C) (d : Alt × Alt) (v : Additive D.fullCentralQuotient) :
      ρ a ((τ.comp i) d v) = (τ.comp i) d (ρ a v) := by
    have hd : i d ∈ J := hr ▸ (show i d ∈ i.range from ⟨d,rfl⟩)
    have ha := a.property (i d) hd
    change τ (a : Q) (τ (i d) v) = τ (i d) (τ (a : Q) v)
    simp only [←Module.End.mul_apply,←map_mul]
    rw [ha]
  have hc := source_a5_original_actor_centralizer_coprime D e hn ht htn
  apply source_full_actor_orbit_centralizer_eq_bot_of_two D
  rcases hcoords with ⟨k,hk,c,hc'⟩ | ⟨k,hk,c,hc'⟩
  · exact natural_isPGroup_two_of_coordinates hk (τ.comp i) ρ hfaith hcomm c hc' hc.1 hc.2
  · exact deleted_isPGroup_two_of_coordinates hk (τ.comp i) ρ hfaith hcomm c hc' hc.1 hc.2

/-- Bounded coordinates of the actual full quotient, retaining both source diagrams. -/
def SourceA5OriginalBoundedSeparatedCoordinates
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) : Prop :=
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
  ∃ (τ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
      (Additive D.fullCentralQuotient))
    (i : Alt × Alt →* (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))),
    Function.Injective τ ∧
    (∀ x : localOrbit T L,
      i (originalA5ProductProjection D e hn ht htn x) =
        q (inclusion (localOrbit T L).le_normalizer x)) ∧
    (∀ (m : D.maximalLocal) (v : D.fullModule),
      τ (q m) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
        Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
          ⟨(m : G) * (v : G) * (m : G)⁻¹,
            (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
              v.property⟩)) ∧
    SourceA5SmallSeparatedCoordinates τ i

/-- The actual bounded coordinate witness concludes full/local equality. -/
theorem source_a5_full_eq_local_of_bounded_separated_coordinates
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hcoords : SourceA5OriginalBoundedSeparatedCoordinates D e hn ht htn) :
    D.fullModule = D.moduleSubgroup := by
  obtain ⟨τ,i,hτ,hi,_,hc⟩ := hcoords
  exact source_a5_full_eq_local_of_actor_pair_centralizer_eq_bot D e hn ht htn
    (source_a5_original_actor_centralizer_eq_bot_of_bounded_coordinates
      D e hn ht htn τ i hτ hi hc)

local instance originalSeparatedCentralizerMovedElementary :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The separated source seed and bounded actual coordinates conclude the
literal original quotient irreducibility and conjugate cross-centralization. -/
theorem source_a5_original_irreducible_of_bounded_separated_coordinates
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (hcoords : SourceA5OriginalBoundedSeparatedCoordinates D e hn ht htn) :
    (originalMovedQuotientAction D e).IsIrreducible ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  source_a5_original_irreducible_of_separated_seed D hn ht htn e
    (source_a5_full_eq_local_of_bounded_separated_coordinates D e hn ht htn hcoords) hsep

end CFSG.Quasithin.Chapter10
