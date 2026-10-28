module
public import CFSG.Quasithin.Chapter10.SourceA5MovedSeedTypes
public import Theory.GroupTheory.ReducedNormal.SubspaceGroupConsequences
public import CFSG.Quasithin.Chapter10.SourceA5LocalSeedReduction
/-!
# Lifting original A₅ seed support

The source seed is a subspace of the actual reduced module for L₀T.
Its marked A₅ × A₅ action is taken on the image in the quotient by
C(L₀). If one marked factor acts trivially there, every displacement
on the seed is fixed by that factor. For each seed vector these
displacements then define a homomorphism from a perfect group to an
abelian group, so all displacements vanish. Thus the corresponding
original subgroup centralizes the actual seed.

Both factor orientations use the literal original product projection.
The final consumer discharges the separated-seed premise of the original
moved-action theorem from an exclusion of simultaneous support. Its
independent full/local module identity remains an explicit premise.

Source: Aschbacher–Smith, D.3.5, printed pp. 195–196; the source
moved-action consumer is 10.1.1, printed p.741.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u

private theorem fixed_of_perfect_central_displacement {A V : Type*} [Group A]
    [Group.IsPerfect A] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) (v : V)
    (h : ∀ a b : A, ρ a (ρ b v - v) = ρ b v - v) (a : A) : ρ a v = v := by
  let f : A →* Multiplicative V :=
    { toFun := fun g => Multiplicative.ofAdd (ρ g v - v)
      map_one' := by simp
      map_mul' := by
        intro g t
        change ρ (g * t) v - v = (ρ g v - v) + (ρ t v - v)
        have ht := h g t
        rw [map_sub] at ht
        rw [map_mul, Module.End.mul_apply]
        calc
          _ = (ρ g (ρ t v) - ρ g v) + (ρ g v - v) := by abel
          _ = _ := by rw [ht]; abel }
  have hz : f a = 1 := Abelianization.commutator_subset_ker f
    (Group.IsPerfect.mem_commutator (g := a))
  exact sub_eq_zero.mp hz

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))

private theorem seed_centralizes_of_projection_trivial
    (A : Subgroup G) [Group.IsPerfect A] (hAO : A ≤ localOrbit T L)
    (htriv : ∀ a : A, originalA5SeedAction D e hn ht htn
      (originalA5ProductProjection D e hn ht htn ⟨a,hAO a.property⟩) = 1) :
    D.seed ≤ centralizer (A : Set G) := by
  let H := localJoin T L
  let X := (localOrbit T L).subgroupOf H
  let ρ := ReducedNormal.representation H
  let f : A →* H := A.inclusion (hAO.trans le_sup_left)
  have hfix (v : Additive (ReducedNormal.ModuleGroup H)) (hv : v ∈ D.seedSpace)
      (a : A) : ρ (f a) v = v := by
    apply fixed_of_perfect_central_displacement (ρ.comp f) v
    intro b c
    have hd : ρ (f c) v - v ∈ fixedSpace ρ X := by
      let cX : X := ⟨f c,hAO c.property⟩
      let vQ : (originalSeedCentralImage D).toSubmodule :=
        ⟨(fixedSpace ρ X).mkQ v,⟨v,hv,rfl⟩⟩
      have he := originalA5SeedAction_apply D e hn ht htn cX vQ
      change originalA5SeedAction D e hn ht htn
        (originalA5ProductProjection D e hn ht htn ⟨c,hAO c.property⟩) vQ = _ at he
      rw [htriv c] at he
      have he' := congrArg Subtype.val he
      change (fixedSpace ρ X).mkQ v = (fixedSpace ρ X).mkQ (ρ (f c) v) at he'
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change (fixedSpace ρ X).mkQ (ρ (f c) v - v) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr he'.symm
    exact hd ⟨f b,hAO b.property⟩
  rintro _ ⟨_,⟨v,hv,rfl⟩,rfl⟩
  apply (ReducedNormal.mem_reduced_fixedSpace_iff H A (hAO.trans le_sup_left) _).mp
  intro a
  exact hfix (Additive.ofMul v) hv ⟨a.val.val,a.property⟩

/-- A trivial original first factor fixes the actual seed. -/
theorem source_a5_seed_centralizes_left_of_trivial
    (hleft : ∀ g, originalA5SeedAction D e hn ht htn (g,1) = 1) :
    D.seed ≤ centralizer (L : Set G) := by
  let : Group.IsPerfect L := by
    let := D.maximal.1.1.perfect
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  apply seed_centralizes_of_projection_trivial D e hn ht htn L (le_componentOrbit L T)
  intro l
  rw [originalA5ProductProjection_first]
  exact hleft _

/-- A trivial original second factor fixes the actual seed. -/
theorem source_a5_seed_centralizes_right_of_trivial
    (hright : ∀ g, originalA5SeedAction D e hn ht htn (1,g) = 1) :
    D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  let : Group.IsPerfect L := by
    let := D.maximal.1.1.perfect
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  let : Group.IsPerfect (L.map (MulAut.conj t).toMonoidHom) := Group.IsPerfect.map _
  have hAO : L.map (MulAut.conj t).toMonoidHom ≤ localOrbit T L :=
    le_iSup (fun s : (T : Subgroup G) => L.map (MulAut.conj (s : G)).toMonoidHom) ⟨t,ht⟩
  apply seed_centralizes_of_projection_trivial D e hn ht htn _ hAO
  rintro ⟨_,a,ha,rfl⟩
  change originalA5SeedAction D e hn ht htn
    (originalA5ProductProjection D e hn ht htn (originalConjugateOrbitInclusion ht ⟨a,ha⟩)) = 1
  rw [originalA5ProductProjection_second]
  exact hright _

/-- Failure of actual seed separation forces nontrivial action of both
original marked A₅ factors on its central image. -/
theorem source_a5_seed_both_factors_nontrivial_of_not_separated
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    (∃ g, originalA5SeedAction D e hn ht htn (g,1) ≠ 1) ∧
      (∃ g, originalA5SeedAction D e hn ht htn (1,g) ≠ 1) := by
  classical
  constructor
  · by_contra hleft
    have htriv : ∀ g, originalA5SeedAction D e hn ht htn (g,1) = 1 := by
      simpa only [not_exists, not_not] using hleft
    exact hsep (Or.inr (source_a5_seed_centralizes_left_of_trivial D e hn ht htn htriv))
  · by_contra hright
    have htriv : ∀ g, originalA5SeedAction D e hn ht htn (1,g) = 1 := by
      simpa only [not_exists, not_not] using hright
    exact hsep (Or.inl (source_a5_seed_centralizes_right_of_trivial D e hn ht htn htriv))

/-- Excluding simultaneous support on the original quotient factors gives
exactly the original source seed-separation alternative. -/
theorem source_a5_seed_separated_of_not_both_active
    (h : ¬ ((∃ g, originalA5SeedAction D e hn ht htn (g,1) ≠ 1) ∧
      (∃ g, originalA5SeedAction D e hn ht htn (1,g) ≠ 1))) :
    D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G) := by
  classical
  by_contra hsep
  exact h (source_a5_seed_both_factors_nontrivial_of_not_separated D e hn ht htn hsep)

local instance movedSeedSupportElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The model exclusion of simultaneous quotient support discharges the
source separation hypothesis for the literal original moved action.
The independent full/local module identity remains explicit. -/
theorem source_a5_original_irreducible_of_not_both_seed_factors_active
    (hfull : D.fullModule = D.moduleSubgroup)
    (h : ¬ ((∃ g, originalA5SeedAction D e hn ht htn (g,1) ≠ 1) ∧
      (∃ g, originalA5SeedAction D e hn ht htn (1,g) ≠ 1))) :
    (originalMovedQuotientAction D e).IsIrreducible ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  source_a5_original_irreducible_of_separated_seed D hn ht htn e hfull
    (source_a5_seed_separated_of_not_both_active D e hn ht htn h)

end CFSG.Quasithin.Chapter10
