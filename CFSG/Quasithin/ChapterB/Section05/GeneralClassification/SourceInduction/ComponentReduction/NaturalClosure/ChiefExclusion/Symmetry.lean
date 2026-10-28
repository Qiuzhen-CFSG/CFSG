module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.Rank
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.CentralFactors
public import Theory.Representation.EndFieldRep

/-!
# Exchanging the natural components in B.5.9

The mixed moved space is symmetric for commuting components. If the natural
seed for either component were its whole moved space, the other perfect
component would act trivially on that space: its commuting action factors
through the units of the finite endomorphism field of the irreducible seed.
Thus both seeds are proper, and the component with larger field degree may
be chosen without changing any of the second-component hypotheses.

The endomorphism-field argument follows the same Schur-lemma proof as
`Representation.PerfectDegreeThree`; it uses the existing finite field
structure on irreducible endomorphisms. No representation-degree estimate
or source classification implication is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, the symmetry preceding inequality (*).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem cross_le {L M : Subgroup G}
    (hc : L ≤ centralizer (M : Set G)) :
    subspaceCommutator ρ (moved ρ L) M ≤ subspaceCommutator ρ (moved ρ M) L := by
  apply Submodule.span_le.mpr
  rintro _ ⟨m, hm, w, hw, rfl⟩
  change ρ m w - w ∈ subspaceCommutator ρ (moved ρ M) L
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, hl, v, _, rfl⟩ := hw
    have he : ρ m (ρ l v) = ρ l (ρ m v) := by
      simp only [← Module.End.mul_apply, ← map_mul]
      rw [hc hl m hm]
    have hv : ρ m v - v ∈ moved ρ M :=
      Submodule.subset_span ⟨m, hm, v, Submodule.mem_top, rfl⟩
    have h := Submodule.subset_span (R := ZMod 2)
      (s := {w | ∃ l ∈ L, ∃ v ∈ moved ρ M, w = ρ l v - v})
      ⟨l, hl, ρ m v - v, hv, rfl⟩
    have he' : ρ m (ρ l v - v) - (ρ l v - v) =
        ρ l (ρ m v - v) - (ρ m v - v) := by
      simp only [map_sub, he]
      abel
    rw [he']
    exact h
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add, add_sub_add_comm] using
      (subspaceCommutator ρ (moved ρ M) L).add_mem ihx ihy
  | smul a x hx ih =>
    simpa only [map_smul, ← smul_sub] using
      (subspaceCommutator ρ (moved ρ M) L).smul_mem a ih

/-- Commuting components have the same mixed moved space in either order. -/
theorem commuting_cross_eq {L M : Subgroup G}
    (hc : L ≤ centralizer (M : Set G)) :
    subspaceCommutator ρ (moved ρ L) M = subspaceCommutator ρ (moved ρ M) L :=
  le_antisymm (cross_le ρ hc) (cross_le ρ (le_centralizer_iff.mp hc))

/-- Exchange the literal components and their seeds, retaining every source clause. -/
def SecondComponent.swap {A L : Subgroup G}
    (seed : NaturalSeed ρ A L) (hL : IsComponent G L) (hLA : ⁅L, A⁆ = L)
    (d : SecondComponent ρ A L) : SecondComponent ρ A d.second where
  second := L
  isComponent := hL
  distinct := d.distinct.symm
  commutator_eq := hLA
  seed := seed
  offender_le := sup_comm L d.second ▸ d.offender_le
  residual_eq := (sup_comm d.second L).trans d.residual_eq
  cross_action := by
    rw [← commuting_cross_eq ρ
      (commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne d.isComponent d.distinct))]
    exact d.cross_action

private theorem commuting_perfect_trivial {H K W : Type*}
    [Group H] [Group K] [Group.IsPerfect K]
    [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (τ : Representation (ZMod 2) H W) [IsIrreducible τ]
    (σ : Representation (ZMod 2) K W)
    (hc : ∀ h k, τ h * σ k = σ k * τ h) : σ = 1 := by
  let t : K →* IntertwiningMap τ τ :=
    { toFun := fun k => ⟨σ k, fun h => (hc h k).symm⟩
      map_one' := by ext v; exact DFunLike.congr_fun (map_one σ) v
      map_mul' := by intro a b; ext v; exact DFunLike.congr_fun (map_mul σ a b) v }
  let e := IntertwiningMap.equivAlgEnd τ
  let f := (e.toMonoidHom.comp t).toHomUnits
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hf (k : K) : f k = 1 := congrArg Subtype.val
    (Subsingleton.elim (⟨f k, k, rfl⟩ : f.range) 1)
  ext k v
  have ht : t k = 1 := e.toMulEquiv.injective (by
    rw [map_one]
    exact congrArg Units.val (hf k))
  exact DFunLike.congr_fun (congrArg IntertwiningMap.toLinearMap ht) v

/-- A perfect commuting actor centralizes a moved space which is natural irreducible. -/
theorem natural_moved_centralized [Module.Finite (ZMod 2) V]
    {A L M : Subgroup G} [Group.IsPerfect M]
    (seed : NaturalSeed ρ A L) (he : seed.space.toSubmodule = moved ρ L)
    (hc : L ≤ centralizer (M : Set G)) : moved ρ L ≤ fixedSpace ρ M := by
  let W := componentSpace ρ seed
  let : IsIrreducible W.toRepresentation :=
    (Subrepresentation.irreducible_iff_isAtom W).mpr (componentSpace_isAtom ρ seed)
  have hs : M ≤ subspaceStabilizer ρ W.toSubmodule := by
    change M ≤ subspaceStabilizer ρ seed.space.toSubmodule
    rw [he]
    apply subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by simp))
    exact (le_centralizer_iff.mp hc).trans (centralizer_le_normalizer _)
  let σ := (invariantSubspace ρ M W.toSubmodule hs).toRepresentation
  have hσ : σ = 1 := commuting_perfect_trivial W.toRepresentation σ (by
    intro l m
    ext v
    change ρ l (ρ m v) = ρ m (ρ l v)
    simp only [← Module.End.mul_apply, ← map_mul]
    rw [hc l.property m m.property])
  intro v hv m
  have hv' : v ∈ W.toSubmodule := by change v ∈ seed.space.toSubmodule; rwa [he]
  exact congrArg Subtype.val
    (DFunLike.congr_fun (DFunLike.congr_fun hσ m) (⟨v, hv'⟩ : W.toSubmodule))

/-- The cross action forces the first seed to be proper; swapping gives the second. -/
theorem SecondComponent.seed_lt_moved [Finite G] [Module.Finite (ZMod 2) V]
    {A L : Subgroup G} (seed : NaturalSeed ρ A L)
    (hL : IsComponent G L) (d : SecondComponent ρ A L) :
    seed.space.toSubmodule < moved ρ L := by
  apply lt_of_le_of_ne (seed_le_moved ρ seed)
  intro he
  let : IsQuasisimple d.second := d.isComponent.2
  exact d.cross_action ((subspaceCommutator_eq_bot_iff ρ _ _).mpr
    (natural_moved_centralized ρ seed he
      (commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne d.isComponent d.distinct))))

/-- Choose the larger field degree, with a proper seed and the full second-component record. -/
theorem exists_ordered_components [Finite G] [Module.Finite (ZMod 2) V]
    {A L : Subgroup G} (seed : NaturalSeed ρ A L)
    (hL : IsComponent G L) (hLA : ⁅L, A⁆ = L) (d : SecondComponent ρ A L) :
    ∃ (J : Subgroup G) (s : NaturalSeed ρ A J) (e : SecondComponent ρ A J),
      IsComponent G J ∧ ⁅J,A⁆ = J ∧ s.space.toSubmodule < moved ρ J ∧
        e.seed.field.degree ≤ s.field.degree := by
  rcases le_total d.seed.field.degree seed.field.degree with h | h
  · exact ⟨L, seed, d, hL, hLA, d.seed_lt_moved ρ seed hL, h⟩
  · let e := d.swap ρ seed hL hLA
    exact ⟨d.second, d.seed, e, d.isComponent, d.commutator_eq,
      e.seed_lt_moved ρ d.seed d.isComponent, h⟩

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
