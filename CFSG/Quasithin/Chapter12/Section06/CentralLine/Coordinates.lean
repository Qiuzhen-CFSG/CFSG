module

public import CFSG.Quasithin.Chapter12.Section06.CentralLine.Transport
public import Theory.Representation.BinaryPermutationAlternatingActions

/-!
# The marked eight-point modules in the central-line argument

Weight four is defined on actual binary coordinates. On the six-dimensional
natural module it means admitting a weight-four lift in the even-weight core.
Linear markings of the original V transport the intrinsic subspace bound to
its actual conjugate intersections, giving r ≥ 4 in the seven-dimensional
case and r ≥ 3 in the six-dimensional case.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 12.6.20(1,3), printed pp.828–829. The intrinsic weight-four subspace
bound is an explicit input owned by the Section06.Permutation development;
fusion and centralizer containment are earlier source inputs.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter12.Section06.CentralLine
open Subgroup ChapterE BinaryPermutation
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- Literal weight four in the seven-dimensional even-weight core. -/
def coreWeightFour (v : core (Fin 8)) : Prop :=
  Fintype.card {i : Fin 8 // v.val i ≠ 0} = 4

/-- The weight-four class in the six-dimensional quotient by constants. -/
def naturalWeightFour (v : natural (Fin 8)) : Prop :=
  ∃ u : core (Fin 8), coreToNatural (Fin 8) u = v ∧ coreWeightFour u

/-- The coordinate predicate on the original ambient subgroup. -/
def markedVectors {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    {V : Subgroup G} [IsElementaryAbelian 2 V]
    (e : Additive V ≃ₗ[ZMod 2] E) (P : E → Prop) : Set G :=
  {v | ∃ hv : v ∈ V, P (e (Additive.ofMul ⟨v, hv⟩))}

variable [Finite G]

/-- A subspace bound in a marked module bounds the binary rank of the
original subgroup, using its inclusion and the specified linear equivalence. -/
theorem rank_le_of_marked_vectors
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    {V U : Subgroup G} [IsElementaryAbelian 2 V]
    (e : Additive V ≃ₗ[ZMod 2] E) (P : E → Prop) {k : ℕ}
    (hbound : ∀ X : Submodule (ZMod 2) E,
      (∀ x ∈ X, x ≠ 0 → P x) → Module.finrank (ZMod 2) X ≤ k)
    (hUV : U ≤ V)
    (hU : ∀ u ∈ U, u ≠ 1 → u ∈ markedVectors e P) :
    Nat.log 2 (Nat.card U) ≤ k := by
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUV
  let f : Additive U →ₗ[ZMod 2] E := e.toLinearMap.comp
    ((Subgroup.inclusion hUV).toAdditive.toZModLinearMap 2)
  have hf : Function.Injective f := fun x y h =>
    Subgroup.inclusion_injective hUV (e.injective h)
  have hr := hbound f.range (by
    rintro _ ⟨u, rfl⟩ hu
    have hu1 : (u.toMul : G) ≠ 1 := by
      intro he
      have hu0 : u = 0 := Subtype.ext he
      exact hu (hu0 ▸ f.map_zero)
    obtain ⟨hv, hp⟩ := hU u.toMul u.toMul.property hu1
    exact hp)
  rw [LinearMap.finrank_range_of_inj hf] at hr
  have hc : Nat.card U = 2 ^ Module.finrank (ZMod 2) (Additive U) := by
    simpa only [Nat.card_zmod, Nat.card_congr (Additive.toMul : Additive U ≃ U)] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U))
  rwa [hc, Nat.log_pow (by decide)]

/-- Lemma 12.6.20(1,3) on the actual seven-dimensional source module.
The exceptional set is fixed by the marking; it is not a group-family tag. -/
theorem core_intersections_and_globalR
    {L V M : Subgroup G} [IsElementaryAbelian 2 V]
    (e : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hbound : ∀ X : Submodule (ZMod 2) (core (Fin 8)),
      (∀ x ∈ X, x ≠ 0 → coreWeightFour x) → Module.finrank (ZMod 2) X ≤ 3)
    (hL : L ≤ normalizer (V : Set G)) (hf : ControlsElementFusion L V)
    (hTI : HasTIConjugatesIn V M)
    (hC : ∀ v ∈ V, v ≠ 1 → v ∉ markedVectors e coreWeightFour →
      centralizer ({v} : Set G) ≤ M) :
    (∀ g ∉ normalizer (V : Set G),
      (∀ v ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom,
        v ≠ 1 → v ∈ markedVectors e coreWeightFour) ∧
      Nat.log 2 (Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) ≤ 3) ∧
      4 ≤ globalR V := by
  have hi g (hg : g ∉ normalizer (V : Set G)) :=
    intersection_mem_of_centralizers hL hf hTI hC hg
  have hr g (hg : g ∉ normalizer (V : Set G)) :=
    rank_le_of_marked_vectors e coreWeightFour hbound inf_le_left (hi g hg)
  refine ⟨fun g hg => ⟨hi g hg, hr g hg⟩, ?_⟩
  have hd : Nat.log 2 (Nat.card V) = 7 := by
    have hc : Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
      simpa only [Nat.card_zmod, Nat.card_congr (Additive.toMul : Additive V ≃ V)] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V))
    rw [hc, e.finrank_eq, finrank_core, Fintype.card_fin, Nat.log_pow (by decide)]
  simpa using globalR_lower_bound (d := 7) (k := 3) (by omega) hr

/-- The same argument on the actual six-dimensional quotient module. -/
theorem natural_intersections_and_globalR
    {L V M : Subgroup G} [IsElementaryAbelian 2 V]
    (e : Additive V ≃ₗ[ZMod 2] natural (Fin 8))
    (hbound : ∀ X : Submodule (ZMod 2) (natural (Fin 8)),
      (∀ x ∈ X, x ≠ 0 → naturalWeightFour x) → Module.finrank (ZMod 2) X ≤ 3)
    (hL : L ≤ normalizer (V : Set G)) (hf : ControlsElementFusion L V)
    (hTI : HasTIConjugatesIn V M)
    (hC : ∀ v ∈ V, v ≠ 1 → v ∉ markedVectors e naturalWeightFour →
      centralizer ({v} : Set G) ≤ M) :
    (∀ g ∉ normalizer (V : Set G),
      (∀ v ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom,
        v ≠ 1 → v ∈ markedVectors e naturalWeightFour) ∧
      Nat.log 2 (Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) ≤ 3) ∧
      3 ≤ globalR V := by
  have hi g (hg : g ∉ normalizer (V : Set G)) :=
    intersection_mem_of_centralizers hL hf hTI hC hg
  have hr g (hg : g ∉ normalizer (V : Set G)) :=
    rank_le_of_marked_vectors e naturalWeightFour hbound inf_le_left (hi g hg)
  refine ⟨fun g hg => ⟨hi g hg, hr g hg⟩, ?_⟩
  have hd : Nat.log 2 (Nat.card V) = 6 := by
    have hc : Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
      simpa only [Nat.card_zmod, Nat.card_congr (Additive.toMul : Additive V ≃ V)] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V))
    rw [hc, e.finrank_eq, finrank_natural_even _ (by decide),
      Fintype.card_fin, Nat.log_pow (by decide)]
  simpa using globalR_lower_bound (d := 6) (k := 3) (by omega) hr

end CFSG.Quasithin.Chapter12.Section06.CentralLine
