module

public import Theory.SpecificGroups.BinaryLinear.NaturalDualFlag
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.SubspaceQuotient
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# The middle-node obstruction on the natural-plus-dual module

The middle-node minimal parabolic in GL₄(2) stabilizes an incident line and
hyperplane. The existing flag-radical calculation gives a fixed nonzero vector
in every nonzero invariant binary subspace of the natural-plus-dual module.
In a two-space, a fixed vector forces every displacement into its span: the
one-dimensional quotient has trivial binary action. Therefore such a two-space
cannot equal its commutator with any subgroup of this marked parabolic.

This excludes the eight-dimensional alternative using V̂₃, with binary rank
two and V̂₃ = [V̂₃,L₁]. It is independent of any assertion about module dimension
alone and transports through actual equivariant linear equivalences.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.25,
printed pp.959–960, PDF pp.976–977.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient
open Representation Representation.BinaryOffender BinaryLinear

private theorem action_eq_of_dim_one
    {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (τ : Representation (ZMod 2) H E)
    (hdim : Module.finrank (ZMod 2) E = 1) (g : H) (v : E) : τ g v = v := by
  obtain ⟨a, ha, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (τ g)
  have hcases : a = 0 ∨ a = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
  rcases hcases with hzero | hone
  · have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ZMod 2) (M := E) (by omega)
    obtain ⟨w, hw⟩ := exists_ne (0 : E)
    have h := congrArg (fun f : E →ₗ[ZMod 2] E => f (τ g⁻¹ w)) ha
    simp only [hzero, zero_smul, LinearMap.zero_apply] at h
    have hh : τ g (τ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    exact (hw (hh.symm.trans h)).elim
  · simpa [hone] using LinearMap.congr_fun ha v

private theorem displacement_mem_fixed_line
    {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (τ : Representation (ZMod 2) H E)
    (hdim : Module.finrank (ZMod 2) E = 2) (v : E) (hv : v ≠ 0)
    (hfix : ∀ g, τ g v = v) (g : H) (w : E) :
    τ g w - w ∈ Submodule.span (ZMod 2) {v} := by
  let S : Subrepresentation τ := {
    toSubmodule := Submodule.span (ZMod 2) {v}
    apply_mem_toSubmodule g := by
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul, hfix]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v) }
  have hs : Module.finrank (ZMod 2) S.toSubmodule = 1 :=
    finrank_span_singleton hv
  have hq : Module.finrank (ZMod 2) (E ⧸ S.toSubmodule) = 1 := by
    have := S.toSubmodule.finrank_quotient_add_finrank
    omega
  exact (Submodule.Quotient.eq _).mp
    (action_eq_of_dim_one S.quotientRepresentation hq g (S.toSubmodule.mkQ w))

/-- The actual natural-plus-contragredient representation. -/
def naturalDualAction {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    Representation (ZMod 2) (BinaryLinear.GL V) (V × Module.Dual (ZMod 2) V) where
  toFun g := (NaturalDualFlag.action g).toLinearMap
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by rw [map_mul]; rfl

/-- An invariant binary two-space for the marked middle parabolic cannot be
its commutator with a subgroup of that parabolic. The flag is arbitrary. -/
theorem middle_flag_no_commutator_plane
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (A F : Submodule (ZMod 2) V) (hAF : A ≤ F)
    (hA : Module.finrank (ZMod 2) A = 1)
    (hF : Module.finrank (ZMod 2) F + 1 = Module.finrank (ZMod 2) V)
    (W : Submodule (ZMod 2) (V × Module.Dual (ZMod 2) V))
    (hdim : Module.finrank (ZMod 2) W = 2)
    (hstable : ∀ g ∈ parabolic A ⊓ parabolic F, ∀ w ∈ W, naturalDualAction g w ∈ W)
    (L : Subgroup (BinaryLinear.GL V)) (hL : L ≤ parabolic A ⊓ parabolic F)
    (hcomm : subspaceCommutator naturalDualAction W L = W) : False := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  have hc : 2 ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
    decide
  obtain ⟨v, hv, hv0, hfix⟩ := NaturalDualFlag.exists_fixed hAF hA hF W hc hstable
  let P := parabolic A ⊓ parabolic F
  let S : Subrepresentation (naturalDualAction.comp P.subtype) := {
    toSubmodule := W
    apply_mem_toSubmodule g := hstable g g.property }
  let v₀ : W := ⟨v, hv⟩
  have hv₀ : v₀ ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hspan : W ≤ Submodule.span (ZMod 2) {v} := by
    rw [← hcomm]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, w, hw, rfl⟩
    have h := displacement_mem_fixed_line S.toRepresentation hdim v₀ hv₀
      (fun (g : P) => Subtype.ext (hfix g g.property)) (⟨g, hL hg⟩ : P) ⟨w, hw⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    exact Submodule.mem_span_singleton.mpr ⟨a, congrArg Subtype.val ha⟩
  have hn := Submodule.finrank_mono hspan
  rw [hdim, finrank_span_singleton hv0] at hn
  omega

/-- Equivariant transport of the flag obstruction. Apply this to the restricted
K*-action; the homomorphism is the specified GL₄(2) marking of K*. -/
theorem not_naturalDual_of_marked_plane
    {K E V : Type*} [Group K] [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (τ : Representation (ZMod 2) K E) (φ : K →* BinaryLinear.GL V)
    (P L : Subgroup K) (hLP : L ≤ P)
    (A F : Submodule (ZMod 2) V) (hAF : A ≤ F)
    (hA : Module.finrank (ZMod 2) A = 1)
    (hF : Module.finrank (ZMod 2) F + 1 = Module.finrank (ZMod 2) V)
    (hP : P.map φ = parabolic A ⊓ parabolic F)
    (S : Submodule (ZMod 2) E) (hdim : Module.finrank (ZMod 2) S = 2)
    (hstable : ∀ g ∈ P, ∀ v ∈ S, τ g v ∈ S)
    (hcomm : subspaceCommutator τ S L = S) :
    ¬ ∃ e : E ≃ₗ[ZMod 2] (V × Module.Dual (ZMod 2) V),
      ∀ g v, e (τ g v) = naturalDualAction (φ g) (e v) := by
  rintro ⟨e, he⟩
  apply middle_flag_no_commutator_plane A F hAF hA hF
    (S.map e.toLinearMap) ((Submodule.equivMapOfInjective e.toLinearMap e.injective S).finrank_eq.symm.trans hdim)
    ?_ (L.map φ) ?_ ?_
  · intro g hg v hv
    rw [← hP] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨τ k w, hstable k hk w hw, he k w⟩
  · rw [← hP]
    exact Subgroup.map_mono hLP
  · have hmap : subspaceCommutator naturalDualAction (S.map e.toLinearMap) (L.map φ) =
        (subspaceCommutator τ S L).map e.toLinearMap := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro _ ⟨g, hg, _, ⟨v, hv, rfl⟩, rfl⟩
        obtain ⟨k, hk, rfl⟩ := hg
        exact ⟨τ k v - v, Submodule.subset_span ⟨k, hk, v, hv, rfl⟩,
          (he k v).symm ▸ map_sub _ _ _⟩
      · rw [Submodule.map_le_iff_le_comap]
        apply Submodule.span_le.mpr
        rintro _ ⟨k, hk, v, hv, rfl⟩
        change e.toLinearMap (τ k v - v) ∈
          subspaceCommutator naturalDualAction (S.map e.toLinearMap) (L.map φ)
        have hh : e.toLinearMap (τ k v - v) =
            naturalDualAction (φ k) (e v) - e v := by
          calc
            e.toLinearMap (τ k v - v) = e (τ k v) - e v := by
              change e (τ k v - v) = _
              rw [map_sub]
            _ = naturalDualAction (φ k) (e v) - e v := congrArg (fun z => z - e v) (he k v)
        rw [hh]
        exact Submodule.subset_span ⟨φ k, Subgroup.mem_map_of_mem φ hk, e v,
          Submodule.mem_map_of_mem hv, rfl⟩
    rw [hmap, hcomm]


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient
