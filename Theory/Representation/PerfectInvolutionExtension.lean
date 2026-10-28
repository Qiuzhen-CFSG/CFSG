module
public import Theory.Representation.NormalConstituentDisplacement
public import Theory.Representation.Clifford
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect components with a small-displacement generator

A perfect group has trivial binary actions in dimension at most two, since
its permutation image lies in the solvable group S₄. In an irreducible
representation, every constituent of a nontrivial normal perfect subgroup
therefore has degree at least three. An additional generator of displacement
at most two preserves each constituent; if it and the subgroup generate the
whole group, restriction is irreducible.

Source: the Clifford restriction implicit in Aschbacher–Smith 13.5.21,
printed p.924, before applying B.4.2 and B.4.5 to K*V*.
-/
public section
open Subgroup
namespace Representation.PerfectInvolutionExtension
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

section Small
variable [Group.IsPerfect G]
/-- A perfect group acts trivially on a binary space of dimension at most two. -/
theorem small_action_trivial (ρ : Representation (ZMod 2) G V)
    (hdim : Module.finrank (ZMod 2) V ≤ 2) (g : G) (v : V) : ρ g v = v := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Fintype V := Fintype.ofFinite V
  have hc : Fintype.card V ≤ Fintype.card (Fin 4) := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) hdim
  let e : V ↪ Fin 4 := Classical.choice (Function.Embedding.nonempty_of_card_le hc)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm V) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  let f : G →* Equiv.Perm V := {
    toFun a := {
      toFun := ρ a
      invFun := ρ a⁻¹
      left_inv := by
        intro w
        simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply]
      right_inv := by
        intro w
        simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply] }
    map_one' := by ext w; simp
    map_mul' := by intro a b; ext w; simp }
  let := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have hf : f g = 1 := congrArg Subtype.val
    (Subsingleton.elim (f.rangeRestrict g) 1)
  exact congrArg (fun a : Equiv.Perm V => a v) hf

end Small

/-- Nontrivial normal perfect constituents have binary degree at least three. -/
theorem constituent_dimension (ρ : Representation (ZMod 2) G V)
    (hρ : ρ.IsIrreducible) (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (hn : ¬ K ≤ ρ.ker)
    (J : Subrepresentation (ρ.comp K.subtype)) (hJ : J.toRepresentation.IsIrreducible) :
    3 ≤ Module.finrank (ZMod 2) J.toSubmodule := by
  by_contra hd
  have hj (k : K) (w : J.toSubmodule) : ρ k w = w :=
    congrArg Subtype.val (small_action_trivial J.toRepresentation (by omega) k w)
  let F : Subrepresentation ρ := {
    toSubmodule := Representation.invariants (ρ.comp K.subtype)
    apply_mem_toSubmodule := Representation.le_comap_invariants ρ K }
  have hJF : J.toSubmodule ≤ F.toSubmodule := fun w hw k => hj k ⟨w,hw⟩
  have hF : F ≠ ⊥ := by
    intro he
    have hb : J.toSubmodule = ⊥ := le_bot_iff.mp (by
      change J.toSubmodule ≤ (⊥ : Subrepresentation ρ).toSubmodule
      exact he ▸ hJF)
    exact ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).ne_bot
      (Subrepresentation.toSubmodule_injective hb)
  let := hρ
  have ht : F = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top F).resolve_left hF
  apply hn
  intro k hk
  apply LinearMap.ext
  intro w
  have hw : w ∈ F.toSubmodule := by rw [ht]; trivial
  exact hw ⟨k,hk⟩

/-- A small-displacement generator leaves restriction to the perfect component irreducible. -/
theorem restriction_irreducible (ρ : Representation (ZMod 2) G V)
    (hρ : ρ.IsIrreducible) (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (hn : ¬ K ≤ ρ.ker) (v : G) (hgen : K ⊔ zpowers v = ⊤)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ v - 1)) ≤ 2) :
    IsIrreducible (ρ.comp K.subtype) := by
  let := hρ
  let := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨J,hJ⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp K.subtype)
  have hi : J.toSubmodule.map (ρ v) = J.toSubmodule :=
    Representation.map_constituent_eq_self_of_displacement_lt ρ K v J hJ
      (lt_of_le_of_lt hr (by have := constituent_dimension ρ hρ K hn J hJ; omega))
  have hK : K ≤ BinaryOffender.subspaceStabilizer ρ J.toSubmodule :=
    BinaryOffender.le_subspaceStabilizer ρ J.toSubmodule
      (fun k hk w hw => J.apply_mem_toSubmodule ⟨k,hk⟩ hw)
  have hv : v ∈ BinaryOffender.subspaceStabilizer ρ J.toSubmodule := by
    intro w
    constructor
    · intro hw
      obtain ⟨x,hx,he⟩ := (hi.ge hw)
      exact (ρ.apply_bijective v).injective he ▸ hx
    · intro hw
      exact hi.le (Submodule.mem_map_of_mem hw)
  have hall : ⊤ ≤ BinaryOffender.subspaceStabilizer ρ J.toSubmodule :=
    hgen ▸ sup_le hK (zpowers_le.mpr hv)
  let A : Subrepresentation ρ := {
    toSubmodule := J.toSubmodule
    apply_mem_toSubmodule g w hw := (hall (mem_top g) w).mpr hw }
  have hA : A ≠ ⊥ := fun he =>
    ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).ne_bot
      (Subrepresentation.toSubmodule_injective (congrArg (fun B : Subrepresentation ρ => B.toSubmodule) he))
  have ht : A = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top A).resolve_left hA
  have hJtop : J = ⊤ :=
    Subrepresentation.toSubmodule_injective (congrArg (fun B : Subrepresentation ρ => B.toSubmodule) ht)
  exact isSimpleOrder_iff_isAtom_top.mpr
    (hJtop ▸ (Subrepresentation.irreducible_iff_isAtom J).mp hJ)
end Representation.PerfectInvolutionExtension
