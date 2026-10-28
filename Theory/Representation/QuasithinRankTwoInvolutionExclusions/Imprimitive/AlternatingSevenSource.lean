module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.AlternatingSeven
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.SwappedCoordinates
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The S₇ exclusion on its source summands

The input is an actual group isomorphism to S₇, an invariant A₇ four-space P,
and the direct sum V = P ⊕ xP for an involution x in the elementary abelian
subgroup X. The decomposition forces x to be odd, and supplies its swapping
coordinates. Simplicity
makes every action of A₇ either faithful or trivial; the concrete component
rank theorem therefore gives rank zero or two on P. For an even element of X,
commutation with x makes the two blocks agree. An odd element exchanges them
and moves four dimensions. No classification of P up to module isomorphism,
extra faithfulness premise, or rank bound is assumed.

This proves the rank exclusion in Aschbacher–Smith G.11.2(8), printed
p.364/PDF p.375, used in 6.2.19, printed p.691/PDF p.708. The totally isotropic
condition in the source is not needed for this stronger linear calculation.
-/

public section

namespace Representation.RankTwo.Imprimitive.AlternatingSeven

/-- Simplicity covers arbitrary four-dimensional A₇ actions, including a
trivial action; no faithfulness premise is needed for the X calculation. -/
theorem finrank_four_square_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (hd : Module.finrank (ZMod 2) V = 4)
    (a : alternatingGroup (Fin 7)) (ha : a * a = 1) :
    Module.finrank (ZMod 2) (movedSpace σ a) = 0 ∨
      Module.finrank (ZMod 2) (movedSpace σ a) = 2 := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  by_cases h1 : a = 1
  · subst a
    left
    apply Submodule.finrank_eq_zero.mpr
    change LinearMap.range (σ 1 - 1) = ⊥
    rw [map_one, sub_self, LinearMap.range_zero]
  rcases σ.normal_ker.eq_bot_or_eq_top with hk | hk
  · exact Or.inr (finrank_faithful_involution σ (σ.ker_eq_bot_iff.mp hk) hd a
      (orderOf_eq_prime (by simpa [pow_two] using ha) h1))
  · left
    have he : σ a = 1 := show a ∈ σ.ker from hk ▸ Subgroup.mem_top a
    apply Submodule.finrank_eq_zero.mpr
    change LinearMap.range (σ a - 1) = ⊥
    rw [he, sub_self, LinearMap.range_zero]


end Representation.RankTwo.Imprimitive.AlternatingSeven

namespace Representation.RankTwo.Imprimitive

/-- The source case (8) on its actual invariant summand. The second coordinates
are constructed using x; no chosen identification with a particular A₇ module
or extra rank hypothesis is required. -/
theorem alternatingSeven_source_X_not_rankTwo
    {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (e : H ≃* Equiv.Perm (Fin 7))
    (P : Subrepresentation (ρ.comp
      (e.symm.toMonoidHom.comp (alternatingGroup (Fin 7)).subtype)))
    (hd : Module.finrank (ZMod 2) P.toSubmodule = 4)
    (X : Subgroup H) (x : H) (hx : x ∈ X)
    (hxodd : e x ∉ alternatingGroup (Fin 7))
    (hX2 : ∀ g ∈ X, g * g = 1)
    (hXcomm : ∀ g ∈ X, ∀ h ∈ X, Commute g h)
    (hsplit : IsCompl P.toSubmodule (P.toSubmodule.map (ρ x)))
    (g : H) (hg : g ∈ X) :
    Module.finrank (ZMod 2) (movedSpace ρ g) ≠ 2 := by
  let σ := P.toRepresentation
  have hx2 : ρ x * ρ x = 1 := by rw [← map_mul, hX2 x hx, map_one]
  let f := swappedCoordinates (ρ x) hx2 P.toSubmodule hsplit
  have inner_action (b : H) (hb : b ∈ X) (heven : e b ∈ alternatingGroup (Fin 7))
      (v w : P.toSubmodule) :
      ρ b (f (v,w)) = f (σ ⟨e b, heven⟩ v, σ ⟨e b, heven⟩ w) := by
    apply action_swappedCoordinates (ρ x) hx2 P.toSubmodule hsplit
      (ρ b) (σ ⟨e b, heven⟩) ((hXcomm b hb x hx).map ρ)
    intro u
    change ρ b u = ρ (e.symm (e b)) u
    rw [e.symm_apply_apply]
  by_cases heven : e g ∈ alternatingGroup (Fin 7)
  · have ha : (⟨e g, heven⟩ : alternatingGroup (Fin 7)) * ⟨e g, heven⟩ = 1 := by
      apply Subtype.ext
      change e g * e g = 1
      rw [← map_mul, hX2 g hg, map_one]
    have hr := finrank_of_block_coordinates f (ρ g) (σ ⟨e g, heven⟩)
      (inner_action g hg heven)
    rcases AlternatingSeven.finrank_four_square_one σ hd ⟨e g, heven⟩ ha with h | h
    all_goals
      have hr' : Module.finrank (ZMod 2) (movedSpace ρ g) =
          2 * Module.finrank (ZMod 2) (movedSpace σ ⟨e g, heven⟩) := hr
      rw [h] at hr'
      intro hh
      have hbad := hr'.symm.trans hh
      norm_num at hbad
  · have hxsign : (e x).sign = -1 := (Int.units_eq_one_or (e x).sign).resolve_left hxodd
    have hgsign : (e g).sign = -1 := (Int.units_eq_one_or (e g).sign).resolve_left heven
    have hb : x * g ∈ X := X.mul_mem hx hg
    have hbeven : e (x * g) ∈ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, hxsign, hgsign]
      decide
    have hge : g = x * (x * g) := by rw [← mul_assoc, hX2 x hx, one_mul]
    have hact (v w : P.toSubmodule) :
        ρ g (f (v,w)) = f (σ ⟨e (x*g), hbeven⟩ w, σ ⟨e (x*g), hbeven⟩ v) := by
      conv_lhs => rw [hge, map_mul, Module.End.mul_apply, inner_action (x*g) hb hbeven]
      exact swappedCoordinates_swap (ρ x) hx2 P.toSubmodule hsplit _ _
    have hr := finrank_of_exchanging_coordinates f (ρ g)
      (σ ⟨e (x*g), hbeven⟩) (σ ⟨e (x*g), hbeven⟩) hact
      (by rw [← map_mul, hX2 g hg, map_one])
    rw [hd] at hr
    exact fun hh => (by decide : (4 : ℕ) ≠ 2) (hr.symm.trans hh)


/-- Case (8) from the source direct sum alone: since even permutations preserve
P, an involution taking P to its complement must be odd. -/
theorem alternatingSeven_decomposition_X_not_rankTwo
    {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (e : H ≃* Equiv.Perm (Fin 7))
    (P : Subrepresentation (ρ.comp
      (e.symm.toMonoidHom.comp (alternatingGroup (Fin 7)).subtype)))
    (hd : Module.finrank (ZMod 2) P.toSubmodule = 4)
    (X : Subgroup H) (x : H) (hx : x ∈ X)
    (hX2 : ∀ g ∈ X, g * g = 1)
    (hXcomm : ∀ g ∈ X, ∀ h ∈ X, Commute g h)
    (hsplit : IsCompl P.toSubmodule (P.toSubmodule.map (ρ x)))
    (g : H) (hg : g ∈ X) :
    Module.finrank (ZMod 2) (movedSpace ρ g) ≠ 2 := by
  apply alternatingSeven_source_X_not_rankTwo ρ e P hd X x hx ?_ hX2 hXcomm hsplit g hg
  intro heven
  have hzero : P.toSubmodule = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    have hinv : ρ x v ∈ P.toSubmodule := by
      have h := P.apply_mem_toSubmodule ⟨e x, heven⟩ hv
      change ρ (e.symm (e x)) v ∈ P.toSubmodule at h
      rwa [e.symm_apply_apply] at h
    have ht : ρ x v = 0 := hsplit.disjoint.le_bot ⟨hinv, ⟨v,hv,rfl⟩⟩
    have hh := congrArg (ρ x) ht
    change v = 0
    simpa only [← Module.End.mul_apply, ← map_mul, hX2 x hx, map_one,
      Module.End.one_apply, map_zero] using hh
  have hd0 : Module.finrank (ZMod 2) P.toSubmodule = 0 := Submodule.finrank_eq_zero.mpr hzero
  omega

end Representation.RankTwo.Imprimitive