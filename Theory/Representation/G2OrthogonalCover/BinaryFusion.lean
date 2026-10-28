module
public import Theory.Representation.G2OrthogonalCover.QuadraticObstruction
public import Mathlib.GroupTheory.PGroup

/-!
# Binary Weyl orbits and Sylow fixed vectors

The scalar radical in the trace-zero seven-space has two elements. Each
natural vector has a unique singular representative, so the singular vectors
form a set of size 64. A two-group preserving the norm fixes a nonzero
singular vector. Natural transitivity then puts every vector outside the
radical into this vector or its translate by the identity.

The norm is preserved by every linear operator fixing the identity and
normalizing the derived action: the difference of the two invariant forms
vanishes on the identity, hence vanishes by the quadratic obstruction.
All actors are the literal derived G₂(2) group.

Source: Aschbacher–Smith, 12.2.16, printed p.800, and I.2.3, p.413.
The octonion model retains the attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Representation Representation.OneCohomology
namespace Atlas.G2.Natural.OrthogonalCover
local notation "F" => ZMod 2
local notation "E" => TraceZero F
local notation "D" => _root_.commutator (Model F)

theorem binary_scalar_iff (x : E) : x ∈ scalarLine F ↔ x = 0 ∨ x = identity F := by
  change x ∈ F ∙ identity F ↔ _
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c,rfl⟩
    fin_cases c
    · exact Or.inl (zero_smul F _)
    · exact Or.inr (one_smul F _)
  · rintro (rfl | rfl)
    · exact ⟨0,zero_smul _ _⟩
    · exact ⟨1,one_smul _ _⟩

theorem binary_mk_eq_iff (x y : E) :
    mk F x = mk F y ↔ x = y ∨ x = y + identity F := by
  rw [← sub_eq_zero, ← map_sub]
  change Submodule.Quotient.mk (x-y) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, binary_scalar_iff, sub_eq_zero]
  exact or_congr Iff.rfl (by rw [sub_eq_iff_eq_add, add_comm])

theorem binary_form_add_identity (x : E) : form F (x + identity F) = form F x + 1 := by
  rw [add_comm x, QuadraticMap.map_add (form F)]
  have hp : (form F).polarBilin (identity F) x = 0 := by
    rw [polar_apply]
    exact (polar_unit F x.val).trans x.property
  rw [form_identity]
  change 1 + form F x + (form F).polarBilin (identity F) x = _
  rw [hp,add_zero,add_comm]

theorem binary_singular_lift_unique {x y : E} (hx : form F x = 0)
    (hy : form F y = 0) (he : mk F x = mk F y) : x = y := by
  rcases (binary_mk_eq_iff x y).mp he with hh | rfl
  · exact hh
  · rw [binary_form_add_identity,hy,zero_add] at hx
    exact (one_ne_zero hx).elim

theorem binary_form_normalized (a : E →ₗ[F] E)
    (ha : a (identity F) = identity F)
    (hn : ∀ g : D, ∃ h : D, ∀ x, a (action F g x) = action F h (a x))
    (x : E) : form F (a x) = form F x := by
  let q := (form F).comp a - form F
  have hq : ∀ g : D, ∀ y, q (action F g y) = q y := by
    intro g y
    obtain ⟨h,hh⟩ := hn g
    change form F (a (action F g y)) - form F (action F g y) = _
    rw [hh, form_invariant, form_invariant]
    rfl
  have hz : q = 0 := by
    by_contra hne
    apply invariantQuadratic_identity_ne_zero q hq hne
    change form F (a (identity F)) - form F (identity F) = 0
    rw [ha,sub_self]
  exact sub_eq_zero.mp (congrArg (fun r : QuadraticForm F E => r x) hz)

theorem binary_orbit_pair {v x : E} (hv : mk F v ≠ 0) (hx : mk F x ≠ 0) :
    ∃ g : D, action F g x = v ∨ action F g x = v + identity F := by
  obtain ⟨g,hg⟩ := derivedAction_transitive F (mk F x) (mk F v) hx hv
  exact ⟨g,(binary_mk_eq_iff _ _).mp hg⟩

theorem binary_exists_fixed_singular {P : Type*} [Group P] (hP : IsPGroup 2 P)
    (σ : Representation F P E)
    (hinv : ∀ t x, form F (σ t x) = form F x) :
    ∃ v : E, v ≠ 0 ∧ form F v = 0 ∧ ∀ t, σ t v = v := by
  let S := {v : E // form F v = 0}
  let π : S → Space F := fun v => mk F v.val
  have hi : Function.Injective π := by
    intro x y he
    exact Subtype.ext (binary_singular_lift_unique x.property y.property he)
  have hs : Function.Surjective π := by
    intro x
    obtain ⟨v,hv,he⟩ := exists_singular_representative x
    exact ⟨⟨v,hv⟩,he⟩
  have hc : Nat.card S = 64 := by
    rw [Nat.card_congr (Equiv.ofBijective π ⟨hi,hs⟩),
      Module.natCard_eq_pow_finrank (K := F),Nat.card_zmod,finrank_space]
    norm_num
  let : MulAction P S := {
    smul t v := ⟨σ t v, (hinv t v).trans v.property⟩
    one_smul v := by apply Subtype.ext; change σ 1 v = v; simp
    mul_smul t s v := by
      apply Subtype.ext
      change σ (t*s) v = σ t (σ s v)
      simp }
  let z : S := ⟨0,map_zero _⟩
  have hz : z ∈ MulAction.fixedPoints P S := by
    intro t
    apply Subtype.ext
    exact map_zero (σ t)
  obtain ⟨v,hv,hv0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point S
    (by rw [hc]; decide) hz
  exact ⟨v,fun he => hv0 (Subtype.ext he.symm),v.property,
    fun t => congrArg Subtype.val (hv t)⟩

end Atlas.G2.Natural.OrthogonalCover
