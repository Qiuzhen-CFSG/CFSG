module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Conj

/-!
# Transport into a fixed-point commutator subgroup

If `Q = [Q, ⟨t⟩]` centralizes `w`, an automorphism fixing `t` and `w`
and mapping `Q` into `P` maps it into `[C_P(w), ⟨t⟩]`. This keeps both
commutators as actual ambient subgroup commutators.

Combined with a fixed Sylow conjugator this is the containment step in
GLS, Volume 4, Chapter 2, Proposition 16.5, immediately after choosing the
invariant Sylow subgroup. No Sylow, finiteness, or coprimality assumption
is needed for this algebraic transport step.
-/

namespace Subgroup

public theorem map_le_fixed_commutator_of_full_commutator
    {G : Type*} [Group G] (P Q : Subgroup G) (t w : G) (f : G ≃* G)
    (ht : f t = t) (hw : f w = w) (hQP : Q.map f.toMonoidHom ≤ P)
    (hQw : Q ≤ centralizer ({w} : Set G)) (hQ : ⁅Q, zpowers t⁆ = Q) :
    Q.map f.toMonoidHom ≤ ⁅P ⊓ centralizer ({w} : Set G), zpowers t⁆ := by
  have hfixed : Q.map f.toMonoidHom ≤ centralizer ({w} : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change f y * w = w * f y
    have he := congrArg f (mem_centralizer_singleton_iff.mp (hQw hy))
    simpa only [map_mul, hw] using he
  calc
    Q.map f.toMonoidHom = (⁅Q, zpowers t⁆).map f.toMonoidHom := by rw [hQ]
    _ = ⁅Q.map f.toMonoidHom, zpowers t⁆ := by
      rw [map_commutator, MonoidHom.map_zpowers]
      change ⁅Q.map f.toMonoidHom, zpowers (f t)⁆ = _
      rw [ht]
    _ ≤ ⁅P ⊓ centralizer ({w} : Set G), zpowers t⁆ :=
      commutator_mono (le_inf hQP hfixed) le_rfl

end Subgroup
