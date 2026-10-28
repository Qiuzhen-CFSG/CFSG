module
public import Glauberman.Theorem4_2
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# Normalizers of the all-abelian Baumann subgroup

For the ordinary all-abelian Thompson subgroup J(P), the subgroup
C_P(Ω₁(Z(J(P)))) is invariant under the ambient normalizer of P. This follows
by transporting normalization successively through J, central omega, and
centralizers. No elementary restriction is imposed on the Thompson family.

Source application: Meierfrankenfeld–Stellmacher (1993), (5.1), printed p.913.
-/

@[expose] public section
open Subgroup
namespace Glauberman
variable {G : Type*} [Group G]
noncomputable def baumannSubgroup (P : Subgroup G) : Subgroup G :=
  P ⊓ centralizer (omegaCenterIn (thompsonSubgroup P) : Set G)
theorem normalizer_le_normalizer_baumannSubgroup (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer (baumannSubgroup P : Set G) := by
  have h := (normalizer_le_normalizer_of_thompsonSubgroup P).trans
    ((normalizer_le_normalizer_omegaCenterIn (thompsonSubgroup P)).trans
      (normalizer_le_normalizer_centralizer _))
  exact (le_inf le_rfl h).trans inf_normalizer_le_normalizer_inf
end Glauberman

