module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Action
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.ModelGeometry
public import Theory.GroupTheory.CyclicQuotientInvolutionTransfer

/-!
# The action and transfer boundaries of the PGL₂ shadow exclusion

`Action` connects the actual conjugation by r to projective matrix conjugation
and transports pair generation to the opening R₀ = 1 argument. The transfer
theorem below rules out a normal subgroup D of T with cyclic quotient omitting
the entire G-class of z. Its two specializations retain the index-two and
cyclic-four endings of the source proof.

The intrinsic PGL₂/S₆ pair calculations, weak closure of z, symmetry with L′,
and E₈ transvection argument must still construct these transfer inputs.
Consequently this module does not yet assert Lemma 16.4.6.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.4.6, printed pp.1184–1186, particularly the two transfer
contradictions on p.1186.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow

open Subgroup

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- The common transfer contradiction, applied to the actual central involution z. -/
theorem cyclic_quotient_contradiction (hnonab : ¬ IsMulCommutative G)
    (h : IntersectionSetup T z L g R) (D : Subgroup T) [D.Normal]
    [IsCyclic (T ⧸ D)]
    (havoid : ∀ x : T, x ∈ D → ¬ IsConj z (x : G)) : False := by
  obtain ⟨x, hxz, hxD⟩ := T.exists_isConj_mem_of_cyclic_quotient_of_simple
    hnonab D ⟨z, h.mem_sylow⟩
      ((Subgroup.orderOf_coe (⟨z, h.mem_sylow⟩ : (T : Subgroup G))).symm.trans h.involution)
  exact havoid x hxD hxz

/-- The PGL₂ ending: D has index two in T and contains no conjugate of z. -/
theorem index_two_contradiction (hnonab : ¬ IsMulCommutative G)
    (h : IntersectionSetup T z L g R) (D : Subgroup T) (hindex : D.index = 2)
    (havoid : ∀ x : T, x ∈ D → ¬ IsConj z (x : G)) : False := by
  let : D.Normal := D.normal_of_index_eq_two hindex
  let : IsCyclic (T ⧸ D) := isCyclic_of_prime_card hindex
  exact cyclic_quotient_contradiction hnonab h D havoid

/-- The Aut(A₆) ending retains the genuine cyclic-four quotient. -/
theorem cyclic_four_contradiction (hnonab : ¬ IsMulCommutative G)
    (h : IntersectionSetup T z L g R) (D : Subgroup T) [D.Normal]
    (e : (T ⧸ D) ≃* Multiplicative (ZMod 4))
    (havoid : ∀ x : T, x ∈ D → ¬ IsConj z (x : G)) : False := by
  let : IsCyclic (T ⧸ D) := isCyclic_of_surjective e.symm e.symm.surjective
  exact cyclic_quotient_contradiction hnonab h D havoid

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow
