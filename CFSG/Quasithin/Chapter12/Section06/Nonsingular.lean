module

public import CFSG.Quasithin.Chapter12.Section06.Setup
public import Theory.GroupTheory.TwoPerfectElementaryIndexTwo

/-!
# Terminal normalizer contradiction for nonsingular centralizers

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Theorem 12.6.2, printed p.828. Once the A₇-block analysis and the degree-seven
and degree-eight cohomology calculations give elementary Q of index two
in R_v = O₂(K_v S), the nontrivial commutator [R_v,r] = ⟨v⟩ rules out
an elementary R_v. Two-perfectness of K_v then forces K_v to normalize Q,
contradicting K_v not contained in M.

This proves the last contradiction on the literal source subgroups. The
component, block and cohomological splitting inputs are explicit. The
source containment theorem is not asserted before those inputs are proved.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]

/-- The final contradiction from the actual two-core and commutator
identities. The source's Q=V and Q≅E₂₅₆ alternatives both supply hQ.
No D₈ × E₆₄ recognition or assumed enumeration is required. -/
theorem nonsingular_terminal_contradiction
    (T : Sylow 2 G) (L V K S : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : L ≤ normalizer (V : Set G)) (D : OrthogonalMarking L V hn)
    (v : V) (hv : D.Nonsingular v)
    (hK : IsPPerfect 2 K) (hKnot : ¬ K ≤ M L)
    (hcore : Rv T L (v : G) = (K ⊔ S).pCoreIn 2)
    (hQ : IsElementaryAbelian 2 (Q T L))
    (hQR : Q T L ≤ Rv T L (v : G))
    (hindex : (Q T L).relIndex (Rv T L (v : G)) = 2)
    (hnormalizer : normalizer (Q T L : Set G) ≤ M L)
    (r : G) (hr : r ∈ Rv T L (v : G))
    (hcomm : ⁅Rv T L (v : G), zpowers r⁆ = zpowers (v : G)) : False := by
  have hnR : K ≤ normalizer (Rv T L (v : G) : Set G) := by
    rw [hcore]
    apply (le_sup_left : K ≤ K ⊔ S).trans
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 (K ⊔ S : Subgroup G)).le_normalizer_map (K ⊔ S).subtype
  have hnon : ¬ IsElementaryAbelian 2 (Rv T L (v : G)) := by
    intro he
    have hz : ⁅Rv T L (v : G), zpowers r⁆ = ⊥ := by
      apply bot_unique
      exact (commutator_mono le_rfl (zpowers_le.mpr hr)).trans_eq
        (commutator_self_eq_bot_iff.mpr he.toIsMulCommutative)
    have hv1 : (v : G) = 1 := zpowers_eq_bot.mp (hcomm.symm.trans hz)
    exact nonsingular_ne_one D hv (Subtype.ext hv1)
  exact hKnot ((twoPerfect_le_normalizer_elementary_index_two K
    (Rv T L (v : G)) (Q T L) hK hnR hQR hQ hindex hnon).trans hnormalizer)

end CFSG.Quasithin.Chapter12.Section06
