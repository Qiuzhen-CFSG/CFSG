module

public import Theory.GroupTheory.ElementaryThompsonFrattini
public import Theory.Order.UniqueMaximalOver
public import Mathlib.Data.SetLike.Fintype

/-!
# Thompson generation in a minimal Sylow overgroup

The existing elementary Thompson Frattini theorem reduces generation to
covering J(G). A unique maximal overgroup of the Sylow subgroup contains
every proper overgroup, including the selected Thompson normalizer.
Therefore any subgroup covering J(G) together with the Sylow subgroup
already generates the whole group. This is the placement step following
solvable Thompson factorization in Aschbacher–Smith 14.1.4, p.976.
-/

public section
open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- In a minimal Sylow overgroup, covering the global Thompson subgroup
forces generation, provided the selected Thompson normalizer is proper. -/
theorem sup_sylow_eq_top_of_global_thompson_le (T : Sylow 2 G)
    (hunique : Order.HasUniqueMaximalOver (T : Subgroup G) ⊤)
    (hproper : normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≠ ⊤)
    (X : Subgroup G)
    (hcover : elementaryAbelianMaxJ (⊤ : Subgroup G) ≤ X ⊔ (T : Subgroup G)) :
    X ⊔ (T : Subgroup G) = ⊤ := by
  by_contra hx
  obtain ⟨M, hM, _⟩ := hunique.2
  have hTN : (T : Subgroup G) ≤
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj t).toMonoidHom = _
    rw [← elementaryAbelianMaxJ_map_equiv,
      show (T : Subgroup G).map (MulAut.conj t).toMonoidHom = (T : Subgroup G) from
        mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)]
  have hNM := hunique.le_maximal hM hTN (lt_top_iff_ne_top.mpr hproper)
  have hXM := hunique.le_maximal hM (show (T : Subgroup G) ≤ X ⊔ (T : Subgroup G) from
    le_sup_right) (lt_top_iff_ne_top.mpr hx)
  have htop : (⊤ : Subgroup G) ≤ M := by
    rw [← elementaryAbelianMaxJ_frattini T]
    exact sup_le hNM (hcover.trans hXM)
  exact hM.2.ne (top_unique htop)

end Stellmacher
