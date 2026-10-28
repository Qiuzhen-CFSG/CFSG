module

public import Theory.GroupTheory.PResidual.IndexThreeCommutator
public import Theory.GroupTheory.ElementaryThompsonFrattini

/-!
# Thompson commutators in a literal index-three Sylow overgroup

Suppose the Sylow subgroup has index three. If the image of its elementary
Thompson subgroup has a two-group normalizer under a map with two-group
kernel, the Thompson subgroup cannot lie in the original two-core.
Otherwise it equals the Thompson subgroup of that normal core and is
normal in the whole group, forcing the entire image, and then the group,
to be a two-group. The index-three residual theorem now gives the exact
commutator identity before taking any quotient.

Source application: Aschbacher--Smith 6.1.5, the original S4 overlap
in the remaining symmetric-five row, with the index-three argument E.1.
-/

public section
open Subgroup Stellmacher
namespace Subgroup
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

theorem residual_eq_thompson_commutator_of_index_three
    (T : Sylow 2 G) (hi : (T : Subgroup G).index = 3)
    (q : G →* Q) (hk : IsPGroup 2 q.ker)
    (hn : IsPGroup 2 (normalizer
      ((elementaryAbelianMaxJ (T : Subgroup G)).map q : Set Q))) :
    pResidual 2 G = ⁅pResidual 2 G, elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hTJ : (T : Subgroup G) ≤
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change (elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj t).toMonoidHom = _
    rw [←elementaryAbelianMaxJ_map_equiv]
    exact congrArg elementaryAbelianMaxJ
      (mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht))
  apply (residual_commutator_of_index_three T hi _ hJT hTJ ?_).symm
  intro hJQ
  have hJ : elementaryAbelianMaxJ (pCore 2 G) =
      elementaryAbelianMaxJ (T : Subgroup G) :=
    elementaryAbelianMaxJ_eq_of_intermediate _ _ hJQ
      (pCore_isPGroup.le_sylow_of_normal T)
  have hnorm : (⊤ : Subgroup G) ≤
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    intro g _
    rw [mem_normalizer_iff_map_conj_eq, ←hJ]
    change (elementaryAbelianMaxJ (pCore 2 G)).map (MulAut.conj g).toMonoidHom = _
    rw [←elementaryAbelianMaxJ_map_equiv]
    exact congrArg elementaryAbelianMaxJ
      ((normal_iff_map_conj_eq.mp (inferInstance : (pCore 2 G).Normal)) g)
  have him : q.range ≤ normalizer
      ((elementaryAbelianMaxJ (T : Subgroup G)).map q : Set Q) := by
    rw [MonoidHom.range_eq_map]
    exact (map_mono hnorm).trans (le_normalizer_map q)
  have hg : IsPGroup 2 G := by
    have hp := (hn.to_le him).comap_of_ker_isPGroup q hk
    rw [MonoidHom.comap_range_self] at hp
    exact hp.of_equiv topEquiv
  have ht : (T : Subgroup G) = ⊤ :=
    (T.is_maximal' (hg.to_subgroup ⊤) le_top).symm
  rw [ht,index_top] at hi
  omega

end Subgroup
