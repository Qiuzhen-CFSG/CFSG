module
public import Stellmacher.ElementaryAbelianMaxJ
public import Stellmacher.ElementaryAbelianMaxJWeakClosure
public import Theory.GroupTheory.WeakClosureNormalizer

/-!
# Intermediate subgroups between two maximal elementary factors

An intermediate subgroup containing one of precisely two maximum elementary
subgroups has that factor as its elementary Thompson subgroup unless it is
their join. This turns normalization of an intermediate span and a supplement
into normalization of the join. Weak closure then identifies conjugate
elementary Thompson subgroups.

Source application: Aschbacher–Smith, original 2.4.21, printed p.536.
-/

public section
open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Between one of two maximum elementary factors and their join, the
proper intermediate subgroup has precisely that factor as its Thompson group. -/
theorem maxJ_eq_left_of_proper_interval
    (P U V X : Subgroup G)
    (hpair : elementaryAbelianMaxSubgroups P = {U,V})
    (hgen : U ⊔ V = P) (hUX : U ≤ X) (hXP : X < P) :
    elementaryAbelianMaxJ X = U := by
  have hU : U ∈ elementaryAbelianMaxSubgroups P := by rw [hpair]; exact Set.mem_insert _ _
  have hUXmax : U ∈ elementaryAbelianMaxSubgroups X :=
    ⟨hUX,hU.2.1,fun W hWX hW => hU.2.2 W (hWX.trans hXP.le) hW⟩
  apply le_antisymm _ (le_sSup hUXmax)
  apply sSup_le
  intro W hW
  have hWP : W ∈ elementaryAbelianMaxSubgroups P :=
    ⟨hW.1.trans hXP.le,hW.2.1,fun B hBP hB =>
      (hU.2.2 B hBP hB).trans (hW.2.2 U hUX hU.2.1)⟩
  rw [hpair,Set.mem_insert_iff,Set.mem_singleton_iff] at hWP
  rcases hWP with rfl | rfl
  · exact le_rfl
  · exact False.elim (hXP.not_ge (hgen ▸ sup_le hUX hW.1))

omit [Finite G] in
/-- A subgroup normalizing a span between one elementary factor and the
whole pair also normalizes the overgroup when it preserves a supplement. -/
theorem normalizes_pair_of_normalizes_intermediate
    (P U V X D Y : Subgroup G)
    (hpair : elementaryAbelianMaxSubgroups P = {U,V})
    (hgen : U ⊔ V = P) (hUX : U ≤ X) (hXP : X ≤ P)
    (hYX : Y ≤ normalizer (X : Set G))
    (hYD : Y ≤ normalizer (D : Set G)) (hDU : D ⊔ U = P) :
    Y ≤ normalizer (P : Set G) := by
  by_cases he : X=P
  · exact he ▸ hYX
  · have hJU := maxJ_eq_left_of_proper_interval P U V X hpair hgen hUX
      (lt_of_le_of_ne hXP he)
    have hYU : Y ≤ normalizer (U : Set G) := by
      intro y hy
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [←hJU]
      change (elementaryAbelianMaxJ X).map (MulAut.conj y).toMonoidHom = elementaryAbelianMaxJ X
      rw [←elementaryAbelianMaxJ_map_equiv]
      exact congrArg elementaryAbelianMaxJ (mem_normalizer_iff_map_conj_eq.mp (hYX hy))
    rw [←hDU]
    exact (le_inf hYD hYU).trans (D.normalizer_inf_normalizer_le_normalizer_sup U)

/-- A conjugate elementary Thompson subgroup normalized by the original
one is equal to it. -/
theorem maxJ_conjugate_eq_of_normalizes (T : Sylow 2 G) (g : G)
    (h : elementaryAbelianMaxJ (T : Subgroup G) ≤
      normalizer ((elementaryAbelianMaxJ (T : Subgroup G)).map
        (MulAut.conj g).toMonoidHom : Set G)) :
    (elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom =
      elementaryAbelianMaxJ (T : Subgroup G) := by
  let R := elementaryAbelianMaxJ (T : Subgroup G)
  let P : Sylow 2 G := T.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have hRP : R.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) :=
    map_mono (sSup_le fun _ hA => hA.1)
  have hJ : elementaryAbelianMaxJ (P : Subgroup G) = R.map (MulAut.conj g).toMonoidHom :=
    elementaryAbelianMaxJ_map_equiv _ _
  have hinv : (R.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = R := by
    rw [map_map]
    have hc : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
      ext a
      simp only [MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply, MulAut.conj_apply, inv_inv, MonoidHom.id_apply]
      group
    rw [hc,map_id]
  have he := P.conjugate_eq_of_le_normalizer_of_weakly_closed
    (R.map (MulAut.conj g).toMonoidHom) hRP (by
      intro x hx
      rw [←hJ] at hx ⊢
      exact elementaryAbelianMaxJ_map_eq_of_le _ _ hx) g⁻¹ (by rw [hinv]; exact h)
  rw [hinv] at he
  exact he.symm
end Stellmacher
