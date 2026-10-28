module
public import Stellmacher.ElementaryAbelianMaxPair
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.PairNormalizerIndex
public import Mathlib.GroupTheory.Nilpotent

/-!
# A Thompson pair controls a finite two-overgroup

Suppose R has precisely two maximum elementary subgroups, and the stabilizer
of one of them in a finite two-group P is R. An index-two overgroup M of R
whose Thompson subgroup is still J(R) is self-normalizing in P: its normalizer
permutes the same pair, so cannot be larger than M. The normalizer condition
then gives M=P. This is the two-member-family endgame of C.6.1.

Source: Aschbacher--Smith C.6.1, printed p.165, case (alpha).
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem thompson_normalizer_preserves_maxFamily_pair
    (R Q W : Subgroup G) (hfamily : elementaryAbelianMaxSubgroups R = {Q,W})
    {g : G} (hg : g ∈ normalizer (elementaryAbelianMaxJ R : Set G)) :
    Q.map (MulAut.conj g).toMonoidHom = Q ∨
      Q.map (MulAut.conj g).toMonoidHom = W := by
  have hQ : Q ∈ elementaryAbelianMaxSubgroups (elementaryAbelianMaxJ R) := by
    rw [maxFamily_thompson,hfamily]
    exact Set.mem_insert _ _
  have hm := (maxFamily_map_injective_iff (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective (elementaryAbelianMaxJ R) Q).mpr hQ
  have he : (elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom =
      elementaryAbelianMaxJ R := mem_normalizer_iff_map_conj_eq.mp hg
  rw [he,maxFamily_thompson,hfamily] at hm
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hm

theorem twoGroup_normalizer_index_two_of_maxFamily_pair
    (P R Q W : Subgroup G) (hP : IsPGroup 2 P) (hRP : R < P)
    (hfamily : elementaryAbelianMaxSubgroups R = {Q,W})
    (hcontrol : P ⊓ normalizer (Q : Set G) = R) :
    R.relIndex (P ⊓ normalizer (R : Set G)) = 2 ∧
      ∀ x ∈ P ⊓ normalizer (R : Set G), x ∉ R →
        elementaryAbelianMaxJ R = Q ⊔ Q.map (MulAut.conj x⁻¹).toMonoidHom := by
  let D := P ⊓ normalizer (R : Set G)
  have hRD : R ≤ D := le_inf hRP.le R.le_normalizer
  let : Group.IsNilpotent P := hP.isNilpotent
  have hproper : R.subgroupOf P < ⊤ := lt_top_iff_ne_top.mpr
    (fun he => hRP.not_ge (subgroupOf_eq_top.mp he))
  obtain ⟨x,hxn,hxr⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (R.subgroupOf P) hproper)
  have hxN : (x : G) ∈ normalizer (R : Set G) := by
    rwa [←subgroupOf_normalizer_eq hRP.le] at hxn
  have hmove : Q.map (MulAut.conj (x : G)).toMonoidHom ≠ Q := by
    intro he
    exact hxr (hcontrol ▸ ⟨x.property,mem_normalizer_iff_map_conj_eq.mpr he⟩)
  have hp (g) (hg : g ∈ D) := thompson_normalizer_preserves_maxFamily_pair R Q W hfamily
    (normalizer_le_normalizer_elementaryAbelianMaxJ R hg.2)
  have hi := normalizer_relIndex_eq_two_of_pair D Q W hp x ⟨x.property,hxN⟩ hmove
  have hs : D ⊓ normalizer (Q : Set G) = R := by
    apply le_antisymm
    · exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hcontrol.le
    · exact le_inf hRD (hcontrol ▸ inf_le_right)
  refine ⟨?_,?_⟩
  · change R.relIndex D = 2
    rw [←hs,inf_relIndex_left]
    exact hi
  · intro g hg hgr
    have hm : Q.map (MulAut.conj g⁻¹).toMonoidHom ≠ Q := by
      intro he
      have hn : g⁻¹ ∈ normalizer (Q : Set G) := mem_normalizer_iff_map_conj_eq.mpr he
      have hn' : g ∈ normalizer (Q : Set G) := by
        simpa only [inv_inv] using (normalizer (Q : Set G)).inv_mem hn
      exact hgr (hcontrol ▸ (show g ∈ P ⊓ normalizer (Q : Set G) from ⟨hg.1,hn'⟩))
    have he := (hp g⁻¹ (D.inv_mem hg)).resolve_left hm
    rw [he,elementaryAbelianMaxJ,hfamily,sSup_pair]

theorem twoGroup_eq_of_index_two_thompson_pair
    (P M R Q W : Subgroup G) (hP : IsPGroup 2 P)
    (hRM : R ≤ M) (hMP : M ≤ P) (hi : R.relIndex M = 2)
    (hfamily : elementaryAbelianMaxSubgroups R = {Q,W})
    (hcontrol : P ⊓ normalizer (Q : Set G) = R)
    (hJ : elementaryAbelianMaxJ M = elementaryAbelianMaxJ R) :
    M = P := by
  let D := P ⊓ normalizer (M : Set G)
  have hMD : M ≤ D := le_inf hMP M.le_normalizer
  have hRD : R ≤ D := hRM.trans hMD
  have hRQ : R ≤ normalizer (Q : Set G) := hcontrol ▸ inf_le_right
  have hDN : D ≤ normalizer (elementaryAbelianMaxJ R : Set G) := by
    rw [←hJ]
    exact inf_le_right.trans (normalizer_le_normalizer_elementaryAbelianMaxJ M)
  have hlt : R < M := lt_of_le_of_ne hRM (by
    rintro rfl
    simp only [relIndex_self] at hi
    omega)
  obtain ⟨x,hxM,hxR⟩ := SetLike.exists_of_lt hlt
  have hmove : Q.map (MulAut.conj x).toMonoidHom ≠ Q := by
    intro he
    exact hxR (hcontrol ▸ ⟨hMP hxM,mem_normalizer_iff_map_conj_eq.mpr he⟩)
  have hidx := normalizer_relIndex_eq_two_of_pair D Q W
    (fun g hg => thompson_normalizer_preserves_maxFamily_pair R Q W hfamily (hDN hg))
    x (hMD hxM) hmove
  have hstab : D ⊓ normalizer (Q : Set G) = R := by
    apply le_antisymm
    · exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hcontrol.le
    · exact le_inf hRD hRQ
  have hiD : R.relIndex D = 2 := by
    rw [←hstab,inf_relIndex_left]
    exact hidx
  have hm := relIndex_mul_relIndex R M D hRM hMD
  rw [hi,hiD] at hm
  have hDM : D ≤ M := relIndex_eq_one.mp (by omega)
  let : Group.IsNilpotent P := hP.isNilpotent
  have hself : normalizer (M.subgroupOf P : Set P) = M.subgroupOf P := by
    apply le_antisymm _ le_normalizer
    rw [←subgroupOf_normalizer_eq hMP]
    intro g hg
    exact hDM ⟨g.property,hg⟩
  have ht := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := P)) _ hself
  exact le_antisymm hMP (subgroupOf_eq_top.mp ht)

end Theory.GroupTheory
