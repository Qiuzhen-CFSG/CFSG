module
public import Theory.GroupTheory.PGroup.ThompsonPairNormalizer
/-!
# Normalizing a two-member invariant elementary family

The normalizer of R preserves its R-invariant maximum elementary subgroups.
If these form a pair and the stabilizer of one member in a finite two-group
is R, the relative normalizer has index two. When the pair spans J(R),
every element outside R gives the corresponding conjugate Thompson span.

Source application: Aschbacher--Smith C.6.1(1), printed pp.164--165.
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_preserves_invariant_maxFamily_pair
    (R Q W : Subgroup G)
    (hfamily : {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} = {Q,W})
    {g : G} (hg : g ∈ normalizer (R : Set G)) :
    Q.map (MulAut.conj g).toMonoidHom = Q ∨ Q.map (MulAut.conj g).toMonoidHom = W := by
  let f := MulAut.conj g
  have hQ : Q ∈ elementaryAbelianMaxSubgroups R ∧ R ≤ normalizer (Q : Set G) := by
    change Q ∈ {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)}
    rw [hfamily]
    exact Set.mem_insert _ _
  have he : R.map f.toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp hg
  have hmax := (maxFamily_map_injective_iff f.toMonoidHom f.injective R Q).mpr hQ.1
  rw [he] at hmax
  have hnormal : R ≤ normalizer (Q.map f.toMonoidHom : Set G) := by
    rw [←he]
    exact (map_mono hQ.2).trans (le_normalizer_map f.toMonoidHom)
  have hh : Q.map f.toMonoidHom ∈
      {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} := ⟨hmax,hnormal⟩
  rw [hfamily] at hh
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hh

theorem twoGroup_normalizer_index_two_of_invariant_maxFamily_pair
    (P R Q W : Subgroup G) (hP : IsPGroup 2 P) (hRP : R < P)
    (hfamily : {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} = {Q,W})
    (hcontrol : P ⊓ normalizer (Q : Set G) = R)
    (hspan : elementaryAbelianMaxJ R = Q ⊔ W) :
    R.relIndex (P ⊓ normalizer (R : Set G)) = 2 ∧
      ∀ x ∈ P ⊓ normalizer (R : Set G), x ∉ R →
        elementaryAbelianMaxJ R = Q ⊔ Q.map (MulAut.conj x⁻¹).toMonoidHom := by
  let N₀ := P ⊓ normalizer (R : Set G)
  have hRN : R ≤ N₀ := le_inf hRP.le R.le_normalizer
  let : Group.IsNilpotent P := hP.isNilpotent
  have hproper : R.subgroupOf P < ⊤ := lt_top_iff_ne_top.mpr
    (fun he => hRP.not_ge (subgroupOf_eq_top.mp he))
  obtain ⟨z,hzn,hzr⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (R.subgroupOf P) hproper)
  have hzN : (z : G) ∈ normalizer (R : Set G) := by
    rwa [←subgroupOf_normalizer_eq hRP.le] at hzn
  have hm : Q.map (MulAut.conj (z : G)).toMonoidHom ≠ Q := by
    intro he
    exact hzr (hcontrol ▸ ⟨z.property,mem_normalizer_iff_map_conj_eq.mpr he⟩)
  have hpair (g : G) (hg : g ∈ normalizer (R : Set G)) :=
    normalizer_preserves_invariant_maxFamily_pair R Q W hfamily hg
  have hi := normalizer_relIndex_eq_two_of_pair N₀ Q W
    (fun g hg => hpair g hg.2) z ⟨z.property,hzN⟩ hm
  have hs : N₀ ⊓ normalizer (Q : Set G) = R := by
    apply le_antisymm
    · exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hcontrol.le
    · exact le_inf hRN (hcontrol ▸ inf_le_right)
  refine ⟨?_,?_⟩
  · change R.relIndex N₀ = 2
    rw [←hs,inf_relIndex_left]
    exact hi
  · intro y hy hyr
    have hmove : Q.map (MulAut.conj y⁻¹).toMonoidHom ≠ Q := by
      intro he
      have hn : y⁻¹ ∈ normalizer (Q : Set G) := mem_normalizer_iff_map_conj_eq.mpr he
      have hn' : y ∈ normalizer (Q : Set G) := by
        simpa only [inv_inv] using (normalizer (Q : Set G)).inv_mem hn
      exact hyr (hcontrol ▸ (show y ∈ P ⊓ normalizer (Q : Set G) from ⟨hy.1,hn'⟩))
    rw [(hpair y⁻¹ ((normalizer (R : Set G)).inv_mem hy.2)).resolve_left hmove]
    exact hspan

end Theory.GroupTheory
