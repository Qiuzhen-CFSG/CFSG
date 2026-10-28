module
public import Theory.GroupTheory.FourFamilyAction.Endgame
public import Theory.GroupAction.IndexedSubgroupFamily
public import Theory.GroupTheory.PGroup.InvariantThompsonPairNormalizer
/-!
# The four-family Thompson normalizer theorem

The original maximum elementary family constructs the actual permutation
representation. Its pointwise kernel and the two successive index-two
extensions identify the image of M with the nonregular Klein four. The
normalizer endgame then gives the full-group or dihedral quotient alternative,
retaining the literal J(R) quotient and mixed subgroup normalizer.

Source application: Aschbacher--Smith C.6.1 case (beta), printed p.165.
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory.FourFamilyAction
variable {G : Type*} [Group G] [Finite G]

theorem thompson_global
    (P M R : Subgroup G) (hP : IsPGroup 2 P) (hRM : R ≤ M) (hMP : M ≤ P)
    (hi : R.relIndex M = 2) (hj : (elementaryAbelianMaxJ R).relIndex R = 2)
    (hJ : elementaryAbelianMaxJ M = elementaryAbelianMaxJ R)
    (f : Fin 4 → Subgroup G) (hinj : Function.Injective f)
    (hfamily : Set.range f = elementaryAbelianMaxSubgroups R)
    (hpair : {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} = {f 0,f 1})
    (hkernel : ∀ g ∈ P, (∀ A ∈ elementaryAbelianMaxSubgroups R,
      g ∈ normalizer (A : Set G)) ↔ g ∈ elementaryAbelianMaxJ R) :
    let S := elementaryAbelianMaxJ R
    let N := P ⊓ normalizer (S : Set G)
    letI : (S.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer inf_le_right
    N = P ⊓ normalizer (M : Set G) ∧
      (M = P ∨ Nonempty ((N ⧸ S.subgroupOf N) ≃* DihedralGroup 4) ∧
        2 * Nat.card S ≤ Nat.card (P ⊓ normalizer ((f 0 ⊔ f 2 : Subgroup G) : Set G) : Subgroup G)) := by
  let N := P ⊓ normalizer (elementaryAbelianMaxJ M : Set G)
  have hMN : M ≤ N := le_inf hMP
    (M.le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ M))
  have hinv (g : N) (i : Fin 4) : ∃ j, f j = (f i).conjBy (g : G) := by
    have hfi : f i ∈ elementaryAbelianMaxSubgroups R := hfamily ▸ ⟨i,rfl⟩
    rw [←maxFamily_thompson] at hfi
    have hn : (g : G) ∈ normalizer (elementaryAbelianMaxJ R : Set G) := hJ ▸ g.property.2
    have hh := (maxFamily_map_injective_iff (MulAut.conj (g : G)).toMonoidHom
      (MulAut.conj (g : G)).injective (elementaryAbelianMaxJ R) (f i)).mpr hfi
    have he : (elementaryAbelianMaxJ R).map (MulAut.conj (g : G)).toMonoidHom = elementaryAbelianMaxJ R :=
      mem_normalizer_iff_map_conj_eq.mp hn
    rw [he,maxFamily_thompson,←hfamily] at hh
    exact hh
  let ρ := IndexedSubgroupFamily.action N f hinj hinv
  have hfix (g : N) (i : Fin 4) : ρ g i = i ↔ (g : G) ∈ normalizer (f i : Set G) :=
    IndexedSubgroupFamily.action_fixed_iff N f hinj hinv g i
  have hker : ρ.ker = (elementaryAbelianMaxJ M).subgroupOf N := by
    ext g
    change ρ g = 1 ↔ (g : G) ∈ elementaryAbelianMaxJ M
    rw [hJ,←hkernel (g : G) g.property.1]
    constructor
    · intro he A hA
      obtain ⟨i,rfl⟩ := hfamily.symm ▸ hA
      exact (hfix g i).mp (by rw [he]; rfl)
    · intro hall
      apply Equiv.ext
      intro i
      exact (hfix g i).mpr (hall (f i) (hfamily ▸ ⟨i,rfl⟩))
  have hMR : M ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hRM).mp (normal_of_index_eq_two hi)
  have hle : (M.subgroupOf N).map ρ ≤ pairGroup := by
    rintro p ⟨g,hg,rfl⟩
    apply (mem_pair_iff (ρ g)).mpr
    have ha (i j : Fin 4)
        (hp : {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} = {f i,f j}) :
        ρ g i = i ∨ ρ g i = j := by
      have hh := normalizer_preserves_invariant_maxFamily_pair R (f i) (f j) hp (hMR hg)
      have he := IndexedSubgroupFamily.action_apply N f hinj hinv g i
      exact hh.imp (fun hi => hinj (he.trans hi)) (fun hj => hinj (he.trans hj))
    exact ⟨ha 0 1 hpair,(ha 1 0 (hpair.trans (Set.pair_comm _ _))).symm⟩
  have hcard : Nat.card ((M.subgroupOf N).map ρ) = 4 := by
    rw [←relIndex_ker,hker,relIndex_subgroupOf hMN,hJ]
    have hJR : elementaryAbelianMaxJ R ≤ R := sSup_le (fun _ h => h.1)
    have hh := relIndex_mul_relIndex (elementaryAbelianMaxJ R) R M hJR hRM
    rw [hi,hj] at hh
    exact hh.symm
  have himage : (M.subgroupOf N).map ρ = pairGroup :=
    eq_of_le_of_card_ge hle (by rw [hcard,pair_card])
  have hg := global_endgame P M hP hMP ρ hker himage f
    (IndexedSubgroupFamily.action_apply N f hinj hinv)
  let C (S : Subgroup G) : Prop :=
    let N := P ⊓ normalizer (S : Set G)
    letI : (S.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer inf_le_right
    N = P ⊓ normalizer (M : Set G) ∧
      (M = P ∨ Nonempty ((N ⧸ S.subgroupOf N) ≃* DihedralGroup 4) ∧
        2 * Nat.card S ≤ Nat.card (P ⊓ normalizer ((f 0 ⊔ f 2 : Subgroup G) : Set G) : Subgroup G))
  have hh : C (elementaryAbelianMaxJ M) := hg
  exact hJ ▸ hh

end Theory.GroupTheory.FourFamilyAction
