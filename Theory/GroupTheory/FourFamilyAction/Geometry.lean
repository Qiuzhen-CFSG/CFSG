module
public import Theory.GroupTheory.ElementaryThompsonFourFamily
public import Theory.GroupTheory.FourFamilyAction.Thompson
public import Mathlib.Tactic.FinCases

/-!
# Labelling and the extra orbit of a four-member elementary square

The adjacent index bounds and opposite intersections distinguish all four
maximum subgroups and make each adjacent index exactly two. The faithful
family action then supplies an element outside its kernel exchanging the
extra pair. Core normalizer control transports this same family to every
outside conjugator in the relative normalizer.

Source application: Aschbacher--Smith C.6.1(4), printed pp.164--166.
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory.FourFamilyAction
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem count (Q A : Subgroup G) :
    Nat.card (Q ⊓ A : Subgroup G) * Q.relIndex A = Nat.card A := by
  simpa only [relIndex_bot_left,inf_relIndex_right] using
    relIndex_mul_relIndex (⊥ : Subgroup G) (Q ⊓ A) A bot_le inf_le_right

theorem labelled_geometry (R S Q W P P' I : Subgroup G)
    (hf : elementaryAbelianMaxSubgroups R = {Q,W,P,P'})
    (hg : FourFamilyGeometry S Q W P P' I) :
    ∃ f : Fin 4 → Subgroup G, Function.Injective f ∧
      Set.range f = elementaryAbelianMaxSubgroups R ∧
      f 0 = Q ∧ f 1 = W ∧ f 2 = P ∧ f 3 = P' ∧ Q.relIndex (f 2) = 2 := by
  have hQ : Q ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
  have hW : W ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
  have hP : P ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
  have hP' : P' ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
  have hc (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups R) : Nat.card A = Nat.card Q :=
    le_antisymm (hQ.2.2 A hA.1 hA.2.1) (hA.2.2 Q hQ.1 hQ.2.1)
  have hi : 0 < Nat.card I := Nat.card_pos
  have hWP : W ≠ P := by
    intro he
    have hh := count Q P
    rw [←he,hg.opposite_first,hc W hW] at hh
    have ht := hg.adjacent_left
    rw [←he] at ht
    nlinarith [hg.core_card]
  have hWP' : W ≠ P' := by
    intro he
    have hh := count Q P'
    rw [←he,hg.opposite_first,hc W hW] at hh
    have ht := hg.adjacent_right
    rw [←he] at ht
    nlinarith [hg.core_card]
  have hQP : Q ≠ P := by
    intro he
    have hh := count Q P'
    rw [he,hg.opposite_second,hc P' hP'] at hh
    have ht := hg.adjacent_right
    rw [he] at ht
    nlinarith [hg.core_card]
  have hQP' : Q ≠ P' := by
    intro he
    have hh := count Q P
    rw [he,inf_comm P' P,hg.opposite_second,hc P hP] at hh
    have ht := hg.adjacent_left
    rw [he] at ht
    nlinarith [hg.core_card]
  have hQW : Q ≠ W := by
    intro he
    have hh := hg.opposite_first
    rw [←he,inf_idem] at hh
    have hp : 0 < Nat.card Q := Nat.card_pos
    have hb := hg.core_card
    rw [←hh] at hb
    omega
  have hPP : P ≠ P' := by
    intro he
    apply hg.cross_ne
    rw [he]
  have hidx : Q.relIndex P = 2 := by
    have hlo : 0 < Q.relIndex P := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hn : Q.relIndex P ≠ 1 := by
      intro hi
      exact hQP ((eq_of_le_of_card_ge (relIndex_eq_one.mp hi) (hc P hP).ge).symm)
    have hhi := hg.adjacent_left
    omega
  let f : Fin 4 → Subgroup G := ![Q,W,P,P']
  refine ⟨f,?_,?_,rfl,rfl,rfl,rfl,hidx⟩
  · intro i j he
    fin_cases i <;> fin_cases j
    all_goals simp only [f,Matrix.cons_val,Fin.reduceFinMk] at he
    all_goals first
    | rfl
    | exact (hQW he).elim
    | exact (hQW he.symm).elim
    | exact (hQP he).elim
    | exact (hQP he.symm).elim
    | exact (hQP' he).elim
    | exact (hQP' he.symm).elim
    | exact (hWP he).elim
    | exact (hWP he.symm).elim
    | exact (hWP' he).elim
    | exact (hWP' he.symm).elim
    | exact (hPP he).elim
    | exact (hPP he.symm).elim
  · rw [hf]
    simp only [f,Matrix.range_cons,Matrix.range_empty,Set.union_empty,Set.singleton_union]
end Theory.GroupTheory.FourFamilyAction

open Subgroup Stellmacher
namespace Theory.GroupTheory.FourFamilyAction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem extra_pair_conjugate
    (R S : Subgroup G) (hSR : S < R)
    (f : Fin 4 → Subgroup G) (hinj : Function.Injective f)
    (hfamily : Set.range f = elementaryAbelianMaxSubgroups R)
    (hfixed : R ≤ normalizer (f 0 : Set G) ∧ R ≤ normalizer (f 1 : Set G))
    (hkernel : ∀ g ∈ R, (∀ A ∈ elementaryAbelianMaxSubgroups R,
      g ∈ normalizer (A : Set G)) ↔ g ∈ S) :
    ∃ r ∈ R, r ∉ S ∧ (f 2).map (MulAut.conj r).toMonoidHom = f 3 := by
  have hinv (g : R) (i : Fin 4) : ∃ j, f j = (f i).conjBy (g : G) := by
    have hm := (maxFamily_map_injective_iff (MulAut.conj (g : G)).toMonoidHom
      (MulAut.conj (g : G)).injective R (f i)).mpr (hfamily ▸ ⟨i,rfl⟩)
    have hr : R.map (MulAut.conj (g : G)).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp (R.le_normalizer g.property)
    rw [hr,←hfamily] at hm
    exact hm
  let ρ := IndexedSubgroupFamily.action R f hinj hinv
  have hfix (r : R) (i : Fin 4) : ρ r i = i ↔ (r : G) ∈ normalizer (f i : Set G) :=
    IndexedSubgroupFamily.action_fixed_iff R f hinj hinv r i
  obtain ⟨r,hr,hrs⟩ := SetLike.exists_of_lt hSR
  let r₀ : R := ⟨r,hr⟩
  have h0 : ρ r₀ 0 = 0 := (hfix r₀ 0).mpr (hfixed.1 hr)
  have h1 : ρ r₀ 1 = 1 := (hfix r₀ 1).mpr (hfixed.2 hr)
  have hn : ρ r₀ ≠ 1 := by
    intro he
    apply hrs
    apply (hkernel r hr).mp
    intro A hA
    obtain ⟨i,rfl⟩ := hfamily.symm ▸ hA
    exact (hfix r₀ i).mp (by rw [he]; rfl)
  have hc : ∀ p : Equiv.Perm (Fin 4), p 0 = 0 → p 1 = 1 → p ≠ 1 → p 2 = 3 := by
    decide +kernel
  refine ⟨r,hr,hrs,?_⟩
  have he := IndexedSubgroupFamily.action_apply R f hinj hinv r₀ 2
  rw [hc (ρ r₀) h0 h1 hn] at he
  exact he.symm
end Theory.GroupTheory.FourFamilyAction

namespace Theory.GroupTheory.FourFamilyAction
variable {G : Type*} [Group G] [Finite G]
theorem normalizer_four_family
    (Λ R S Q W P P' I : Subgroup G) (hRΛ : R ≤ Λ) (hSR : S < R)
    (hf : elementaryAbelianMaxSubgroups R = {Q,W,P,P'})
    (hg : FourFamilyGeometry S Q W P P' I)
    (hpair : {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} = {Q,W})
    (hkernel : ∀ g ∈ Λ, (∀ A ∈ elementaryAbelianMaxSubgroups R,
      g ∈ normalizer (A : Set G)) ↔ g ∈ S)
    (hcontrol : Λ ⊓ normalizer (Q : Set G) = R) :
    ∀ y ∈ Λ ⊓ normalizer (R : Set G), y ∉ R →
      ∃ A : Subgroup G, ∃ r : G,
        r ∈ R ∧ r ∉ S ∧ Q.relIndex A = 2 ∧
        elementaryAbelianMaxSubgroups R =
          {Q,Q.map (MulAut.conj y⁻¹).toMonoidHom,A,A.map (MulAut.conj r⁻¹).toMonoidHom} := by
  obtain ⟨f,hinj,hfamily,h0,h1,h2,h3,hidx⟩ := labelled_geometry R S Q W P P' I hf hg
  have hQn : R ≤ normalizer (Q : Set G) := by
    have hh : Q ∈ {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} := by
      rw [hpair]; simp
    exact hh.2
  have hWn : R ≤ normalizer (W : Set G) := by
    have hh : W ∈ {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} := by
      rw [hpair]; simp
    exact hh.2
  obtain ⟨r,hr,hrs,he⟩ := extra_pair_conjugate R S hSR f hinj hfamily
    (by rw [h0,h1]; exact ⟨hQn,hWn⟩) (fun g hg => hkernel g (hRΛ hg))
  intro y hy hyr
  have hmove : Q.map (MulAut.conj y⁻¹).toMonoidHom ≠ Q := by
    intro heq
    have hny : y⁻¹ ∈ normalizer (Q : Set G) := mem_normalizer_iff_map_conj_eq.mpr heq
    have hny' : y ∈ normalizer (Q : Set G) := by
      simpa only [inv_inv] using (normalizer (Q : Set G)).inv_mem hny
    exact hyr (hcontrol ▸ (show y ∈ Λ ⊓ normalizer (Q : Set G) from ⟨hy.1,hny'⟩))
  have hmap := (normalizer_preserves_invariant_maxFamily_pair R Q W hpair
    ((normalizer (R : Set G)).inv_mem hy.2)).resolve_left hmove
  refine ⟨f 2,r⁻¹,R.inv_mem hr,?_,hidx,?_⟩
  · intro hri
    exact hrs (by simpa only [inv_inv] using S.inv_mem hri)
  · rw [inv_inv,hmap,he,h2,h3]
    exact hf
end Theory.GroupTheory.FourFamilyAction
