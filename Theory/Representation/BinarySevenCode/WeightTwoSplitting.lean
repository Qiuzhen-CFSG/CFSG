module
public import Theory.Representation.BinarySevenCode.WeightTwoCore

/-!
# The moved space and support-pair involution for a weight-two point

The A₅ fixer moves exactly the even words vanishing on its two fixed
letters: pair differences span that space. The transposition on the two
letters is central in the full word stabilizer and belongs to its two-core.
Its fixed words split into the moved space and the line of the marked word.
These explicit coordinates supply the omega-center decomposition in
Aschbacher--Smith, Lemma 12.3.7(2), printed p.809.
-/
@[expose] public noncomputable section
open Subgroup Representation.BinaryOffender
namespace BinarySevenCode.WeightTwoGeometry

def pairWord (i j : Fin 7) : EvenWord :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp [mem_evenWords_iff, Finset.sum_add_distrib]; decide⟩

theorem action_pairWord (g : Equiv.Perm (Fin 7)) (i j : Fin 7) :
    evenRepresentation g (pairWord i j) = pairWord (g i) (g j) := by
  apply Subtype.ext
  funext k
  simp only [evenRepresentation_apply, pairWord, Pi.add_apply, Pi.single_apply]
  simp only [Equiv.symm_apply_eq]

theorem pairWord_sub (i j s : Fin 7) : pairWord i s - pairWord j s = pairWord i j := by
  apply Subtype.ext
  change (Pi.single i 1 + Pi.single s 1) - (Pi.single j 1 + Pi.single s 1) =
    Pi.single i 1 + Pi.single j 1
  rw [add_sub_add_right_eq_sub, ZModModule.sub_eq_add]

theorem pairWord_basis (x : EvenWord) (r : Fin 7) :
    x = ∑ i : Fin 7, x.val i • pairWord i r := by
  apply Subtype.ext
  simp only [Submodule.coe_sum,Submodule.coe_smul_of_tower]
  have hx : ∑ i, x.val i = 0 := (mem_evenWords_iff _).mp x.property
  simp only [pairWord, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hx, zero_smul, add_zero]
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem support_zero_mem_moved (w x : EvenWord) (hw : weight w.val = 2)
    (hx : ∀ i ∈ support w, x.val i = 0) :
    x ∈ subspaceCommutator (evenRepresentation.comp (alternatingGroup (Fin 7)).subtype)
      ⊤ (five w) := by
  classical
  have hs : (support w).Nonempty := Finset.card_pos.mp (by change 0 < weight w.val; omega)
  obtain ⟨s,hs⟩ := hs
  have hr : Nonempty (Complement w) := Nat.card_pos_iff.mp (by rw [complement_card w hw]; decide) |>.1
  obtain ⟨r⟩ := hr
  rw [pairWord_basis x r]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i ∈ support w
  · rw [hx i hi,zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    obtain ⟨a,ha⟩ := five_transitive_complement w hw r ⟨i,Finset.mem_compl.mpr hi⟩
    have has : a.val.val s = s := a.property ⟨s,hs⟩
    have he : evenRepresentation a.val.val (pairWord r s) - pairWord r s = pairWord i r := by
      rw [action_pairWord,ha,has,pairWord_sub]
    rw [← he]
    exact Submodule.subset_span ⟨a.val,a.property,pairWord r s,Submodule.mem_top,rfl⟩

theorem word_eq_pairWord (w : EvenWord) (i j : Fin 7) (hij : i ≠ j)
    (hw : support w = {i,j}) : w = pairWord i j := by
  apply Subtype.ext
  funext k
  have hk : w.val k ≠ 0 ↔ k = i ∨ k = j := by
    have he : k ∈ support w ↔ k = i ∨ k = j := by rw [hw]; simp
    simpa only [support,Finset.mem_filter,Finset.mem_univ,true_and] using he
  change w.val k = (Pi.single i 1 + Pi.single j 1 : Word) k
  by_cases hki : k = i
  · subst k
    have hv : w.val i = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ (hk.mpr (Or.inl rfl))
    simp [hv, hij]
  · by_cases hkj : k = j
    · subst k
      have hv : w.val j = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ (hk.mpr (Or.inr rfl))
      simp [hv, hij.symm]
    · have hv : w.val k = 0 := by simpa [hki,hkj] using hk
      simp [hv,hki,hkj]

theorem support_swap_mem (w : EvenWord) (i j : Fin 7) (hij : i ≠ j)
    (hw : support w = {i,j}) : Equiv.swap i j ∈ symmetricStabilizer w := by
  rw [mem_symmetricStabilizer,word_eq_pairWord w i j hij hw,action_pairWord]
  simp only [Equiv.swap_apply_left,Equiv.swap_apply_right]
  apply Subtype.ext
  exact add_comm _ _

theorem support_swap_commutes (w : EvenWord) (i j : Fin 7) (hij : i ≠ j)
    (hw : support w = {i,j}) (g : symmetricStabilizer w) :
    g.val * Equiv.swap i j = Equiv.swap i j * g.val := by
  have hi := (stabilizer_mem_support w g i).mpr (hw ▸ (by simp : i ∈ ({i,j} : Finset (Fin 7))))
  have hj := (stabilizer_mem_support w g j).mpr (hw ▸ (by simp : j ∈ ({i,j} : Finset (Fin 7))))
  rw [hw] at hi hj
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi hj
  have hne := g.val.injective.ne hij
  rw [Equiv.mul_swap_eq_swap_mul]
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact (hne (hi.trans hj.symm)).elim
  · rw [hi,hj]
  · rw [hi,hj,Equiv.swap_comm]
  · exact (hne (hi.trans hj.symm)).elim

theorem support_swap_mem_twoCore (w : EvenWord) (i j : Fin 7) (hij : i ≠ j)
    (hw : support w = {i,j}) :
    (⟨Equiv.swap i j,support_swap_mem w i j hij hw⟩ : symmetricStabilizer w) ∈
      pCore 2 (symmetricStabilizer w) := by
  let s : symmetricStabilizer w := ⟨Equiv.swap i j,support_swap_mem w i j hij hw⟩
  have hs : s ∈ center (symmetricStabilizer w) :=
    mem_center_iff.mpr (fun g => Subtype.ext (support_swap_commutes w i j hij hw g))
  have hz : zpowers s ≤ center (symmetricStabilizer w) := zpowers_le.mpr hs
  let : (zpowers s).Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hz hn) g,mul_inv_cancel_right]
    exact hn⟩
  have hp : IsPGroup 2 (zpowers s) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by change (Equiv.swap i j)^2 = 1; simp [pow_two]))
  exact (show zpowers s ≤ pCore 2 (symmetricStabilizer w) from le_sSup ⟨inferInstance,hp⟩)
    (mem_zpowers s)

theorem support_swap_fixed_split (w x : EvenWord) (i j : Fin 7) (hij : i ≠ j)
    (hw : support w = {i,j}) (hx : evenRepresentation (Equiv.swap i j) x = x) :
    ∃ y : EvenWord, (∀ k ∈ support w, y.val k = 0) ∧
      ∃ c : ZMod 2, x = y + c • w := by
  let c := x.val i
  let y := x - c • w
  have hxj : x.val j = x.val i := by
    have h := congrArg (fun v : EvenWord => v.val i) hx
    simpa only [evenRepresentation_apply,Equiv.symm_swap,Equiv.swap_apply_left] using h
  refine ⟨y,?_,c,by dsimp only [y]; exact (sub_add_cancel x (c • w)).symm⟩
  intro k hk
  rw [hw] at hk
  have hw' := word_eq_pairWord w i j hij hw
  have hwi : w.val i = 1 := by rw [hw']; simp [pairWord,hij]
  have hwj : w.val j = 1 := by rw [hw']; simp [pairWord,hij.symm]
  simp only [Finset.mem_insert,Finset.mem_singleton] at hk
  rcases hk with hk | hk
  · subst k
    change x.val i - c * w.val i = 0
    rw [hwi,mul_one,sub_self]
  · subst k
    change x.val j - c * w.val j = 0
    rw [hwj,hxj,mul_one,sub_self]

end BinarySevenCode.WeightTwoGeometry
