module
public import ABG.ChapterII.Section1.WreathedUHighInvolutions
public import ABG.ChapterII.Section1.WreathedVHighInvolutions
public import ABG.ChapterII.Section1.WreathedWeakCenter
public import ABG.ChapterII.Section1.WreathedLowFusion
public import ABG.ChapterII.Section2.AutomizerRestriction
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Global involution fusion for wreathed Sylow subgroups

For an actual wreathed fusion frame in a finite group, the two automizer
indices determine the exact number of ambient conjugacy classes of
involutions. Indices six at both `U` and `V` give one class; exactly one
index two gives two classes; and two low indices give three classes. The
class-count conclusions retain representatives, coverage, and pairwise
nonconjugacy.

The three Sylow classes have representatives `x`, `x₂`, and `z`. A high
base automizer fuses `x` with `x₂`, while a high outer automizer fuses
`x₂` with `z`. At low base index the central representative `x` has no
distinct ambient conjugate inside the Sylow subgroup. At low outer index,
ambient fusion preserves membership in the base, separating `z` from
`x` and `x₂`. When both indices are low, all ambient fusion between Sylow
elements is already Sylow fusion. Finally, Sylow conjugacy for prime-power
order elements transports these local representatives to every ambient
involution.

This proves the four involution-count clauses of Alperin--Brauer--Gorenstein,
Chapter II, Section 1, Proposition 2, article pp.12--13, in
`refs/latex/alperin-brauer-gorenstein-pages/page-013.tex` and
`page-014.tex`.
-/

namespace ABG.Wreathed
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem order_conj {x y : G} (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).symm

private theorem count_of_representatives (S : Sylow 2 G) {k : ℕ} (r : Fin k → S)
    (ho : ∀ i, orderOf (r i) = 2)
    (hsep : ∀ i j, IsConj (r i : G) (r j : G) → i = j)
    (hcover : ∀ y : S, orderOf y = 2 → ∃ i, IsConj (y : G) (r i : G)) :
    HasElementConjugacyClassCount G 2 k := by
  refine ⟨fun i => (r i : G), fun i => (Subgroup.orderOf_coe _).trans (ho i), hsep, ?_⟩
  intro x hx
  obtain ⟨y, hxy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  have hy : orderOf y = 2 :=
    (Subgroup.orderOf_coe y).symm.trans ((order_conj hxy).symm.trans hx)
  obtain ⟨i, hi⟩ := hcover y hy
  exact ⟨i, hxy.trans hi⟩

private theorem count_one (S : Sylow 2 G) (a : S) (ha : orderOf a = 2)
    (hcover : ∀ y : S, orderOf y = 2 → IsConj (y : G) (a : G)) :
    HasElementConjugacyClassCount G 2 1 :=
  count_of_representatives S (fun _ => a) (fun _ => ha)
    (fun i j _ => Subsingleton.elim i j) (fun y hy => ⟨0, hcover y hy⟩)

private theorem count_two (S : Sylow 2 G) (a b : S)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : ¬ IsConj (a : G) (b : G))
    (hcover : ∀ y : S, orderOf y = 2 →
      IsConj (y : G) (a : G) ∨ IsConj (y : G) (b : G)) :
    HasElementConjugacyClassCount G 2 2 := by
  let r : Fin 2 → S := ![a, b]
  apply count_of_representatives S r
  · intro i
    fin_cases i
    · exact ha
    · exact hb
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hab hij).elim
    · exact (hab hij.symm).elim
    · rfl
  · intro y hy
    rcases hcover y hy with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

private theorem count_three {n : ℕ} (S : Sylow 2 G) (P : Presentation S n)
    (hc : ∀ {x y : S}, IsConj (x : G) (y : G) → IsConj x y) :
    HasElementConjugacyClassCount G 2 3 := by
  let r : Fin 3 → S := ![P.x, P.x₂, P.z]
  apply count_of_representatives S r
  · intro i
    fin_cases i
    · exact P.x_orderOf
    · exact P.x₂_orderOf
    · exact P.z_orderOf
  · intro i j hij
    have h := hc hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (P.x_not_isConj_x₂ h).elim
    · exact (P.x_not_isConj_z h).elim
    · exact (P.x_not_isConj_x₂ h.symm).elim
    · rfl
    · exact (P.x₂_not_isConj_z h).elim
    · exact (P.x_not_isConj_z h.symm).elim
    · exact (P.x₂_not_isConj_z h.symm).elim
    · rfl
  · intro y hy
    rcases P.involution_isConj hy with h | h | h
    · exact ⟨0, (S : Subgroup G).subtype.map_isConj h⟩
    · exact ⟨1, (S : Subgroup G).subtype.map_isConj h⟩
    · exact ⟨2, (S : Subgroup G).subtype.map_isConj h⟩

/-- The base and outer automizer indices determine all four possible exact
ambient involution counts for a wreathed fusion frame. -/
public theorem involution_fusion (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G)
    (hf : WreathedFusionFrame S n U V) :
    (automizerIndex U = 6 → outerAutomizerIndex V = 6 →
      HasElementConjugacyClassCount G 2 1) ∧
    (automizerIndex U = 2 → outerAutomizerIndex V = 6 →
      HasElementConjugacyClassCount G 2 2) ∧
    (automizerIndex U = 6 → outerAutomizerIndex V = 2 →
      HasElementConjugacyClassCount G 2 2) ∧
    (automizerIndex U = 2 → outerAutomizerIndex V = 2 →
      HasElementConjugacyClassCount G 2 3) := by
  obtain ⟨P⟩ := nonempty_presentation hf.1
  have hUP : P.U = U.subgroupOf (S : Subgroup G) :=
    hf.2.2.2.2.1 P.U P.abelian_maximal_unique.1 P.U_isCoatom
  have hxU : (P.x : G) ∈ U := by
    change P.x ∈ U.subgroupOf (S : Subgroup G)
    rw [← hUP]
    exact P.T_le_U (Subgroup.subset_closure (by simp))
  have hx₂U : (P.x₂ : G) ∈ U := by
    change P.x₂ ∈ U.subgroupOf (S : Subgroup G)
    rw [← hUP]
    exact P.T_le_U (Subgroup.subset_closure (by simp))
  have hzU : (P.z : G) ∉ U := by
    change P.z ∉ U.subgroupOf (S : Subgroup G)
    rw [← hUP]
    exact P.z_not_mem_U
  have hxx₂ (hU : automizerIndex U = 6) : IsConj (P.x : G) (P.x₂ : G) := by
    apply u_involutions_isConj S n U V hf hU ⟨P.x, hxU⟩ ⟨P.x₂, hx₂U⟩
    · rw [← Subgroup.orderOf_coe]
      exact (Subgroup.orderOf_coe P.x).trans P.x_orderOf
    · rw [← Subgroup.orderOf_coe]
      exact (Subgroup.orderOf_coe P.x₂).trans P.x₂_orderOf
  have hx₂z (hV : outerAutomizerIndex V = 6) : IsConj (P.x₂ : G) (P.z : G) := by
    apply v_high_involution_fusion S P
    obtain ⟨_, s, hs⟩ := hf.presentation_representatives P
    have hi := outerAutomizerIndex_map (P.V.map (S : Subgroup G).subtype)
      (MulAut.conj (s : G))
    rw [hs, hV] at hi
    exact hi.symm
  have hcover (y : S) (hy : orderOf y = 2) :
      IsConj (y : G) (P.x : G) ∨ IsConj (y : G) (P.x₂ : G) ∨
        IsConj (y : G) (P.z : G) := by
    exact (P.involution_isConj hy).imp ((S : Subgroup G).subtype.map_isConj)
      (fun h => h.imp ((S : Subgroup G).subtype.map_isConj)
        ((S : Subgroup G).subtype.map_isConj))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hU hV
    apply count_one S P.x P.x_orderOf
    intro y hy
    rcases hcover y hy with h | h | h
    · exact h
    · exact h.trans (hxx₂ hU).symm
    · exact (h.trans (hx₂z hV).symm).trans (hxx₂ hU).symm
  · intro hU hV
    apply count_two S P.x P.z P.x_orderOf P.z_orderOf
    · intro h
      have he := central_isConj_eq_of_u_index_two S n U V hf hU P.x_mem_center h
      exact P.x_not_isConj_z (he ▸ IsConj.refl P.x)
    · intro y hy
      rcases hcover y hy with h | h | h
      · exact Or.inl h
      · exact Or.inr (h.trans (hx₂z hV))
      · exact Or.inr h
  · intro hU hV
    apply count_two S P.x P.z P.x_orderOf P.z_orderOf
    · intro h
      exact hzU ((mem_base_iff_of_isConj_of_v_index_two S n U V hf hV h).mp hxU)
    · intro y hy
      rcases hcover y hy with h | h | h
      · exact Or.inl h
      · exact Or.inl (h.trans (hxx₂ hU).symm)
      · exact Or.inr h
  · intro hU hV
    exact count_three S P (isConj_of_indices_two S n U V hf hU hV)

end ABG.Wreathed
