module

public import Theory.AlgebraicGroup.RootSystems.FiniteClassification

universe u v w

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open StandardRootSystem

set_option maxHeartbeats 800000 in
/-- A concrete Dynkin-type witness for a `G₂` root pairing must carry the
`G₂` kind. -/
public theorem dynkinKind_eq_g2_of_isG2
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsG2]
    (classification : RootClassification)
    (hType : HasDynkinType P classification) :
    classification.kind = .G2 := by
  let : MulAction.IsPretransitive P.weylGroup P.Base :=
    weylGroup_action_on_bases_transitive P
  obtain ⟨g2Base, g2Numbering, hg2⟩ := hasDynkinType_g2_of_isG2 P
  obtain ⟨base, numbering, hbase⟩ := hType
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P.weylGroup g2Base base
  change RootPairing.Base.mapAut g.1 g2Base = base at hg
  let long : g2Base.support := g2Numbering.symm 1
  let short : g2Base.support := g2Numbering.symm 0
  have hlong : g.1.indexEquiv long ∈ base.support := by
    rw [← hg, RootPairing.Base.mem_mapAut_support]
    simp
  have hshort : g.1.indexEquiv short ∈ base.support := by
    rw [← hg, RootPairing.Base.mem_mapAut_support]
    simp
  let mappedLong : base.support := ⟨g.1.indexEquiv long, hlong⟩
  let mappedShort : base.support := ⟨g.1.indexEquiv short, hshort⟩
  have hg2Entry : P.pairingIn ℤ long short = -3 := by
    change g2Base.cartanMatrixIn ℤ long short = -3
    rw [hg2]
    simp [long, short, dynkinCartanEntry]
  have hpairing :
      P.pairingIn ℤ mappedLong mappedShort = P.pairingIn ℤ long short := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → R))
    change algebraMap ℤ R (P.pairingIn ℤ mappedLong mappedShort) =
      algebraMap ℤ R (P.pairingIn ℤ long short)
    rw [P.algebraMap_pairingIn, P.algebraMap_pairingIn]
    exact RootPairing.Equiv.pairing_eq g.1 long short
  have hentry :
      dynkinCartanEntry classification (numbering mappedLong)
        (numbering mappedShort) = -3 := by
    rw [← hbase]
    change P.pairingIn ℤ mappedLong mappedShort = -3
    exact hpairing.trans hg2Entry
  rcases classification with ⟨kind, rank⟩
  change kind = .G2
  cases kind <;> simp only [dynkinCartanEntry] at hentry ⊢ <;> omega

/-- The four-vertex path with a unique middle double bond is the standard
type `F₄` matrix, after reversing the numbering when necessary. -/
public lemma cartan_path_middle_doubleBond_is_typeF4
    {κ : Type*} (A : Matrix κ κ ℤ) (e : Fin 4 ≃ κ) (u v : ℤ)
    (hentries : ∀ i j : Fin 4, A (e i) (e j) =
      if i = j then 2 else if i.val + 1 = j.val then
        if i.val = 1 then u else -1
      else if j.val + 1 = i.val then
        if j.val = 1 then v else -1
      else 0)
    (horient : (u = -2 ∧ v = -1) ∨ (u = -1 ∧ v = -2)) :
    ∃ e' : Fin 4 ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeF4CartanMatrix i j := by
  rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨e, ?_⟩
    intro i j
    rw [hentries]
    fin_cases i <;> fin_cases j <;> simp [typeF4CartanMatrix]
  · let e' : Fin 4 ≃ κ := (Fin.revPerm (n := 4)).trans e
    refine ⟨e', ?_⟩
    intro i j
    change A (e (Fin.revPerm (n := 4) i)) (e (Fin.revPerm (n := 4) j)) = _
    rw [hentries]
    fin_cases i <;> fin_cases j <;> simp [typeF4CartanMatrix]

open StandardRootSystem

/-- A connected finite Cartan matrix containing a product-three bond is the
standard `G₂` Cartan matrix after renumbering. -/
public lemma cartan_tripleBond_isG2
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef)
    (a b : κ) (hab : a ≠ b)
    (hprod : A a b * A b a = 3) :
    ∃ e : Fin 2 ≃ κ,
      ∀ i j, A (e i) (e j) = typeG2CartanMatrix i j := by
  have hcard := cartan_tripleBond_card_eq_two
    A d hdiag hrank hconn hpos a b hab hprod
  exact cartan_rankTwo_tripleBond_isG2 A hdiag hrank a b hab hprod hcard

open StandardRootSystem

/-- A path whose unique double bond is its final edge is type `B` or type `C`
according to the orientation of that edge.  The exact-entry premise is an
ordinary matrix formula and carries no classification conclusion. -/
public lemma cartan_path_terminal_doubleBond_is_typeB_or_typeC
    {κ : Type*} (A : Matrix κ κ ℤ) (m : ℕ) (e : Fin (m + 2) ≃ κ)
    (u v : ℤ)
    (hentries : ∀ i j : Fin (m + 2), A (e i) (e j) =
      if i = j then 2 else if i.val + 1 = j.val then
        if i.val = m then u else -1
      else if j.val + 1 = i.val then
        if j.val = m then v else -1
      else 0)
    (horient : (u = -2 ∧ v = -1) ∨ (u = -1 ∧ v = -2)) :
    (∀ i j, A (e i) (e j) = typeBCartanMatrix m i j) ∨
      (∀ i j, A (e i) (e j) = typeCCartanMatrix (m + 1) i j) := by
  rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    apply cartan_pathGraph_eq_typeBCartanMatrix_of_terminal_heavy_bond A e
    · intro i
      simp [hentries]
    · intro i j hf
      rw [hentries]
      have hij : i ≠ j := by omega
      rw [if_neg hij, if_pos hf]
      split_ifs with hi hj
      all_goals simp_all [Fin.ext_iff]
    · intro i j hr
      rw [hentries]
      have hij : i ≠ j := by omega
      rw [if_neg hij, if_neg (by omega), if_pos hr]
      simp
    · intro i j hij hf hr
      simpa [hij, hf, hr] using hentries i j
  · right
    apply cartan_pathGraph_eq_typeCCartanMatrix_of_entries A e
    · intro i
      simp [hentries]
    · intro i j hf
      rw [hentries]
      have hij : i ≠ j := by omega
      rw [if_neg hij, if_pos hf]
      simp
    · intro i j hr
      rw [hentries]
      have hij : i ≠ j := by omega
      rw [if_neg hij, if_neg (by omega), if_pos hr]
      split_ifs with hj hi
      all_goals simp_all [Fin.ext_iff]
    · intro i j hij hf hr
      simpa [hij, hf, hr] using hentries i j

open StandardRootSystem

/-- A path whose unique double bond is its initial edge is type `B` or type
`C`; reversing the path turns it into the terminal case. -/
public lemma cartan_path_initial_doubleBond_is_typeB_or_typeC
    {κ : Type*} (A : Matrix κ κ ℤ) (m : ℕ) (e : Fin (m + 2) ≃ κ)
    (u v : ℤ)
    (hentries : ∀ i j : Fin (m + 2), A (e i) (e j) =
      if i = j then 2 else if i.val + 1 = j.val then
        if i.val = 0 then u else -1
      else if j.val + 1 = i.val then
        if j.val = 0 then v else -1
      else 0)
    (horient : (u = -2 ∧ v = -1) ∨ (u = -1 ∧ v = -2)) :
    (∃ e' : Fin (m + 2) ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeBCartanMatrix m i j) ∨
      (∃ e' : Fin (m + 2) ≃ κ,
        ∀ i j, A (e' i) (e' j) = typeCCartanMatrix (m + 1) i j) := by
  let e' : Fin (m + 2) ≃ κ := (Fin.revPerm (n := m + 2)).trans e
  have hentries' : ∀ i j : Fin (m + 2), A (e' i) (e' j) =
      if i = j then 2 else if i.val + 1 = j.val then
        if i.val = m then v else -1
      else if j.val + 1 = i.val then
        if j.val = m then u else -1
      else 0 := by
    intro i j
    change A (e (Fin.rev i)) (e (Fin.rev j)) = _
    rw [hentries]
    simp only [Fin.rev_injective.eq_iff, Fin.val_rev]
    split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
    all_goals omega
  have horient' : (v = -2 ∧ u = -1) ∨ (v = -1 ∧ u = -2) := by
    rcases horient with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inr ⟨hv, hu⟩
    · exact Or.inl ⟨hv, hu⟩
  rcases cartan_path_terminal_doubleBond_is_typeB_or_typeC
    A m e' v u hentries' horient' with hB | hC
  · exact Or.inl ⟨e', hB⟩
  · exact Or.inr ⟨e', hC⟩

open SimpleGraph StandardRootSystem

/-- Case split for a path with exactly one non-simple bond.  The theorem
returns the standard B/C/F4/G2 matrix rows as ordinary disjunction data; no
classification conclusion is stored in a definition or structure. -/
public lemma cartan_path_single_heavy_case_split
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef)
    {m r : ℕ} (e : Fin (m + 2) ≃ κ) (hpath : ∀ i j,
      (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj (e i) (e j) ↔
        (pathGraph (m + 2)).Adj i j)
    (hr : r + 1 < m + 2)
    (hoff : ∀ q (hq : q + 1 < m + 2), q ≠ r →
      A (e ⟨q, by omega⟩) (e ⟨q + 1, hq⟩) *
        A (e ⟨q + 1, hq⟩) (e ⟨q, by omega⟩) ≤ 1)
    (hheavy : 2 ≤ A (e ⟨r, by omega⟩) (e ⟨r + 1, hr⟩) *
      A (e ⟨r + 1, hr⟩) (e ⟨r, by omega⟩)) :
    (∃ e' : Fin (m + 2) ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeBCartanMatrix m i j) ∨
    (∃ e' : Fin (m + 2) ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeCCartanMatrix (m + 1) i j) ∨
    (∃ e' : Fin 4 ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeF4CartanMatrix i j) ∨
    (∃ e' : Fin 2 ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeG2CartanMatrix i j) := by
  let u := A (e ⟨r, by omega⟩) (e ⟨r + 1, hr⟩)
  let v := A (e ⟨r + 1, hr⟩) (e ⟨r, by omega⟩)
  have hidx : (⟨r, by omega⟩ : Fin (m + 2)) ≠ ⟨r + 1, hr⟩ := by
    intro h
    have hv := congrArg Fin.val h
    change r = r + 1 at hv
    omega
  have hroot : e ⟨r, by omega⟩ ≠ e ⟨r + 1, hr⟩ := by
    intro h
    exact hidx (e.injective h)
  have hsimple : ∀ {i j : Fin (m + 2)}, (pathGraph (m + 2)).Adj i j →
      ¬(i.val = r ∧ j.val = r + 1) →
      ¬(j.val = r ∧ i.val = r + 1) →
      A (e i) (e j) = -1 ∧ A (e j) (e i) = -1 := by
    intro i j hadj hnot₁ hnot₂
    have hadj' := hadj
    rw [pathGraph_adj] at hadj'
    have hbond := cartan_pathGraph_adjacent_rankTwoBond A hrank e hpath hadj
    rcases hadj' with hf | hb
    · have hridx : i.val + 1 < m + 2 := by omega
      have hri : i.val ≠ r := by
        intro hi
        apply hnot₁
        exact ⟨hi, by omega⟩
      have hprod := hoff i.val hridx hri
      have hj : j = (⟨i.val + 1, hridx⟩ : Fin (m + 2)) := by
        apply Fin.ext
        simpa using hf.symm
      have hj' : (⟨i.val + 1, hridx⟩ : Fin (m + 2)) = j := by
        apply Fin.ext
        exact hf
      rw [hj'] at hprod
      rcases hbond with h11 | h12 | h21 | h13 | h31
      · exact h11
      · simp [h12.1, h12.2] at hprod
      · simp [h21.1, h21.2] at hprod
      · simp [h13.1, h13.2] at hprod
      · simp [h31.1, h31.2] at hprod
    · have hridx : j.val + 1 < m + 2 := by omega
      have hri : j.val ≠ r := by
        intro hj
        apply hnot₂
        exact ⟨hj, by omega⟩
      have hprod := hoff j.val hridx hri
      have hi : i = (⟨j.val + 1, hridx⟩ : Fin (m + 2)) := by
        apply Fin.ext
        simpa using hb.symm
      have hi' : (⟨j.val + 1, hridx⟩ : Fin (m + 2)) = i := by
        apply Fin.ext
        exact hb
      rw [hi'] at hprod
      rcases hbond with h11 | h12 | h21 | h13 | h31
      · exact h11
      · simp [h12.1, h12.2] at hprod
      · simp [h21.1, h21.2] at hprod
      · simp [h13.1, h13.2] at hprod
      · simp [h31.1, h31.2] at hprod
  have hentries : ∀ i j : Fin (m + 2), A (e i) (e j) =
      if i = j then 2 else if i.val + 1 = j.val then
        if i.val = r then u else -1
      else if j.val + 1 = i.val then
        if j.val = r then v else -1
      else 0 := by
    exact cartan_pathGraph_entries_of_unique_doubleBond A hdiag hrank e hpath hr u v
      (by simp [u]) (by simp [v]) hsimple
  have hprod : u * v = 2 ∨ u * v = 3 := by
    rcases hrank (e ⟨r, by omega⟩) (e ⟨r + 1, hr⟩) hroot with h0 | h11 | h12 | h21 | h13 | h31
    · norm_num [u, v, h0.1, h0.2] at hheavy
    · norm_num [u, v, h11.1, h11.2] at hheavy
    · exact Or.inl (by simp [u, v, h12.1, h12.2])
    · exact Or.inl (by simp [u, v, h21.1, h21.2])
    · exact Or.inr (by simp [u, v, h13.1, h13.2])
    · exact Or.inr (by simp [u, v, h31.1, h31.2])
  rcases hprod with hdouble | htriple
  · have horient : (u = -2 ∧ v = -1) ∨ (u = -1 ∧ v = -2) := by
      rcases hrank (e ⟨r, by omega⟩) (e ⟨r + 1, hr⟩) hroot with h0 | h11 | h12 | h21 | h13 | h31
      · norm_num [u, v, h0.1, h0.2] at hdouble
      · norm_num [u, v, h11.1, h11.2] at hdouble
      · exact Or.inr (by simpa [u, v] using h12)
      · exact Or.inl (by simpa [u, v] using h21)
      · norm_num [u, v, h13.1, h13.2] at hdouble
      · norm_num [u, v, h31.1, h31.2] at hdouble
    by_cases hr0 : r = 0
    · subst r
      rcases cartan_path_initial_doubleBond_is_typeB_or_typeC A m e u v hentries horient with hB | hC
      · exact Or.inl hB
      · exact Or.inr (Or.inl hC)
    by_cases hrlast : r + 1 = m + 1
    · have hrt : r = m := by omega
      subst r
      rcases cartan_path_terminal_doubleBond_is_typeB_or_typeC A m e u v hentries horient with hB | hC
      · exact Or.inl ⟨e, hB⟩
      · exact Or.inr (Or.inl ⟨e, hC⟩)
    have hleft : 0 < r := by omega
    have hright : r + 2 < m + 2 := by omega
    have hmid := cartan_path_internal_heavy_eq_middle_four_of_diagonal_mul_posDef
      A d hpos e u v hentries hdouble hleft hright
    rcases hmid with ⟨hm, hrone⟩
    have hm2 : m = 2 := by omega
    subst m
    rcases cartan_path_middle_doubleBond_is_typeF4 A e u v
      (by simpa [hrone] using hentries) horient with hF4
    exact Or.inr (Or.inr (Or.inl hF4))
  · let ha : κ := e ⟨r, by omega⟩
    let hb : κ := e ⟨r + 1, hr⟩
    have hab : ha ≠ hb := by
      intro h
      have heq : (⟨r, by omega⟩ : Fin (m + 2)) = ⟨r + 1, hr⟩ := by
        apply e.injective
        exact h
      omega
    have hprodab : A ha hb * A hb ha = 3 := by
      change A (e ⟨r, by omega⟩) (e ⟨r + 1, hr⟩) *
        A (e ⟨r + 1, hr⟩) (e ⟨r, by omega⟩) = 3
      exact htriple
    exact Or.inr (Or.inr (Or.inr (cartan_tripleBond_isG2 A d hdiag hrank hconn hpos
      ha hb hab hprodab)))

open SimpleGraph StandardRootSystem

/-- A positive-definite Cartan matrix whose support is numbered by a path is
of type A, B, C, F₄, or G₂.  The finite path numbering and the case split are
ordinary theorem data; no classification conclusion is stored in a structure
or definition. -/
public theorem cartan_pathGraph_classification_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef)
    {n : ℕ} (e : Fin n ≃ κ)
    (hpath : ∀ i j,
      (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj (e i) (e j) ↔
        (pathGraph n).Adj i j) :
    (∃ e' : Fin n ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeACartanMatrix n i j) ∨
    (∃ m : ℕ, ∃ e' : Fin (m + 2) ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeBCartanMatrix m i j) ∨
    (∃ m : ℕ, ∃ e' : Fin (m + 1) ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeCCartanMatrix m i j) ∨
    (∃ e' : Fin 4 ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeF4CartanMatrix i j) ∨
    (∃ e' : Fin 2 ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeG2CartanMatrix i j) := by
  classical
  by_cases hno : ∀ (q : ℕ) (hq : q + 1 < n),
      A (e ⟨q, by omega⟩) (e ⟨q + 1, hq⟩) *
        A (e ⟨q + 1, hq⟩) (e ⟨q, by omega⟩) ≤ 1
  · have hsimple : ∀ {i j : Fin n}, (pathGraph n).Adj i j →
        A (e i) (e j) = -1 ∧ A (e j) (e i) = -1 := by
      intro i j hadj
      have hbond := cartan_pathGraph_adjacent_rankTwoBond A hrank e hpath hadj
      rw [pathGraph_adj] at hadj
      rcases hadj with hf | hb
      · have hq : i.val + 1 < n := by omega
        have hprod := hno i.val hq
        have hj : j = (⟨i.val + 1, hq⟩ : Fin n) := by
          apply Fin.ext
          simpa using hf.symm
        have hprod' : A (e i) (e j) * A (e j) (e i) ≤ 1 := by
          rw [hj]
          exact hprod
        rcases hbond with h11 | h12 | h21 | h13 | h31
        · exact h11
        · simp [h12.1, h12.2] at hprod'
        · simp [h21.1, h21.2] at hprod'
        · simp [h13.1, h13.2] at hprod'
        · simp [h31.1, h31.2] at hprod'
      · have hq : j.val + 1 < n := by omega
        have hprod := hno j.val hq
        have hi : i = (⟨j.val + 1, hq⟩ : Fin n) := by
          apply Fin.ext
          simpa using hb.symm
        have hprod' : A (e i) (e j) * A (e j) (e i) ≤ 1 := by
          simpa [hi, mul_comm] using hprod
        rcases hbond with h11 | h12 | h21 | h13 | h31
        · exact h11
        · simp [h12.1, h12.2] at hprod'
        · simp [h21.1, h21.2] at hprod'
        · simp [h13.1, h13.2] at hprod'
        · simp [h31.1, h31.2] at hprod'
    exact Or.inl ⟨e, cartan_pathGraph_eq_typeACartanMatrix_of_simple_bonds
      A hdiag e hpath hsimple⟩
  · push Not at hno
    rcases hno with ⟨r, hr, hheavy⟩
    have hn2 : 2 ≤ n := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn2
    have hmn : m + 2 = n := by omega
    let c : Fin (m + 2) ≃ Fin n := finCongr hmn
    let e' : Fin (m + 2) ≃ κ := c.trans e
    have hpath' : ∀ i j,
        (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj (e' i) (e' j) ↔
          (pathGraph (m + 2)).Adj i j := by
      intro i j
      simpa [e', c, pathGraph_adj] using hpath (c i) (c j)
    let edgeProd : ℕ → ℤ := fun q =>
      if hq : q + 1 < n then
        A (e ⟨q, by omega⟩) (e ⟨q + 1, hq⟩) *
          A (e ⟨q + 1, hq⟩) (e ⟨q, by omega⟩)
      else 0
    let heavy : ℕ → Prop := fun q => q + 1 < n ∧ 2 ≤ edgeProd q
    have hex : ∃ q, heavy q := by
      refine ⟨r, hr, ?_⟩
      have hprod : 1 < edgeProd r := by
        simpa [edgeProd, hr] using hheavy
      omega
    let p := Nat.find hex
    have hpheavy : heavy p := Nat.find_spec hex
    have hpb : p + 1 < n := hpheavy.1
    have hpp : 2 ≤ A (e ⟨p, by omega⟩) (e ⟨p + 1, by omega⟩) *
        A (e ⟨p + 1, by omega⟩) (e ⟨p, by omega⟩) := by
      have hpp0 : 2 ≤ edgeProd p := hpheavy.2
      simpa [edgeProd, hpb] using hpp0
    have hsecond : ¬ ∃ q, p < q ∧ heavy q := by
      intro hexq
      let q := Nat.find hexq
      have hqheavy : heavy q := (Nat.find_spec hexq).2
      have hpq : p < q := (Nat.find_spec hexq).1
      have hqbound : q + 1 < n := hqheavy.1
      let u := A (e ⟨p, by omega⟩) (e ⟨p + 1, by omega⟩)
      let v := A (e ⟨p + 1, by omega⟩) (e ⟨p, by omega⟩)
      let s := A (e ⟨q, by omega⟩) (e ⟨q + 1, by omega⟩)
      let t := A (e ⟨q + 1, by omega⟩) (e ⟨q, by omega⟩)
      have hqq : 2 ≤ s * t := by
        have hqq0 : 2 ≤ edgeProd q := hqheavy.2
        simpa [s, t, edgeProd, hqbound] using hqq0
      have hsimple_mid : ∀ {i j : Fin n}, (pathGraph n).Adj i j →
          i.val + 1 = j.val →
          p ≤ i.val → i.val ≤ q + 1 → p ≤ j.val → j.val ≤ q + 1 →
          p < i.val → i.val < q →
          A (e i) (e j) = -1 ∧ A (e j) (e i) = -1 := by
        intro i j hadj hf hil hiu hjl hju hip hiq
        have hbond := cartan_pathGraph_adjacent_rankTwoBond A hrank e hpath hadj
        have hk : i.val + 1 < n := by omega
        have hnot : ¬ heavy i.val := by
          intro hh
          have hle : q ≤ i.val := Nat.find_min' hexq ⟨by omega, hh⟩
          omega
        have hprod : A (e i) (e j) * A (e j) (e i) ≤ 1 := by
          by_contra hgt
          apply hnot
          have hprod2 : 2 ≤ A (e i) (e j) * A (e j) (e i) := by omega
          have hj : j = (⟨i.val + 1, hk⟩ : Fin n) := by
            apply Fin.ext
            simpa using hf.symm
          rw [hj] at hprod2
          exact ⟨hk, by simpa [edgeProd, hk, mul_comm, Fin.eta] using hprod2⟩
        rcases hbond with h11 | h12 | h21 | h13 | h31
        · exact h11
        · simp [h12.1, h12.2] at hprod
        · simp [h21.1, h21.2] at hprod
        · simp [h13.1, h13.2] at hprod
        · simp [h31.1, h31.2] at hprod
      by_cases hgap : p + 1 < q
      · have hAint : ∀ (i j : Fin n), p ≤ i.val → i.val ≤ q + 1 →
            p ≤ j.val → j.val ≤ q + 1 →
            A (e i) (e j) =
              if i = j then 2 else if i.val + 1 = j.val then
                if i.val = p then u else if i.val = q then s else -1
              else if j.val + 1 = i.val then
                if j.val = p then v else if j.val = q then t else -1
              else 0 := by
          intro i j hil hiu hjl hju
          by_cases hij : i = j
          · subst j
            simp [hdiag]
          by_cases hf : i.val + 1 = j.val
          · rw [if_neg hij, if_pos hf]
            by_cases hip : i.val = p
            · have hi : i = (⟨p, by omega⟩ : Fin n) := Fin.ext (by simpa using hip)
              have hj : j = (⟨p + 1, by omega⟩ : Fin n) := by
                apply Fin.ext
                simpa [hip] using hf.symm
              have hentry : A (e i) (e j) = u := by
                simp [u, hi, hj]
              simpa [hip] using hentry
            by_cases hiq : i.val = q
            · have hi : i = (⟨q, by omega⟩ : Fin n) := Fin.ext (by simpa using hiq)
              have hj : j = (⟨q + 1, hqbound⟩ : Fin n) := by
                apply Fin.ext
                simpa [hiq] using hf.symm
              have hentry : A (e i) (e j) = s := by
                simp [s, hi, hj]
              have hqp : q ≠ p := by omega
              simpa [hiq, hqp] using hentry
            have hadj : (pathGraph n).Adj i j := by
              rw [pathGraph_adj]
              exact Or.inl hf
            have hs := hsimple_mid hadj hf hil hiu hjl hju (by omega) (by omega)
            simpa [hip, hiq] using hs.1
          by_cases hb : j.val + 1 = i.val
          · rw [if_neg hij, if_neg hf, if_pos hb]
            by_cases hjp : j.val = p
            · have hj : j = (⟨p, by omega⟩ : Fin n) := Fin.ext (by simpa using hjp)
              have hi : i = (⟨p + 1, by omega⟩ : Fin n) := by
                apply Fin.ext
                simpa [hjp] using hb.symm
              have hentry : A (e i) (e j) = v := by
                simp [v, hi, hj]
              simpa [hjp] using hentry
            by_cases hjq : j.val = q
            · have hj : j = (⟨q, by omega⟩ : Fin n) := Fin.ext (by simpa using hjq)
              have hi : i = (⟨q + 1, hqbound⟩ : Fin n) := by
                apply Fin.ext
                simpa [hjq] using hb.symm
              have hentry : A (e i) (e j) = t := by
                simp [t, hi, hj]
              have hqp : q ≠ p := by omega
              simpa [hqp, hjq] using hentry
            have hadj : (pathGraph n).Adj i j := by
              rw [pathGraph_adj]
              exact Or.inr hb
            have hs := hsimple_mid hadj.symm hb hjl hju hil hiu (by omega) (by omega)
            simpa [hjp, hjq] using hs.2
          rw [if_neg hij, if_neg hf, if_neg hb]
          exact (cartan_pathGraph_nonadjacent_entries_eq_zero
            A hrank e hpath hij (by simp [pathGraph_adj, hf, hb])).1
        have hfalse := not_cartan_path_two_heavy_edges_of_bounded_interval
          A d hpos e.toEmbedding hqbound hgap u v s t hAint hpp hqq
        exact hfalse.elim
      · have hqp1 : q = p + 1 := by omega
        let c0 : κ := e ⟨p + 1, by omega⟩
        let a0 : κ := e ⟨p, by omega⟩
        let b0 : κ := e ⟨q + 1, by omega⟩
        have hca0 : c0 ≠ a0 := by
          intro h
          change e (⟨p + 1, by omega⟩ : Fin n) = e ⟨p, by omega⟩ at h
          have hfin : (⟨p + 1, by omega⟩ : Fin n) = ⟨p, by omega⟩ := e.injective h
          have hv : p + 1 = p := by simpa using congrArg Fin.val hfin
          omega
        have hcb0 : c0 ≠ b0 := by
          intro h
          change e (⟨p + 1, by omega⟩ : Fin n) = e ⟨q + 1, by omega⟩ at h
          have hfin : (⟨p + 1, by omega⟩ : Fin n) = ⟨q + 1, by omega⟩ := e.injective h
          have hv := congrArg Fin.val hfin
          simp [hqp1] at hv
        have hab0 : a0 ≠ b0 := by
          intro h
          change e (⟨p, by omega⟩ : Fin n) = e ⟨q + 1, by omega⟩ at h
          have hfin : (⟨p, by omega⟩ : Fin n) = ⟨q + 1, by omega⟩ := e.injective h
          have hv := congrArg Fin.val hfin
          simp [hqp1] at hv
          omega
        have hce : Function.Injective ![c0, a0, b0] := by
          intro i j hij
          fin_cases i <;> fin_cases j
          · rfl
          · exact (hca0 (by simpa using hij)).elim
          · exact (hcb0 (by simpa using hij)).elim
          · exact (hca0 (by simpa using hij.symm)).elim
          · rfl
          · exact (hab0 (by simpa using hij)).elim
          · exact (hcb0 (by simpa using hij.symm)).elim
          · exact (hab0 (by simpa using hij.symm)).elim
          · rfl
        have hv0 : v ≠ 0 := by
          intro hv
          have hv' : A (e ⟨p + 1, by omega⟩) (e ⟨p, by omega⟩) = 0 := by
            simpa [v] using hv
          rw [hv'] at hpp
          norm_num at hpp
        have hs0 : s ≠ 0 := by
          intro hs
          have hz : s * t = 0 := by simp [hs]
          nlinarith [hqq, hz]
        have hca : A c0 a0 ≠ 0 := by
          change A (e ⟨p + 1, by omega⟩) (e ⟨p, by omega⟩) ≠ 0
          simpa [v] using hv0
        have hcb : A c0 b0 ≠ 0 := by
          change A (e ⟨p + 1, by omega⟩) (e ⟨q + 1, by omega⟩) ≠ 0
          simpa [hqp1, s] using hs0
        have hfalse := not_cartan_two_heavy_edges_of_diagonal_mul_posDef
          A d hdiag hrank hpos c0 a0 b0 hce hca hcb (by
            simpa [c0, a0, u, v, mul_comm] using hpp) (by
            simpa [c0, b0, s, t, hqp1] using hqq)
        exact hfalse.elim
    have huniq : ∀ q, heavy q → q = p := by
      intro q hq
      by_cases hqp : q = p
      · exact hqp
      · have hpq : p < q := by
          have hle : p ≤ q := Nat.find_min' hex hq
          omega
        exact False.elim (hsecond ⟨q, hpq, hq⟩)
    have hpr : p + 1 < m + 2 := by omega
    have hheavy_p' : 2 ≤ A (e' ⟨p, by omega⟩) (e' ⟨p + 1, hpr⟩) *
        A (e' ⟨p + 1, hpr⟩) (e' ⟨p, by omega⟩) := by
      simpa [e', c, hmn] using hpp
    have hoff : ∀ q (hq : q + 1 < m + 2), q ≠ p →
        A (e' ⟨q, by omega⟩) (e' ⟨q + 1, hq⟩) *
          A (e' ⟨q + 1, hq⟩) (e' ⟨q, by omega⟩) ≤ 1 := by
      intro q hq hqp
      have hqn : q + 1 < n := by omega
      by_contra hgt
      have hheavyq : heavy q := by
        refine ⟨hqn, ?_⟩
        have hprod : 2 ≤ A (e' ⟨q, by omega⟩) (e' ⟨q + 1, hq⟩) *
            A (e' ⟨q + 1, hq⟩) (e' ⟨q, by omega⟩) := by omega
        simpa [e', c, edgeProd, hqn, hq] using hprod
      have hpeq := huniq q hheavyq
      exact hqp hpeq
    rcases cartan_path_single_heavy_case_split A d hdiag hrank hconn hpos
      e' hpath' hpr hoff hheavy_p' with hB | hC | hF | hG
    · rcases hB with ⟨eB, hBeq⟩
      exact Or.inr (Or.inl ⟨m, eB, hBeq⟩)
    · rcases hC with ⟨eC, hCeq⟩
      exact Or.inr (Or.inr (Or.inl ⟨m + 1, eC, hCeq⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hF)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hG)))

open StandardRootSystem

/-- Every nonempty finite connected positive-definite integral Cartan matrix
with the crystallographic rank-two entries is, after renumbering, one of the
nine finite irreducible Cartan types. -/
public theorem finiteCartanMatrix_classification_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef) :
    (∃ m : ℕ, ∃ e : Fin m ≃ κ,
      ∀ i j, A (e i) (e j) = typeACartanMatrix m i j) ∨
    (∃ m : ℕ, ∃ e : Fin (m + 2) ≃ κ,
      ∀ i j, A (e i) (e j) = typeBCartanMatrix m i j) ∨
    (∃ m : ℕ, ∃ e : Fin (m + 1) ≃ κ,
      ∀ i j, A (e i) (e j) = typeCCartanMatrix m i j) ∨
    (∃ m : ℕ, ∃ e : Fin (m + 2) ≃ κ,
      ∀ i j, A (e i) (e j) = typeDCartanMatrix m i j) ∨
    (∃ e : Fin 6 ≃ κ,
      ∀ i j, A (e i) (e j) = typeE6CartanMatrix i j) ∨
    (∃ e : Fin 7 ≃ κ,
      ∀ i j, A (e i) (e j) = typeE7CartanMatrix i j) ∨
    (∃ e : Fin 8 ≃ κ,
      ∀ i j, A (e i) (e j) = typeE8CartanMatrix i j) ∨
    (∃ e : Fin 4 ≃ κ,
      ∀ i j, A (e i) (e j) = typeF4CartanMatrix i j) ∨
    (∃ e : Fin 2 ≃ κ,
      ∀ i j, A (e i) (e j) = typeG2CartanMatrix i j) := by
  classical
  rcases cartanSupport_exists_degree_three_or_pathGraph_numbering
    A d hdiag hrank hconn hpos with ⟨c, hc⟩ | ⟨n, e, hpath⟩
  · let G : SimpleGraph κ := SimpleGraph.fromRel fun i j => A i j ≠ 0
    have htree : G.IsTree := by
      simpa [G] using cartanSupport_isTree A d hdiag hrank hconn hpos
    have hdegree : ∀ v, G.degree v ≤ 3 := by
      intro v
      simpa [G] using cartanSupport_degree_le_three A d hdiag hrank hpos v
    have huniq : ∀ v, G.degree v = 3 → v = c := by
      intro v hv
      exact cartanSupport_degree_three_unique_of_diagonal_mul_posDef
        A d hdiag hrank hconn hpos v c (by simpa [G] using hv) hc
    obtain ⟨a, ha, n0, n1, n2, e, hec, hea0, hea1, hea2,
        hcenter0, hcenter1, hcenter2, hpath0, hpath1, hpath2,
        hcross01, hcross02, hcross12⟩ :=
      simpleGraph_tree_three_arm_global_sigma_numbering
        G htree c hdegree (by simpa [G] using hc) huniq
    have hdeg : G.degree (e none) = 3 := by
      rw [hec]
      simpa [G] using hc
    rcases cartan_three_arm_classification_of_diagonal_mul_posDef
      A d hdiag hrank hpos e
      (by simpa [G] using hcenter0)
      (by simpa [G] using hcenter1)
      (by simpa [G] using hcenter2)
      (by simpa [G] using hpath0)
      (by simpa [G] using hpath1)
      (by simpa [G] using hpath2)
      (by simpa [G] using hcross01)
      (by simpa [G] using hcross02)
      (by simpa [G] using hcross12)
      (by simpa [G] using hdeg) with hD | hE6 | hE7 | hE8
    · exact Or.inr (Or.inr (Or.inr (Or.inl hD)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE6))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE7)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE8))))))
  · rcases cartan_pathGraph_classification_of_diagonal_mul_posDef
      A d hdiag hrank hconn hpos e hpath with hA | hB | hC | hF4 | hG2
    · exact Or.inl ⟨n, hA⟩
    · exact Or.inr (Or.inl hB)
    · exact Or.inr (Or.inr (Or.inl hC))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl hF4)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr hG2)))))))

/-- Conditional classification core for Theorem 1.8.7.

An external classification theorem for finite connected symmetrizable
positive-definite integral Cartan matrices specializes to the Cartan matrix of
an irreducible reduced crystallographic root system.  The premise is a theorem
about arbitrary matrices; it does not store a classification conclusion in a
definition or structure. -/
public theorem rootSystem_finiteCartanClassification_of_matrix_classifier
    {ι : Type u} {M : Type v} {N : Type w} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] (b : P.Base)
    (classify :
      ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℤ),
        (∀ i, A i i = 2) →
        (∀ i j, i ≠ j →
          (A i j = 0 ∧ A j i = 0) ∨
          (A i j = -1 ∧ A j i = -1) ∨
          (A i j = -1 ∧ A j i = -2) ∨
          (A i j = -2 ∧ A j i = -1) ∨
          (A i j = -1 ∧ A j i = -3) ∨
          (A i j = -3 ∧ A j i = -1)) →
        (∀ (p : κ → Prop) {i j : κ}, p i →
          (∀ i j, p i → A j i ≠ 0 → p j) → p j) →
        (∃ d : κ → ℤ, (∀ i, 0 < d i) ∧
          (Matrix.diagonal d * A).PosDef) →
        (∃ m : ℕ, ∃ e : Fin m ≃ κ,
          ∀ i j, A (e i) (e j) = typeACartanMatrix m i j) ∨
        (∃ m : ℕ, ∃ e : Fin (m + 2) ≃ κ,
          ∀ i j, A (e i) (e j) = typeBCartanMatrix m i j) ∨
        (∃ m : ℕ, ∃ e : Fin (m + 1) ≃ κ,
          ∀ i j, A (e i) (e j) = typeCCartanMatrix m i j) ∨
        (∃ m : ℕ, ∃ e : Fin (m + 2) ≃ κ,
          ∀ i j, A (e i) (e j) = typeDCartanMatrix m i j) ∨
        (∃ e : Fin 6 ≃ κ,
          ∀ i j, A (e i) (e j) = typeE6CartanMatrix i j) ∨
        (∃ e : Fin 7 ≃ κ,
          ∀ i j, A (e i) (e j) = typeE7CartanMatrix i j) ∨
        (∃ e : Fin 8 ≃ κ,
          ∀ i j, A (e i) (e j) = typeE8CartanMatrix i j) ∨
        (∃ e : Fin 4 ≃ κ,
          ∀ i j, A (e i) (e j) = typeF4CartanMatrix i j) ∨
        (∃ e : Fin 2 ≃ κ,
          ∀ i j, A (e i) (e j) = typeG2CartanMatrix i j)) :
    (∃ m : ℕ, ∃ e : Fin m ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeACartanMatrix m i j) ∨
    (∃ m : ℕ, ∃ e : Fin (m + 2) ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeBCartanMatrix m i j) ∨
    (∃ m : ℕ, ∃ e : Fin (m + 1) ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeCCartanMatrix m i j) ∨
    (∃ m : ℕ, ∃ e : Fin (m + 2) ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeDCartanMatrix m i j) ∨
    (∃ e : Fin 6 ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeE6CartanMatrix i j) ∨
    (∃ e : Fin 7 ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeE7CartanMatrix i j) ∨
    (∃ e : Fin 8 ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeE8CartanMatrix i j) ∨
    (∃ e : Fin 4 ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeF4CartanMatrix i j) ∨
    (∃ e : Fin 2 ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeG2CartanMatrix i j) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  apply classify b.cartanMatrix
  · exact b.cartanMatrix_apply_same
  · exact base_rankTwo_cartanClassification b
  · intro p i j hi hp
    exact b.induction_on_cartanMatrix p hi hp
  · exact b.exists_cartanMatrix_diagaonal_mul_posDef

/-- The Cartan matrix of a base of a finite irreducible reduced
crystallographic root system is, after renumbering, one of the nine finite
irreducible Cartan types. -/
public theorem rootSystem_finiteCartanClassification
    {ι : Type u} {M : Type v} {N : Type w} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] (b : P.Base) :
    (∃ m : ℕ, ∃ e : Fin m ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeACartanMatrix m i j) ∨
    (∃ m : ℕ, ∃ e : Fin (m + 2) ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeBCartanMatrix m i j) ∨
    (∃ m : ℕ, ∃ e : Fin (m + 1) ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeCCartanMatrix m i j) ∨
    (∃ m : ℕ, ∃ e : Fin (m + 2) ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeDCartanMatrix m i j) ∨
    (∃ e : Fin 6 ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeE6CartanMatrix i j) ∨
    (∃ e : Fin 7 ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeE7CartanMatrix i j) ∨
    (∃ e : Fin 8 ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeE8CartanMatrix i j) ∨
    (∃ e : Fin 4 ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeF4CartanMatrix i j) ∨
    (∃ e : Fin 2 ≃ b.support,
      ∀ i j, b.cartanMatrix (e i) (e j) = typeG2CartanMatrix i j) := by
  classical
  apply rootSystem_finiteCartanClassification_of_matrix_classifier b
  intro κ _ _ A hdiag hrank hconn hsymm
  obtain ⟨d, hd, hpos⟩ := hsymm
  by_cases hκ : Nonempty κ
  · let : Nonempty κ := hκ
    exact finiteCartanMatrix_classification_of_diagonal_mul_posDef
      A d hdiag hrank hconn hpos
  · let : IsEmpty κ := ⟨fun x => hκ ⟨x⟩⟩
    refine Or.inl ⟨0, Equiv.equivOfIsEmpty (Fin 0) κ, ?_⟩
    intro i
    exact isEmptyElim i

public theorem theorem_1_8_7
    {ι ι₂ R M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
    {Q : RootPairing ι₂ R M₂ N₂} [Q.IsRootSystem]
    [Q.IsCrystallographic] [Q.IsReduced] (b₂ : Q.Base)
    (f : b.support ≃ b₂.support) :
    (∃ e : P.Equiv Q,
      ∀ i : b.support, e.indexEquiv i = (f i : ι₂)) ↔
      ∃ d : P.DynkinDiagramIso b.support Q b₂.support,
        d.toEquiv = f := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨⟨f, ?_⟩, rfl⟩
    intro i j
    apply FaithfulSMul.algebraMap_injective ℤ R
    simp only [RootPairing.dynkinDiagramOn,
      RootPairing.algebraMap_pairingIn]
    have h := RootPairing.Equiv.pairing_eq e i.1 j.1
    simpa [he i, he j] using h
  · rintro ⟨d, hd⟩
    have hcartan : ∀ i j, b₂.cartanMatrix (d.toEquiv i) (d.toEquiv j) =
        b.cartanMatrix i j := by
      intro i j
      change Q.pairingIn ℤ (d.toEquiv i) (d.toEquiv j) =
        P.pairingIn ℤ i j
      simpa [RootPairing.dynkinDiagramOn] using d.map_entry i j
    let e : P.Equiv Q := b.equivOfCartanMatrixEq b₂ d.toEquiv hcartan
    refine ⟨e, ?_⟩
    intro i
    have he : e.toHom.indexEquiv i = d.toEquiv i := by
      apply Q.root.injective
      rw [← RootPairing.Hom.root_weightMap_apply P Q i e.toHom]
      change (b.toWeightBasis.equiv b₂.toWeightBasis d.toEquiv) (P.root i) =
        Q.root (d.toEquiv i)
      simp [Module.Basis.equiv]
    rw [he, hd]

end Theory.AlgebraicGroup
