module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import Theory.AlgebraicGroup.RootSystems.Defs

/-! Standard Dynkin Cartan tables and their realization by root-pairing bases. -/

namespace Theory.AlgebraicGroup

@[expose]
public def dynkinCartanEntry (R : RootClassification)
    (i j : Fin R.rank) : ℤ :=
  if i = j then 2 else
    match R.kind with
    | .A => if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0
    | .B =>
        if i.val + 1 = j.val then
          if j.val + 1 = R.rank then -2 else -1
        else if j.val + 1 = i.val then -1 else 0
    | .C =>
        if i.val + 1 = j.val then -1
        else if j.val + 1 = i.val then
          if i.val + 1 = R.rank then -2 else -1
        else 0
    | .D =>
        if (i.val + 1 = j.val ∧ j.val + 2 < R.rank) ∨
            (j.val + 1 = i.val ∧ i.val + 2 < R.rank) ∨
            (i.val + 3 = R.rank ∧
              (j.val + 2 = R.rank ∨ j.val + 1 = R.rank)) ∨
            (j.val + 3 = R.rank ∧
              (i.val + 2 = R.rank ∨ i.val + 1 = R.rank)) then -1 else 0
    | .E6 =>
        if R.rank = 6 then
          if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
              (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
              (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
              (i.val = 2 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 2) ∨
              (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4)
            then -1 else 0
        else 0
    | .E7 =>
        if R.rank = 7 then
          if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
              (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
              (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
              (i.val = 2 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 2) ∨
              (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4) ∨
              (i.val = 5 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 5)
            then -1 else 0
        else 0
    | .E8 =>
        if R.rank = 8 then
          if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
              (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
              (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
              (i.val = 2 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 2) ∨
              (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4) ∨
              (i.val = 5 ∧ j.val = 6) ∨ (i.val = 6 ∧ j.val = 5) ∨
              (i.val = 6 ∧ j.val = 7) ∨ (i.val = 7 ∧ j.val = 6)
            then -1 else 0
        else 0
    | .F4 =>
        if R.rank = 4 then
          if i.val + 1 = j.val then
            if i.val = 1 then -2 else -1
          else if j.val + 1 = i.val then -1 else 0
        else 0
    | .G2 =>
        if R.rank = 2 then
          if i.val = 0 ∧ j.val = 1 then -1 else
            if j.val = 0 ∧ i.val = 1 then -3 else 0
        else 0

@[expose]
public def HasDynkinType
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (C : RootClassification) : Prop :=
  ∃ b : P.Base, ∃ e : b.support ≃ Fin C.rank,
    ∀ i j, b.cartanMatrixIn ℤ i j = dynkinCartanEntry C (e i) (e j)

public lemma dynkinCartanEntry_A_symmetric (m : ℕ) :
    ∀ i j : Fin m,
      dynkinCartanEntry ⟨.A, m⟩ i j = dynkinCartanEntry ⟨.A, m⟩ j i := by
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · simp only [dynkinCartanEntry, hij, ↓reduceIte]
    by_cases h₁ : i.val + 1 = j.val
    · have h₂ : ¬ j.val + 1 = i.val := by omega
      simp [h₁, h₂, hij, eq_comm]
    · by_cases h₂ : j.val + 1 = i.val
      · simp [h₁, h₂, hij, eq_comm]
      · simp [h₁, h₂, hij, eq_comm]

public lemma dynkinCartanEntry_D_symmetric_any_rank (n : ℕ) :
    ∀ i j : Fin n,
      dynkinCartanEntry ⟨.D, n⟩ i j = dynkinCartanEntry ⟨.D, n⟩ j i := by
  intro i j
  simp only [dynkinCartanEntry]
  split <;> rename_i h1
  all_goals try split <;> try rename_i h2
  all_goals try split <;> try rename_i h3
  all_goals try split <;> try rename_i h4
  all_goals simp_all [eq_comm] <;> omega

public lemma dynkinCartanEntry_E6_symmetric_any_rank (n : ℕ) :
    ∀ i j : Fin n,
      dynkinCartanEntry ⟨.E6, n⟩ i j = dynkinCartanEntry ⟨.E6, n⟩ j i := by
  intro i j
  by_cases hn : n = 6
  · subst n
    fin_cases i <;> fin_cases j <;> rfl
  · by_cases hij : i = j
    · subst j
      simp [dynkinCartanEntry]
    · simp only [dynkinCartanEntry, hn, hij, ↓reduceIte]
      by_cases hji : j = i
      · exact (hij (Eq.symm hji)).elim
      · simp [hji]

public lemma dynkinCartanEntry_E7_symmetric_any_rank (n : ℕ) :
    ∀ i j : Fin n,
      dynkinCartanEntry ⟨.E7, n⟩ i j = dynkinCartanEntry ⟨.E7, n⟩ j i := by
  intro i j
  by_cases hn : n = 7
  · subst n
    fin_cases i <;> fin_cases j <;> rfl
  · by_cases hij : i = j
    · subst j
      simp [dynkinCartanEntry]
    · simp only [dynkinCartanEntry, hn, hij, ↓reduceIte]
      by_cases hji : j = i
      · exact (hij (Eq.symm hji)).elim
      · simp [hji]

public lemma dynkinCartanEntry_E8_symmetric_any_rank (n : ℕ) :
    ∀ i j : Fin n,
      dynkinCartanEntry ⟨.E8, n⟩ i j = dynkinCartanEntry ⟨.E8, n⟩ j i := by
  intro i j
  by_cases hn : n = 8
  · subst n
    fin_cases i <;> fin_cases j <;> rfl
  · by_cases hij : i = j
    · subst j
      simp [dynkinCartanEntry]
    · simp only [dynkinCartanEntry, hn, hij, ↓reduceIte]
      by_cases hji : j = i
      · exact (hij (Eq.symm hji)).elim
      · simp [hji]

set_option maxHeartbeats 800000 in
/-- A Cartan-connected base forces irreducibility.  The connectivity premise
is independent of any classification witness; it records exactly the Dynkin
graph input used by the reflection-invariant-submodule argument. -/
public theorem isIrreducible_of_cartan_connected
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (hbase : b.support.Nonempty)
    (hconn : ∀ s t : b.support,
      Relation.ReflTransGen (fun u v : b.support => b.cartanMatrix u v ≠ 0) s t) :
    P.IsIrreducible := by
  let : Nonempty ι := ⟨(hbase.choose : ι)⟩
  let : Nontrivial M := nontrivial_of_ne (P.root hbase.choose) 0
    (P.ne_zero hbase.choose)
  apply RootPairing.IsIrreducible.mk' P
  intro q hq hqbot
  let q' : P.invtRootSubmodule := ⟨q, P.mem_invtRootSubmodule_iff.mpr hq⟩
  have hroot : ∃ i, P.root i ∈ q := by
    by_contra h
    apply hqbot
    have hq'bot : q' = ⊥ :=
      (RootPairing.invtRootSubmodule.eq_bot_iff q').mpr (by simpa using h)
    simpa [q'] using hq'bot
  obtain ⟨i, hi⟩ := hroot
  have hbaseRoot : ∃ s : b.support, P.root s ∈ q := by
    have hreflect : ∀ k j, P.root j ∈ q →
        P.root (P.reflectionPerm k j) ∈ q := by
      intro k j hj
      have hmap := (Module.End.mem_invtSubmodule_iff_mapsTo (P.reflection k)).mp
        (hq k) hj
      rw [P.root_reflectionPerm]
      exact hmap
    have hind : ∀ j, P.root j ∈ q → ∃ s : b.support, P.root s ∈ q := by
      intro j
      refine b.induction_reflect
        (p := fun j => P.root j ∈ q → ∃ s : b.support, P.root s ∈ q)
        j ?_ ?_ ?_
      · intro x hx hxr
        have hback : P.root x ∈ q := by
          have htmp := hreflect x (P.reflectionPerm x x) hxr
          simpa [P.reflectionPerm_self] using htmp
        exact hx hback
      · intro x hx hxr
        exact ⟨⟨x, hx⟩, hxr⟩
      · intro x k hx hk hxr
        have hback : P.root x ∈ q := by
          have htmp := hreflect k (P.reflectionPerm k x) hxr
          simpa [P.reflectionPerm_self] using htmp
        exact hx hback
    exact hind i hi
  obtain ⟨s, hs⟩ := hbaseRoot
  have hstep : ∀ {u v : b.support},
      Relation.ReflTransGen (fun x y : b.support => b.cartanMatrix x y ≠ 0) u v →
      P.root u ∈ q → P.root v ∈ q := by
    intro u v huv
    induction huv with
    | refl => intro hu; exact hu
    | @tail w z huv hstep ih =>
        intro hu
        have hw : P.root w ∈ q := ih hu
        have href : P.root (P.reflectionPerm z w) ∈ q := by
          have hmap := (Module.End.mem_invtSubmodule_iff_mapsTo (P.reflection z)).mp
            (hq z) hw
          rw [P.root_reflectionPerm]
          exact hmap
        have hpair : P.pairingIn ℤ w z ≠ 0 := by
          simpa [RootPairing.Base.cartanMatrixIn_def] using hstep
        have hsub : P.root w - (P.pairingIn ℤ w z : R) • P.root z ∈ q := by
          have href' : (P.reflection z) (P.root w) ∈ q := by
            rw [← P.root_reflectionPerm]
            exact href
          rw [P.reflection_apply_root] at href'
          simpa [← P.algebraMap_pairingIn ℤ w z] using href'
        have hne : (P.pairingIn ℤ w z : R) ≠ 0 := by
          exact_mod_cast hpair
        have hsmul : (P.pairingIn ℤ w z : R) • P.root z ∈ q :=
          (q.sub_mem_iff_right hw).mp hsub
        exact (q.smul_mem_iff hne).mp hsmul
  have hsupport : ∀ t : b.support, P.root t ∈ q := by
    intro t
    exact hstep (hconn s t) hs
  have hspan : P.rootSpan R ≤ q := by
    rw [← b.span_root_support]
    exact Submodule.span_le.mpr (by
      rintro _ ⟨t, ht, rfl⟩
      exact hsupport ⟨t, ht⟩)
  apply le_antisymm
  · exact le_top
  · rw [← RootPairing.IsRootSystem.span_root_eq_top (P := P)]
    exact hspan

set_option maxHeartbeats 800000 in
/-- A root pairing with the standard rank-two `G₂` Cartan matrix is irreducible.

The proof uses only the root-pairing API: a nonzero invariant submodule contains
a root, reflection induction reaches a simple root, and the two-node Cartan
matrix propagates membership to the other simple root. -/
public theorem isIrreducible_of_hasDynkinType_g2
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (hType : HasDynkinType P ⟨.G2, 2⟩) : P.IsIrreducible := by
  rcases hType with ⟨b, e, hbe⟩
  have hcard : b.support.card = 2 := by
    simpa using Fintype.card_congr e
  have hnonempty : b.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have : b.support.card = 0 := by simp [hzero]
    omega
  let : Nonempty ι := ⟨(hnonempty.choose : ι)⟩
  let : Nontrivial M := nontrivial_of_ne (P.root hnonempty.choose) 0
    (P.ne_zero hnonempty.choose)
  apply RootPairing.IsIrreducible.mk' P
  intro q hq hqbot
  let q' : P.invtRootSubmodule := ⟨q, P.mem_invtRootSubmodule_iff.mpr hq⟩
  have hroot : ∃ i, P.root i ∈ q := by
    by_contra h
    apply hqbot
    have hq'bot : q' = ⊥ :=
      (RootPairing.invtRootSubmodule.eq_bot_iff q').mpr (by simpa using h)
    simpa [q'] using hq'bot
  obtain ⟨i, hi⟩ := hroot
  have fin2_cases : ∀ z : Fin ({ kind := DynkinType.G2, rank := 2 } : RootClassification).rank,
      z = 0 ∨ z = 1 := by
    intro z
    have hlt := z.isLt
    change z.val < 2 at hlt
    have hz : z.val = 0 ∨ z.val = 1 := by omega
    rcases hz with hz | hz
    · exact Or.inl (Fin.ext hz)
    · exact Or.inr (Fin.ext hz)
  have hbase : ∃ i : b.support, P.root i ∈ q := by
    have hreflect : ∀ k j, P.root j ∈ q → P.root (P.reflectionPerm k j) ∈ q := by
      intro k j hj
      have hmap := (Module.End.mem_invtSubmodule_iff_mapsTo (P.reflection k)).mp (hq k) hj
      rw [P.root_reflectionPerm]
      exact hmap
    classical
    have hind : ∀ j, P.root j ∈ q → ∃ s : b.support, P.root s ∈ q := by
      intro j
      refine b.induction_reflect
        (p := fun j => P.root j ∈ q → ∃ s : b.support, P.root s ∈ q)
        j ?_ ?_ ?_
      · intro x hx hxr
        have hback : P.root x ∈ q := by
          have htmp := hreflect x (P.reflectionPerm x x) hxr
          simpa [P.reflectionPerm_self] using htmp
        exact hx hback
      · intro x hx hxr
        exact ⟨⟨x, hx⟩, hxr⟩
      · intro x k hx hk hxr
        have hback : P.root x ∈ q := by
          have htmp := hreflect k (P.reflectionPerm k x) hxr
          simpa [P.reflectionPerm_self] using htmp
        exact hx hback
    exact hind i hi
  obtain ⟨s, hs⟩ := hbase
  have htop : ∀ t : b.support, P.root t ∈ q := by
    intro t
    by_cases hst : t = s
    · simpa [hst] using hs
    · have hmat : b.cartanMatrixIn ℤ s t ≠ 0 := by
        rw [hbe]
        have ht_cases := fin2_cases (e t)
        have hs_cases := fin2_cases (e s)
        have hte : e t ≠ e s := e.injective.ne hst
        rcases ht_cases with ht0 | ht1 <;>
          rcases hs_cases with hs0 | hs1 <;>
            simp_all [dynkinCartanEntry]
      have hsref : P.root (P.reflectionPerm t s) ∈ q := by
        have hsref' := (Module.End.mem_invtSubmodule_iff_mapsTo (P.reflection t)).mp (hq t) hs
        rw [P.root_reflectionPerm]
        exact hsref'
      have hpair : P.pairingIn ℤ s t ≠ 0 := by
        simpa [RootPairing.Base.cartanMatrixIn_def] using hmat
      have hsub : P.root s - (P.pairingIn ℤ s t : R) • P.root t ∈ q := by
        have hsref' : (P.reflection t) (P.root s) ∈ q := by
          rw [← P.root_reflectionPerm]
          exact hsref
        rw [P.reflection_apply_root] at hsref'
        simpa [← P.algebraMap_pairingIn ℤ s t] using hsref'
      have hne : (P.pairingIn ℤ s t : R) ≠ 0 := by
        exact_mod_cast hpair
      have hsmul : (P.pairingIn ℤ s t : R) • P.root t ∈ q :=
        (q.sub_mem_iff_right hs).mp hsub
      exact (q.smul_mem_iff hne).mp hsmul
  have hspan : P.rootSpan R ≤ q := by
    rw [← b.span_root_support]
    exact Submodule.span_le.mpr (by
      rintro _ ⟨t, ht, rfl⟩
      exact htop ⟨t, ht⟩)
  apply le_antisymm
  · exact le_top
  · rw [← RootPairing.IsRootSystem.span_root_eq_top (P := P)]
    exact hspan

/-!
GLS3 Chapter 1, Section 10: symmetric Cartan matrices force equal root
lengths, so a pairing value `2` can occur only on the diagonal.  This is the
root-system core for excluding simply-laced Dynkin branches and does not
assume a stored classification tag.
-/

private lemma base_rootForm_length_eq_of_symmetric_cartan
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (b : P.Base) (i : b.support)
    (hsym : ∀ j k, b.cartanMatrix j k = b.cartanMatrix k j) :
    (let := Fintype.ofFinite ι
     ∀ j : b.support,
       P.RootForm (P.root j) (P.root j) = P.RootForm (P.root i) (P.root i)) := by
  dsimp only
  let := Fintype.ofFinite ι
  have hlen (j k : b.support) (hjk : b.cartanMatrix j k ≠ 0) :
      P.RootForm (P.root j) (P.root j) = P.RootForm (P.root k) (P.root k) := by
    have hsym' : P.pairingIn ℤ j k = P.pairingIn ℤ k j := by
      change b.cartanMatrixIn ℤ j k = b.cartanMatrixIn ℤ k j
      rw [RootPairing.Base.cartanMatrixIn_def ℤ b j k,
        RootPairing.Base.cartanMatrixIn_def ℤ b k j]
      exact hsym j k
    have hpair : (P.pairingIn ℤ j k : R) * P.RootForm (P.root k) (P.root k) =
        (P.pairingIn ℤ k j : R) * P.RootForm (P.root j) (P.root j) := by
      simpa [← P.algebraMap_pairingIn ℤ j k, ← P.algebraMap_pairingIn ℤ k j] using
        (P.toInvariantForm).pairing_mul_eq_pairing_mul_swap j k |>.symm
    have hpne : P.pairingIn ℤ j k ≠ 0 := by
      intro hzero
      apply hjk
      rw [b.cartanMatrix_apply_eq_zero_iff_pairing]
      simpa [← P.algebraMap_pairingIn ℤ j k] using hzero
    have hne : (P.pairingIn ℤ j k : R) ≠ 0 := by exact_mod_cast hpne
    have hpair' : (P.pairingIn ℤ j k : R) * P.RootForm (P.root k) (P.root k) =
        (P.pairingIn ℤ j k : R) * P.RootForm (P.root j) (P.root j) := by
      calc
        _ = (P.pairingIn ℤ k j : R) * P.RootForm (P.root j) (P.root j) := hpair
        _ = _ := by rw [← hsym']
    have hEq := mul_left_cancel₀ hne hpair'
    exact hEq.symm
  intro j
  apply b.induction_on_cartanMatrix (p := fun j : b.support =>
      P.RootForm (P.root j) (P.root j) = P.RootForm (P.root i) (P.root i)) (j := j)
    (i := i) rfl
  intro k l hk hkl
  exact hlen l k hkl |>.trans hk

public lemma pairingIn_two_eq_same_of_symmetric_cartan
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (b : P.Base) (i : b.support)
    (hsym : ∀ j k, b.cartanMatrix j k = b.cartanMatrix k j)
    {a c : ι} (hpair : P.pairingIn ℤ a c = 2) :
    letI := Fintype.ofFinite ι
    a = c := by
  let := Fintype.ofFinite ι
  have hall := base_rootForm_length_eq_of_symmetric_cartan P b i hsym
  have hallRoot : ∀ j : ι,
      P.RootForm (P.root j) (P.root j) = P.RootForm (P.root i) (P.root i) := by
    intro j
    apply b.induction_reflect j
    · intro x hx
      simpa using hx
    · intro x hx
      exact hall ⟨x, hx⟩
    · intro x l hx hl
      rw [P.root_reflectionPerm]
      simpa using hx
  have hlenac : P.RootForm (P.root a) (P.root a) =
      P.RootForm (P.root c) (P.root c) := (hallRoot a).trans (hallRoot c).symm
  have hpEq : P.pairingIn ℤ a c = P.pairingIn ℤ c a := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → R))
    have h := (P.toInvariantForm).pairing_mul_eq_pairing_mul_swap a c
    have h' : (P.pairingIn ℤ c a : R) * P.RootForm (P.root a) (P.root a) =
        (P.pairingIn ℤ a c : R) * P.RootForm (P.root c) (P.root c) := by
      simpa [← P.algebraMap_pairingIn ℤ a c, ← P.algebraMap_pairingIn ℤ c a] using h
    rw [hlenac] at h'
    have hne : P.RootForm (P.root c) (P.root c) ≠ 0 :=
      RootPairing.IsAnisotropic.rootForm_root_ne_zero c
    exact mul_right_cancel₀ hne h'.symm
  have hrev : P.pairingIn ℤ c a = 2 := by rw [← hpEq, hpair]
  exact (P.pairingIn_two_two_iff (S := ℤ) a c).mp ⟨hpair, hrev⟩

private lemma exists_pairingIn_two_of_root_sum_double_length
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (i j γ : ι)
    (hγ : P.root γ = P.root i + P.root j)
    (hlen : P.RootForm (P.root i) (P.root i) =
      P.RootForm (P.root j) (P.root j))
    (hlenγ : P.RootForm (P.root γ) (P.root γ) =
      2 * P.RootForm (P.root i) (P.root i)) :
    ∃ a b, a ≠ b ∧ P.pairingIn ℤ a b = 2 := by
  let B := (P.posRootForm ℤ).toInvariantForm
  have hrootLen : P.RootForm (P.root i) (P.root i) ≠ 0 :=
    RootPairing.IsAnisotropic.rootForm_root_ne_zero i
  have hpEq : P.pairingIn ℤ i j = P.pairingIn ℤ j i := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → R))
    apply mul_right_cancel₀ hrootLen
    have hswap := B.pairing_mul_eq_pairing_mul_swap i j
    have hswap' :
        (P.pairingIn ℤ i j : R) * P.RootForm (P.root j) (P.root j) =
          (P.pairingIn ℤ j i : R) * P.RootForm (P.root i) (P.root i) := by
      change P.pairing j i * P.RootForm (P.root i) (P.root i) =
        P.pairing i j * P.RootForm (P.root j) (P.root j) at hswap
      simpa [← P.algebraMap_pairingIn ℤ i j,
        ← P.algebraMap_pairingIn ℤ j i] using hswap.symm
    rw [← hlen] at hswap'
    exact hswap'
  have hformExpand :
      P.RootForm (P.root γ) (P.root γ) =
        P.RootForm (P.root i) (P.root i) +
          P.RootForm (P.root j) (P.root j) +
            2 * P.RootForm (P.root i) (P.root j) := by
    rw [hγ]
    simp only [map_add, LinearMap.add_apply, add_assoc]
    rw [show P.RootForm (P.root j) (P.root i) =
      P.RootForm (P.root i) (P.root j) by
        exact P.rootForm_symmetric.eq _ _]
    ring
  have hpair := B.two_mul_apply_root_root i j
  have hpair' :
      2 * P.RootForm (P.root i) (P.root j) =
        (P.pairingIn ℤ i j : R) * P.RootForm (P.root j) (P.root j) := by
    change 2 * P.RootForm (P.root i) (P.root j) =
      P.pairing i j * P.RootForm (P.root j) (P.root j) at hpair
    simpa [← P.algebraMap_pairingIn ℤ i j] using hpair
  have hzero :
      (P.pairingIn ℤ i j : R) * P.RootForm (P.root j) (P.root j) = 0 := by
    rw [← hpair']
    have h := hformExpand
    rw [hlenγ, hlen] at h
    calc
      2 * P.RootForm (P.root i) (P.root j) =
          2 * P.RootForm (P.root j) (P.root j) -
            (P.RootForm (P.root j) (P.root j) +
              P.RootForm (P.root j) (P.root j)) := by
        rw [h]
        ring
      _ = 0 := by ring
  have hne : P.RootForm (P.root j) (P.root j) ≠ 0 := by
    intro hj
    exact hrootLen (hlen.trans hj)
  have hpCast : (P.pairingIn ℤ i j : R) = 0 :=
    (mul_eq_zero.mp hzero).resolve_right hne
  have hp : P.pairingIn ℤ i j = 0 := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → R))
    simpa using hpCast
  have hroot_ne : γ ≠ i := by
    intro h
    have hsum : P.root i = P.root i + P.root j := by simpa [h] using hγ
    have hzero : P.root j = 0 := by
      apply add_left_cancel (a := P.root i)
      simpa using hsum.symm
    exact P.ne_zero j hzero
  refine ⟨γ, i, hroot_ne, ?_⟩
  rw [P.pairingIn_eq_add_of_root_eq_add hγ, ← hpEq, hp]
  simp

/-- An equal-length root sum of twice the squared length can occur only in a
non-simply-laced Dynkin family. -/
public lemma root_sum_double_length_kind_of_hasDynkinType
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (i j γ : ι)
    (hγ : P.root γ = P.root i + P.root j)
    (hlen : P.RootForm (P.root i) (P.root i) =
      P.RootForm (P.root j) (P.root j))
    (hlenγ : P.RootForm (P.root γ) (P.root γ) =
      2 * P.RootForm (P.root i) (P.root i))
    (classification : RootClassification)
    (hType : HasDynkinType P classification) :
    classification.kind = .B ∨ classification.kind = .C ∨
      classification.kind = .F4 ∨ classification.kind = .G2 := by
  obtain ⟨a, c, hac, hpair⟩ :=
    exists_pairingIn_two_of_root_sum_double_length P i j γ hγ hlen hlenγ
  rcases classification with ⟨kind, rank⟩
  rcases hType with ⟨b, e, hbe⟩
  let : Nonempty ι := ⟨i⟩
  let hsupp : b.support.Nonempty := b.support_nonempty
  let i₀ : b.support := ⟨hsupp.choose, hsupp.choose_spec⟩
  have hnotSymmetric : ¬ ∀ x y, b.cartanMatrix x y = b.cartanMatrix y x := by
    intro hsym
    exact hac (pairingIn_two_eq_same_of_symmetric_cartan P b i₀ hsym hpair)
  have hbaseSymmetric
      (hentry : ∀ x y : Fin rank,
        dynkinCartanEntry ⟨kind, rank⟩ x y =
          dynkinCartanEntry ⟨kind, rank⟩ y x) :
      ∀ x y, b.cartanMatrix x y = b.cartanMatrix y x := by
    intro x y
    change b.cartanMatrixIn ℤ x y = b.cartanMatrixIn ℤ y x
    rw [hbe x y, hbe y x]
    exact hentry (e x) (e y)
  cases kind with
  | A =>
      exact False.elim (hnotSymmetric
        (hbaseSymmetric (dynkinCartanEntry_A_symmetric rank)))
  | B => exact Or.inl rfl
  | C => exact Or.inr (Or.inl rfl)
  | D =>
      exact False.elim (hnotSymmetric
        (hbaseSymmetric (dynkinCartanEntry_D_symmetric_any_rank rank)))
  | E6 =>
      exact False.elim (hnotSymmetric
        (hbaseSymmetric (dynkinCartanEntry_E6_symmetric_any_rank rank)))
  | E7 =>
      exact False.elim (hnotSymmetric
        (hbaseSymmetric (dynkinCartanEntry_E7_symmetric_any_rank rank)))
  | E8 =>
      exact False.elim (hnotSymmetric
        (hbaseSymmetric (dynkinCartanEntry_E8_symmetric_any_rank rank)))
  | F4 => exact Or.inr (Or.inr (Or.inl rfl))
  | G2 => exact Or.inr (Or.inr (Or.inr rfl))

/-! A concrete Dynkin witness supplies the base cardinality; when its rank is
positive, an independently supplied Cartan-graph connectivity witness yields
irreducibility.  No classification result is stored in a realization
structure. -/

public theorem isIrreducible_of_hasDynkinType_of_cartan_connected
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (C : RootClassification) (hType : HasDynkinType P C)
    (hrank : 0 < C.rank)
    (hconn : ∀ b : P.Base, ∀ s t : b.support,
      Relation.ReflTransGen (fun u v : b.support => b.cartanMatrix u v ≠ 0) s t) :
    P.IsIrreducible := by
  rcases hType with ⟨b, e, _⟩
  have hcard : b.support.card = C.rank := by
    simpa using Fintype.card_congr e
  have hbase : b.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have hcard0 : b.support.card = 0 := by simp [hzero]
    omega
  exact isIrreducible_of_cartan_connected P b hbase (hconn b)

end Theory.AlgebraicGroup
