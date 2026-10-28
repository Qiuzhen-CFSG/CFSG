module
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups

/-!
# Proper binary flag overgroups preserved by graph actions

An outer automorphism preserving a full binary flag reverses its cuts.
In dimensions four and five, the reversal has two node orbits. Thus a
proper Sylow overgroup preserved by an outer automorphism is the Sylow
subgroup itself, the interior parabolic, or the endpoint parabolic.
The classification uses a common original basis and the actual action.

Source: Aschbacher--Smith 15.1.22(3), printed pp.1099--1100.
-/
public section
open Subgroup
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic

/-- Graph action reverses every subset of the original flag cuts. -/
theorem outer_map_cuts {m : ℕ} (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4)
    (b : Basis m) (a : MulAut (LinearGroup (m+1)))
    (ha : a ∉ MulAut.innerSubgroup _)
    (hB : (cutStabilizer b Set.univ).map a.toMonoidHom = cutStabilizer b Set.univ)
    (cuts : Set (Fin m)) :
    (cutStabilizer b cuts).map a.toMonoidHom =
      cutStabilizer b {i | i.rev ∈ cuts} := by
  obtain ⟨g,rfl⟩ := outer_eq_graph_inner (by omega) (by omega) a ha
  let a := graphLinear (m+1) * MulAut.conj g
  have hp (j : Fin m) : (parabolic (cutSpace b j)).map a.toMonoidHom =
      parabolic (cutSpace b j.rev) := by
    rw [graph_inner_map_parabolic, graph_inner_cutSpace_of_fullFlag b g hB]
  ext x
  change x ∈ (cutStabilizer b cuts).map a.toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv, mem_cutStabilizer, mem_cutStabilizer]
  have hm (j : Fin m) : a.symm x ∈ parabolic (cutSpace b j) ↔
      x ∈ parabolic (cutSpace b j.rev) := by
    rw [← hp j, Subgroup.mem_map_equiv]
  constructor
  · intro hx j hj
    have he := (hm j.rev).mp (hx j.rev hj)
    change x ∈ parabolic (cutSpace b j)
    simpa only [Fin.rev_rev] using he
  · intro hx j hj
    exact (hm j).mpr (hx j.rev (by simpa using hj))

/-- Preservation of a partial flag is exactly reversal invariance of its cuts. -/
theorem outer_invariant_cuts_iff {m : ℕ} (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4)
    (b : Basis m) (a : MulAut (LinearGroup (m+1)))
    (ha : a ∉ MulAut.innerSubgroup _)
    (hB : (cutStabilizer b Set.univ).map a.toMonoidHom = cutStabilizer b Set.univ)
    (cuts : Set (Fin m)) :
    (cutStabilizer b cuts).map a.toMonoidHom = cutStabilizer b cuts ↔
      ∀ i : Fin m, i.rev ∈ cuts ↔ i ∈ cuts := by
  rw [outer_map_cuts hm₀ hm₁ b a ha hB]
  constructor
  · intro he i
    exact ⟨fun hi => (cutStabilizer_le_iff b _ _).mp he.ge hi,
      fun hi => (cutStabilizer_le_iff b _ _).mp he.le hi⟩
  · intro hc
    congr 1
    ext i
    exact hc i

private theorem symmetric_cuts_cases {m : ℕ} (hm : m=3 ∨ m=4)
    (cuts : Set (Fin m)) (hc : ∀ i : Fin m, i.rev ∈ cuts ↔ i ∈ cuts) :
    cuts = ∅ ∨ cuts = Set.univ ∨
      cuts = {i | i.val=0 ∨ i.val=m-1} ∨
      cuts = {i | i.val=0 ∨ i.val=m-1}ᶜ := by
  rcases hm with rfl | rfl
  · have h02 : (2 : Fin 3) ∈ cuts ↔ (0 : Fin 3) ∈ cuts := hc 0
    by_cases h0 : (0 : Fin 3) ∈ cuts <;> by_cases h1 : (1 : Fin 3) ∈ cuts
    · exact Or.inr (Or.inl (by ext i; fin_cases i <;> simp_all))
    · exact Or.inr (Or.inr (Or.inl (by ext i; fin_cases i <;> simp_all)))
    · exact Or.inr (Or.inr (Or.inr (by ext i; fin_cases i <;> simp_all)))
    · exact Or.inl (by ext i; fin_cases i <;> simp_all)
  · have h03 : (3 : Fin 4) ∈ cuts ↔ (0 : Fin 4) ∈ cuts := hc 0
    have h12 : (2 : Fin 4) ∈ cuts ↔ (1 : Fin 4) ∈ cuts := hc 1
    by_cases h0 : (0 : Fin 4) ∈ cuts <;> by_cases h1 : (1 : Fin 4) ∈ cuts
    · exact Or.inr (Or.inl (by ext i; fin_cases i <;> simp_all))
    · exact Or.inr (Or.inr (Or.inl (by ext i; fin_cases i <;> simp_all)))
    · exact Or.inr (Or.inr (Or.inr (by ext i; fin_cases i <;> simp_all)))
    · exact Or.inl (by ext i; fin_cases i <;> simp_all)

/-- Classify every proper Sylow overgroup fixed by a genuine outer action. -/
theorem outer_invariant_overgroup {m : ℕ} (hm : m=3 ∨ m=4)
    (S : Sylow 2 (LinearGroup (m+1))) (b : Basis m)
    (hS : (S : Subgroup (LinearGroup (m+1))) = cutStabilizer b Set.univ)
    (a : MulAut (LinearGroup (m+1))) (ha : a ∉ MulAut.innerSubgroup _)
    (hB : (S : Subgroup (LinearGroup (m+1))).map a.toMonoidHom = S)
    (P : Subgroup (LinearGroup (m+1))) (hSP : (S : Subgroup _) ≤ P) (hP : P ≠ ⊤)
    (hPa : P.map a.toMonoidHom = P) :
    P = S ∨ P = cutStabilizer b {i | i.val=0 ∨ i.val=m-1} ∨
      P = cutStabilizer b {i | i.val=0 ∨ i.val=m-1}ᶜ := by
  obtain ⟨c,cuts,hc,hPc⟩ := BinaryLinear.SylowFlagOvergroups.exists_flag_of_sylow_le S P hSP
  have hPb : P = cutStabilizer b cuts :=
    hPc.trans (cutStabilizer_eq_of_fullFlag_le b c cuts (hS ▸ hPc ▸ hSP))
  have hs := (outer_invariant_cuts_iff (by omega) (by omega) b a ha (hS ▸ hB) cuts).mp
    (hPb ▸ hPa)
  rcases symmetric_cuts_cases hm cuts hs with he | he | he | he
  · exfalso
    apply hP
    rw [hPb,he,cutStabilizer]
    simp
  · exact Or.inl (hPb.trans (he ▸ hS.symm))
  · exact Or.inr (Or.inl (hPb.trans (congrArg (cutStabilizer b) he)))
  · exact Or.inr (Or.inr (hPb.trans (congrArg (cutStabilizer b) he)))
end BinaryLinear.InvariantNodeActions
