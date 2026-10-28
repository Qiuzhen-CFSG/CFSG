module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.Families
public import Theory.Representation.BinaryPermutation.OddOffenderTransport

/-!
# Three fixed vectors detect the three pair swaps

In the even-weight core on seven letters, the indicators of {0,1}, {2,3},
and {4,5} are fixed by the three-transposition subgroup. A permutation fixing
them must preserve each pair and the remaining letter, hence is a product
of the three swaps. The odd-degree core/natural equivalence transports this
test to the precise natural quotient representation. The final lemma
transports the same test by a simultaneous permutation conjugation.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.22, printed p.932, with the fixed-vector argument of B.2.20.
-/

@[expose] public section

open Subgroup Equiv
open Representation.BinaryOffender
open BinaryPermutation
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison
private def pairVector (p : Fin 3) : Full (Fin 7) :=
  fun i => if i.val / 2 = p.val ∧ i.val < 6 then 1 else 0
private theorem pairVector_one (p : Fin 3) (i : Fin 7) :
    pairVector p i = 1 ↔ i.val / 2 = p.val ∧ i.val < 6 := by
  simp only [pairVector]
  split_ifs <;> simp_all
private def pairCore (p : Fin 3) : core (Fin 7) :=
  ⟨pairVector p, by
    change ∑ i, pairVector p i = 0
    fin_cases p <;> decide +kernel⟩
private theorem pairCore_fixed (p : Fin 3) :
    pairCore p ∈ fixedSpace (coreRepresentation (Fin 7)) threeTranspositions := by
  rw [threeTranspositions, mem_fixedSpace_closure_iff]
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl <;> apply Subtype.ext <;>
    fin_cases p <;> decide +kernel

private def pairWord (a b c : Bool) : Perm (Fin 7) :=
  (if a then swap 0 1 else 1) * (if b then swap 2 3 else 1) * (if c then swap 4 5 else 1)
private theorem pairWord_table (a b c : Bool) :
    pairWord a b c 0 = (if a then 1 else 0) ∧
    pairWord a b c 1 = (if a then 0 else 1) ∧
    pairWord a b c 2 = (if b then 3 else 2) ∧
    pairWord a b c 3 = (if b then 2 else 3) ∧
    pairWord a b c 4 = (if c then 5 else 4) ∧
    pairWord a b c 5 = (if c then 4 else 5) ∧ pairWord a b c 6 = 6 := by
  cases a <;> cases b <;> cases c <;> decide +kernel
private theorem pairWord_mem (a b c : Bool) : pairWord a b c ∈ threeTranspositions := by
  unfold pairWord
  apply mul_mem
  · apply mul_mem
    · split_ifs
      · exact subset_closure (by simp)
      · exact one_mem _
    · split_ifs
      · exact subset_closure (by simp)
      · exact one_mem _
  · split_ifs
    · exact subset_closure (by simp)
    · exact one_mem _
private theorem pair_coordinates (a b x y : Fin 7) (hab : a ≠ b)
    (hx : x = a ∨ x = b) (hy : y = a ∨ y = b) (hxy : x ≠ y) :
    x = (if decide (x = b) then b else a) ∧ y = (if decide (x = b) then a else b) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact (hxy rfl).elim
  · simp [hab]
  · simp
  · exact (hxy rfl).elim

private theorem perm_mem_of_pairCore (s : Perm (Fin 7))
    (hs : ∀ p, coreRepresentation (Fin 7) s (pairCore p) = pairCore p) :
    s ∈ threeTranspositions := by
  have hc (p : Fin 3) (i : Fin 7) : pairVector p i = pairVector p (s i) := by
    have h := congrArg (fun v : core (Fin 7) => v.val (s i)) (hs p)
    change pairVector p (s.symm (s i)) = pairVector p (s i) at h
    simpa using h
  have hp (p : Fin 3) (i : Fin 7) (hi : pairVector p i = 1) :
      (s i).val / 2 = p.val ∧ (s i).val < 6 :=
    (pairVector_one p (s i)).mp ((hc p i).symm.trans hi)
  have h0 : s 0 = 0 ∨ s 0 = 1 := by
    have h := hp 0 0 (by decide)
    have he : (s 0).val = 0 ∨ (s 0).val = 1 := by omega
    exact he.imp Fin.ext Fin.ext
  have h1 : s 1 = 0 ∨ s 1 = 1 := by
    have h := hp 0 1 (by decide)
    have he : (s 1).val = 0 ∨ (s 1).val = 1 := by omega
    exact he.imp Fin.ext Fin.ext
  have h2 : s 2 = 2 ∨ s 2 = 3 := by
    have h := hp 1 2 (by decide)
    have he : (s 2).val = 2 ∨ (s 2).val = 3 := by omega
    exact he.imp Fin.ext Fin.ext
  have h3 : s 3 = 2 ∨ s 3 = 3 := by
    have h := hp 1 3 (by decide)
    have he : (s 3).val = 2 ∨ (s 3).val = 3 := by omega
    exact he.imp Fin.ext Fin.ext
  have h4 : s 4 = 4 ∨ s 4 = 5 := by
    have h := hp 2 4 (by decide)
    have he : (s 4).val = 4 ∨ (s 4).val = 5 := by omega
    exact he.imp Fin.ext Fin.ext
  have h5 : s 5 = 4 ∨ s 5 = 5 := by
    have h := hp 2 5 (by decide)
    have he : (s 5).val = 4 ∨ (s 5).val = 5 := by omega
    exact he.imp Fin.ext Fin.ext
  have h6 : s 6 = 6 := by
    have hn (p : Fin 3) : ¬ ((s 6).val / 2 = p.val ∧ (s 6).val < 6) := by
      intro he
      have h := hc p 6
      rw [(pairVector_one p (s 6)).mpr he] at h
      have hz : pairVector p 6 = 0 := by fin_cases p <;> rfl
      rw [hz] at h
      exact zero_ne_one h
    have ha := hn 0
    have hb := hn 1
    have hd := hn 2
    apply Fin.ext
    have hbnd := (s 6).isLt
    change (s 6).val = 6
    omega
  clear hs hc hp
  have hn01 := s.injective.ne (by decide : (0 : Fin 7) ≠ 1)
  have hn23 := s.injective.ne (by decide : (2 : Fin 7) ≠ 3)
  have hn45 := s.injective.ne (by decide : (4 : Fin 7) ≠ 5)
  have h01 := pair_coordinates 0 1 (s 0) (s 1) (by decide) h0 h1 hn01
  have h23 := pair_coordinates 2 3 (s 2) (s 3) (by decide) h2 h3 hn23
  have h45 := pair_coordinates 4 5 (s 4) (s 5) (by decide) h4 h5 hn45
  let a := decide (s 0 = 1)
  let b := decide (s 2 = 3)
  let c := decide (s 4 = 5)
  have ht := pairWord_table a b c
  have he : s = pairWord a b c := by
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h01.1.trans ht.1.symm
    · exact h01.2.trans ht.2.1.symm
    · exact h23.1.trans ht.2.2.1.symm
    · exact h23.2.trans ht.2.2.2.1.symm
    · exact h45.1.trans ht.2.2.2.2.1.symm
    · exact h45.2.trans ht.2.2.2.2.2.1.symm
    · exact h6.trans ht.2.2.2.2.2.2.symm
  rw [he]
  exact pairWord_mem a b c

theorem natural_fixed_detection (s : Perm (Fin 7))
    (hs : ∀ w ∈ fixedSpace (naturalRepresentation (Fin 7)) threeTranspositions,
      naturalRepresentation (Fin 7) s w = w) : s ∈ threeTranspositions := by
  let e := coreEquivNatural (Fin 7) (by decide)
  apply perm_mem_of_pairCore s
  intro p
  apply e.injective
  rw [coreEquivNatural_equivariant]
  apply hs
  intro a
  change naturalRepresentation (Fin 7) a.val (e (pairCore p)) = e (pairCore p)
  rw [← coreEquivNatural_equivariant]
  exact congrArg e (pairCore_fixed p a)

theorem natural_fixed_detection_conjugate (B : Subgroup (Perm (Fin 7)))
    (g : Perm (Fin 7)) (hg : B.map (MulAut.conj g).toMonoidHom = threeTranspositions)
    (s : Perm (Fin 7))
    (hs : ∀ w ∈ fixedSpace (naturalRepresentation (Fin 7)) B,
      naturalRepresentation (Fin 7) s w = w) : s ∈ B := by
  let π := naturalRepresentation (Fin 7)
  have hd : (MulAut.conj g) s ∈ threeTranspositions := by
    apply natural_fixed_detection
    intro w hw
    have hw' : π g⁻¹ w ∈ fixedSpace π B := by
      intro b
      have hb : (MulAut.conj g) b.val ∈ threeTranspositions :=
        hg ▸ mem_map_of_mem _ b.property
      have h := hw ⟨(MulAut.conj g) b.val, hb⟩
      have he : π b.val (π g⁻¹ w) = π g⁻¹ (π ((MulAut.conj g) b.val) w) := by
        change _ = π g⁻¹ (π (g * b.val * g⁻¹) w)
        simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]
      change π b.val (π g⁻¹ w) = π g⁻¹ w
      change π ((MulAut.conj g) b.val) w = w at h
      rw [he, h]
    change π (g * s * g⁻¹) w = w
    simp only [map_mul, Module.End.mul_apply]
    rw [hs _ hw', Representation.self_inv_apply]
  rw [← hg] at hd
  obtain ⟨b, hb, he⟩ := hd
  exact (MulAut.conj g).injective he ▸ hb

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison

end
