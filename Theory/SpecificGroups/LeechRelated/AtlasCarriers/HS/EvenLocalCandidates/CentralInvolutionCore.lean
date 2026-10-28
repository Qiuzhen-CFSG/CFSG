module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralInvolutionCore.Data
/-!
# A normal self-centralizing two-subgroup in the first HS local

Let `L` be the actual normalizer of `elementary 0` in the degree-100 ATLAS
carrier. Since `elementary 0 = ⟨e0⟩` has order two, every element of `L`
centralizes `e0`. The graph in `CentralInvolutionCore.Data`, preserved by
both defining carrier generators, partitions the letters into pairs according
to their neighborhoods among the fixed letters of `e0`. Thus `L` permutes
these pairs.

Define `core` to fix each pair of fixed letters setwise. This is normal in
`L`. Its elements square to the identity on the fixed letters, and their
squares then fix every pair of letters. Consequently every element of `core`
has fourth power one. Five explicit word elements of `core` have fixed-point
patterns distinguishing the fixed-letter pairs. An element centralizing
`core` must therefore fix each such pair, proving self-centralization.

This gives exactly the intrinsic two-subgroup required for this local in
Aschbacher–Smith's condition E, printed pp.3–4. The construction agrees with
the central-involution entry of GLS volume 3, Table 5.3m, printed p.274; it
requires no order, coverage, or quotient-recognition hypothesis. All finite
witnesses are checked in Lean's kernel; discovery scripts are retained in
`CentralInvolutionCore/source/`.
-/

namespace Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open Subgroup
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option Elab.async false


private theorem carrier_adj (g : Carrier) (i j : Fin 100) :
    adj ((g : Equiv.Perm (Fin 100)) i) ((g : Equiv.Perm (Fin 100)) j) = adj i j := by
  have h : ∀ x ∈ generated, ∀ i j,
      adj (x i) (x j) = adj i j := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · rw [← ab0_eq]; exact ab0_adj
      · have hx' : x = generatorB := Set.mem_singleton_iff.mp hx
        subst x
        rw [← ab1_eq]; exact ab1_adj
    | one => intro i j; rfl
    | mul x y _ _ hx hy =>
      intro i j
      exact (hx (y i) (y j)).trans (hy i j)
    | inv x _ hx =>
      intro i j
      simpa using (hx (x⁻¹ i) (x⁻¹ j)).symm
  exact h g g.property i j

/-- The fixed ATLAS carrier preserves the graph used to define the pair kernel. -/
public theorem carrier_preserves_adj (g : Carrier) (i j : Fin 100) :
    adj ((g : Equiv.Perm (Fin 100)) i) ((g : Equiv.Perm (Fin 100)) j) = adj i j :=
  carrier_adj g i j

private theorem elementary_zero : elementary 0 = closure {e0} := by
  unfold elementary
  congr 1
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj0 : j = 0 := Fin.ext (by simpa using hj)
    subst j
    rfl
  · rintro rfl
    exact ⟨(0 : Fin 3), by simp, rfl⟩

private theorem elementary_zero_mem (x : Carrier) :
    x ∈ elementary 0 ↔ x = 1 ∨ x = e0 := by
  rw [elementary_zero]
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact Or.inr (Set.mem_singleton_iff.mp hy)
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact Or.inl (one_mul _)
      · exact Or.inr (one_mul _)
      · exact Or.inr (mul_one _)
      · exact Or.inl e0_mul
    | inv x _ hx =>
      rcases hx with rfl | rfl
      · exact Or.inl inv_one
      · exact Or.inr (inv_eq_of_mul_eq_one_right e0_mul)
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact subset_closure (Set.mem_singleton _)

private theorem local_commutes (g : localGroup 0) : (g : Carrier) * e0 = e0 * g := by
  have he : e0 ∈ elementary 0 := (elementary_zero_mem _).mpr (Or.inr rfl)
  have hc := (mem_normalizer_iff.mp g.property e0).mp he
  rcases (elementary_zero_mem _).mp hc with hc | hc
  · have hh := congrArg (fun x : Carrier => (g : Carrier)⁻¹ * x * g) hc
    have : e0 = 1 := by simpa [mul_assoc] using hh
    exact (e0_nontrivial this).elim
  · exact mul_inv_eq_iff_eq_mul.mp hc

private theorem mem_local_of_commutes (g : Carrier) (hg : g * e0 = e0 * g) :
    g ∈ localGroup 0 := by
  apply centralizer_le_normalizer
  intro y hy
  rcases (elementary_zero_mem _).mp hy with rfl | rfl
  · simp
  · exact hg.symm

private abbrev act (g : localGroup 0) : Equiv.Perm (Fin 100) := g.val.val

private theorem act_e0 (g : localGroup 0) (i : Fin 100) :
    act g ((e0 : Equiv.Perm (Fin 100)) i) =
      (e0 : Equiv.Perm (Fin 100)) (act g i) :=
  congrArg (fun x : Carrier => (x : Equiv.Perm (Fin 100)) i) (local_commutes g)

private theorem act_fixed (g : localGroup 0) {i : Fin 100}
    (hi : (e0 : Equiv.Perm (Fin 100)) i = i) :
    (e0 : Equiv.Perm (Fin 100)) (act g i) = act g i := by
  rw [← act_e0, hi]

private theorem signature_eq_of (i j : Fin 100)
    (h : ∀ v : Fin 100, (e0 : Equiv.Perm (Fin 100)) v = v → adj i v = adj j v) :
    signature i = signature j := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 100
  · have hi := signature_bits i ⟨k, hk⟩
    have hj := signature_bits j ⟨k, hk⟩
    rw [hi, hj]
    split
    · exact h _ ‹_›
    · rfl
  · have hik : signature i < 2^k := (signature_bound i).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
    have hjk : signature j < 2^k := (signature_bound j).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow hik, Nat.testBit_lt_two_pow hjk]

private theorem signature_transport (g : localGroup 0) {i j : Fin 100}
    (h : signature i = signature j) : signature (act g i) = signature (act g j) := by
  apply signature_eq_of
  intro v hv
  have hu := act_fixed g⁻¹ hv
  have hb := congrArg (fun n : ℕ => n.testBit (act g⁻¹ v).val) h
  simp only [signature_bits, if_pos hu] at hb
  calc
    adj (act g i) v = adj i (act g⁻¹ v) := by
      simpa [act] using carrier_adj g.val i (act g⁻¹ v)
    _ = adj j (act g⁻¹ v) := hb
    _ = adj (act g j) v := by
      simpa [act] using (carrier_adj g.val j (act g⁻¹ v)).symm

private theorem act_twin (g : localGroup 0) (i : Fin 100) :
    act g (twin i) = twin (act g i) := by
  have hs := signature_transport g ((signature_class i (twin i)).mpr (Or.inr rfl))
  rcases (signature_class _ _).mp hs with h | h
  · exact (twin_ne i ((act g).injective h)).elim
  · exact h

private theorem twice_of_pair (g : localGroup 0) {i : Fin 100}
    (hi : act g i = i ∨ act g i = twin i) : act g (act g i) = i := by
  rcases hi with hi | hi
  · rw [hi, hi]
  · rw [hi, act_twin, hi, twin_square]

/-- The kernel of the action on the ten pairs of fixed letters. -/
public def core : Subgroup (localGroup 0) where
  carrier := {g | ∀ i : Fin 100, (e0 : Equiv.Perm (Fin 100)) i = i →
    act g i = i ∨ act g i = twin i}
  one_mem' := by intro i _; exact Or.inl rfl
  mul_mem' := by
    intro g h hg hh i hi
    change act g (act h i) = i ∨ act g (act h i) = twin i
    rcases hh i hi with hh | hh
    · rw [hh]; exact hg i hi
    · rw [hh, act_twin]
      rcases hg i hi with hg | hg
      · exact Or.inr (congrArg twin hg)
      · exact Or.inl ((congrArg twin hg).trans (twin_square i))
  inv_mem' := by
    intro g hg i hi
    have hu := act_fixed g⁻¹ hi
    rcases hg (act g⁻¹ i) hu with h | h
    · exact Or.inl (by simpa [act] using h.symm)
    · right
      have h' : i = twin (act g⁻¹ i) := by simpa [act] using h
      exact (twin_square _).symm.trans (congrArg twin h'.symm)

/-- Normality is inside the actual ambient normalizer `localGroup 0`. -/
public theorem core_normal : core.Normal := by
  constructor
  intro n hn g i hi
  change act g (act n (act g⁻¹ i)) = i ∨
    act g (act n (act g⁻¹ i)) = twin i
  rcases hn (act g⁻¹ i) (act_fixed g⁻¹ hi) with h | h
  · left
    rw [h]
    exact (act g).apply_symm_apply i
  · right
    rw [h, act_twin]
    exact congrArg twin ((act g).apply_symm_apply i)

/-- Membership in the pair kernel, stated without its private action abbreviation. -/
public theorem mem_core_iff (g : localGroup 0) : g ∈ core ↔
    ∀ i : Fin 100, (e0 : Equiv.Perm (Fin 100)) i = i →
      g.val.val i = i ∨ g.val.val i = twin i := Iff.rfl

/-- The local group permutes the graph-defined pairs. -/
public theorem local_preserves_twin (g : localGroup 0) (i : Fin 100) :
    g.val.val (twin i) = twin (g.val.val i) := act_twin g i

private theorem core_square_fixed (g : core) {i : Fin 100}
    (hi : (e0 : Equiv.Perm (Fin 100)) i = i) : act (g.val ^ 2) i = i := by
  exact twice_of_pair g.val (g.property i hi)

private theorem pointwise_fixed_pairs (g : localGroup 0)
    (hg : ∀ v : Fin 100, (e0 : Equiv.Perm (Fin 100)) v = v → act g v = v)
    (i : Fin 100) : act g i = i ∨ act g i = twin i := by
  apply (signature_class i (act g i)).mp
  apply signature_eq_of
  intro v hv
  have ha := carrier_adj g.val i v
  rw [hg v hv] at ha
  exact ha.symm

/-- Every element of the pair kernel has fourth power one. -/
public theorem core_fourth_power (g : core) : g ^ 4 = 1 := by
  have hp := pointwise_fixed_pairs (g.val ^ 2) (fun _ hv => core_square_fixed g hv)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have h := twice_of_pair (g.val ^ 2) (hp i)
  change (act (g.val ^ 4)) i = i
  rw [show 4 = 2 * 2 from rfl, pow_mul, pow_two]
  exact h

/-- The pair kernel is a two-group, without an ambient order assumption. -/
public theorem core_isPGroup : IsPGroup 2 core := by
  intro g
  exact ⟨2, core_fourth_power g⟩

private def qLocal (k : Fin 5) : localGroup 0 :=
  ⟨q k, mem_local_of_commutes (q k) (q_commutes k)⟩

private theorem qLocal_mem (k : Fin 5) : qLocal k ∈ core := q_pair k

/-- The five word elements force a centralizing element to fix every pair. -/
public theorem core_selfCentralizing : centralizer (core : Set (localGroup 0)) ≤ core := by
  intro g hg i hi
  apply (signature_class i (act g i)).mp
  apply q_separates i (act g i) hi (act_fixed g hi)
  intro k
  have hc := congrArg (fun x : localGroup 0 => act x i) (hg (qLocal k) (qLocal_mem k))
  change (q k : Equiv.Perm (Fin 100)) (act g i) =
    act g ((q k : Equiv.Perm (Fin 100)) i) at hc
  constructor
  · intro h
    exact hc.trans (congrArg (act g) h)
  · intro h
    exact (act g).injective (hc.symm.trans h)

/-- The first explicit HS local has a normal self-centralizing two-subgroup. -/
public theorem exists_normal_selfCentralizing_two_subgroup :
    ∃ Q : Subgroup (localGroup 0), Q.Normal ∧ IsPGroup 2 Q ∧
      centralizer (Q : Set (localGroup 0)) ≤ Q :=
  ⟨core, core_normal, core_isPGroup, core_selfCentralizing⟩

end Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
