module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.Contracts
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Data
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Base

/-!
# Recovering order-thirteen witnesses in seed extensions

Write the literal representative as `a*r*b⁻¹`. If a seed word q satisfies
`q*a = b*n`, then `q*(a*r*b⁻¹)` is conjugate by b to the short element n*r.
The same conjugator works for products, so a product of recovered seed
multiples is conjugate to the corresponding product of short elements.
Order certificates can consequently be shared by different seeds and cosets.

Recovery tests use only forward maps. The certified base 0,1,2 proves actual
group equalities; prime order also requires a moved base point. Seed membership
comes from words in the literal published generators, not from a claimed
seed order or a subgroup catalogue.

Source: Parrott (1972), section 5, p.683, with the existing Atlas normal forms
and three-point base. The finite data are discovered by original code in
`source/`; no discovery computation is accepted as a proof.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates
open ConverseLocalCoverage DoubleCosetCertificate
open OuterOddSubgroups.OverlapCentralizers

def shortElement (n : Fin 2048) (k : Fin 18) : Atlas1600Group :=
  atlas1600SylowTwoNormalForm n * doubleCosetRep k

def shortTest (n : Fin 2048) (k : Fin 18) : Bool :=
  let y := fastNormalForm n * fastRep k
  (y ^ 13) 0 == 0 && (y ^ 13) 1 == 1 && (y ^ 13) 2 == 2 &&
    (y 0 != 0 || y 1 != 1 || y 2 != 2)

theorem normalForm_val (n : Fin 2048) :
    (atlas1600SylowTwoNormalForm n).val = fastNormalForm n := by
  simp [fastNormalForm, Packed.perm_eq, Packed.generator, atlas1600SylowTwoNormalForm_val]

private theorem packed_code (a : ParrottGenerator) :
    Packed.perm (code a) = Atlas1600ParrottData.permutation a := by
  cases a <;> simp [Packed.perm_eq, Packed.generator, code, Atlas1600ParrottData.permutation]

private theorem positiveWord_val (w : List ParrottGenerator) :
    ((w.map atlas1600ParrottAssignment).prod).val =
      (w.map fun a => Packed.perm (code a)).prod := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (atlas1600ParrottAssignment a).val * ((w.map atlas1600ParrottAssignment).prod).val =
      Packed.perm (code a) * (w.map fun b => Packed.perm (code b)).prod
    rw [ih, packed_code, atlas1600ParrottAssignment_val]

theorem shortElement_val (n : Fin 2048) (k : Fin 18) :
    (shortElement n k).val = fastNormalForm n * fastRep k := by
  change (atlas1600SylowTwoNormalForm n).val * (doubleCosetRep k).val = _
  rw [normalForm_val, show (doubleCosetRep k).val = fastRep k from
    positiveWord_val (doubleCosetWord k)]

theorem shortTest_sound (n : Fin 2048) (k : Fin 18) (h : shortTest n k = true) :
    orderOf (shortElement n k) = 13 := by
  simp only [shortTest, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    bne_iff_ne] at h
  obtain ⟨⟨⟨h0,h1⟩,h2⟩,hne⟩ := h
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply threePoint_eq_one
    · change ((shortElement n k).val ^ 13) 0 = 0
      rwa [shortElement_val]
    · change ((shortElement n k).val ^ 13) 1 = 1
      rwa [shortElement_val]
    · change ((shortElement n k).val ^ 13) 2 = 2
      rwa [shortElement_val]
  · intro he
    have hv : fastNormalForm n * fastRep k = 1 := by
      rw [← shortElement_val, he]; rfl
    simp only [hv, Equiv.Perm.one_apply, ne_eq, not_true_eq_false, or_self] at hne

def seedWord (w : List (Fin 2048)) : Atlas1600Group :=
  (w.map atlas1600SylowTwoNormalForm).prod

theorem seedWord_mem (i : Fin 122) (w : List (Fin 2048))
    (hw : ∀ n ∈ w, n ∈ seedIndices i) : seedWord w ∈ seed i := by
  apply (seed i).list_prod_mem
  intro x hx
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure ⟨n, hw n hn, rfl⟩

theorem seedWord_val (w : List (Fin 2048)) :
    (seedWord w).val = (w.map fastNormalForm).prod := by
  induction w with
  | nil => rfl
  | cons n w ih =>
    change (atlas1600SylowTwoNormalForm n).val * (seedWord w).val =
      fastNormalForm n * (w.map fastNormalForm).prod
    rw [normalForm_val, ih]

def recoveryTest (w : List (Fin 2048)) (u v n : Fin 2048) : Bool :=
  let x := (w.map fastNormalForm).prod * fastNormalForm u
  let y := fastNormalForm v * fastNormalForm n
  x 0 == y 0 && x 1 == y 1 && x 2 == y 2

theorem recoveryTest_sound (w : List (Fin 2048)) (u v n : Fin 2048)
    (h : recoveryTest w u v n = true) :
    seedWord w * atlas1600SylowTwoNormalForm u =
      atlas1600SylowTwoNormalForm v * atlas1600SylowTwoNormalForm n := by
  simp only [recoveryTest, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h0,h1⟩,h2⟩ := h
  apply threePoint_ext
  · change ((seedWord w).val * (atlas1600SylowTwoNormalForm u).val) 0 =
      ((atlas1600SylowTwoNormalForm v).val * (atlas1600SylowTwoNormalForm n).val) 0
    simpa only [seedWord_val, normalForm_val] using h0
  · change ((seedWord w).val * (atlas1600SylowTwoNormalForm u).val) 1 =
      ((atlas1600SylowTwoNormalForm v).val * (atlas1600SylowTwoNormalForm n).val) 1
    simpa only [seedWord_val, normalForm_val] using h1
  · change ((seedWord w).val * (atlas1600SylowTwoNormalForm u).val) 2 =
      ((atlas1600SylowTwoNormalForm v).val * (atlas1600SylowTwoNormalForm n).val) 2
    simpa only [seedWord_val, normalForm_val] using h2

theorem seed_mul_representative_eq_conj
    (i : Fin 122) (a b : Fin 32) (k : Fin 18) (n : Fin 2048) (q : Atlas1600Group)
    (hr : q * transversal i a = transversal i b * atlas1600SylowTwoNormalForm n) :
    q * representative i a b k = MulAut.conj (transversal i b) (shortElement n k) := by
  dsimp only [representative, shortElement, MulAut.conj_apply]
  calc
    q * (transversal i a * doubleCosetRep k * (transversal i b)⁻¹) =
      (q * transversal i a) * doubleCosetRep k * (transversal i b)⁻¹ := by group
    _ = (transversal i b * atlas1600SylowTwoNormalForm n) *
      doubleCosetRep k * (transversal i b)⁻¹ := by rw [hr]
    _ = _ := by group

theorem representativeWitness_of_shortRecovery
    (i : Fin 122) (a b : Fin 32) (k : Fin 18) (n : Fin 2048) (q : seed i)
    (hr : q.val * transversal i a = transversal i b * atlas1600SylowTwoNormalForm n)
    (ho : orderOf (shortElement n k) = 13) : RepresentativeWitness i a b k := by
  let y := q.val * representative i a b k
  have hy : y ∈ singleExtension i (representative i a b k) :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left q.property)
      (Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _)))
  refine Or.inr (Or.inr (Or.inr ⟨y, hy, ?_⟩))
  have he := seed_mul_representative_eq_conj i a b k n q.val hr
  change orderOf (q.val * representative i a b k) = 13
  rw [he, MulEquiv.orderOf_eq, ho]

theorem representativeWitness_of_tests
    (i : Fin 122) (a b : Fin 32) (k : Fin 18) (n : Fin 2048) (w : List (Fin 2048))
    (hw : ∀ m ∈ w, m ∈ seedIndices i)
    (hr : recoveryTest w (transversalPattern (seedTransversalPattern i) a)
      (transversalPattern (seedTransversalPattern i) b) n = true)
    (ho : shortTest n k = true) : RepresentativeWitness i a b k :=
  representativeWitness_of_shortRecovery i a b k n ⟨seedWord w, seedWord_mem i w hw⟩
    (recoveryTest_sound _ _ _ _ hr) (shortTest_sound n k ho)

def productTest (ns : List (Fin 2048)) (k : Fin 18) : Bool :=
  let y := (ns.map fun n => fastNormalForm n * fastRep k).prod
  (y ^ 13) 0 == 0 && (y ^ 13) 1 == 1 && (y ^ 13) 2 == 2 &&
    (y 0 != 0 || y 1 != 1 || y 2 != 2)

theorem productTest_sound (ns : List (Fin 2048)) (k : Fin 18)
    (h : productTest ns k = true) : orderOf ((ns.map (shortElement · k)).prod) = 13 := by
  have hv : ((ns.map (shortElement · k)).prod).val =
      (ns.map fun n => fastNormalForm n * fastRep k).prod := by
    clear h
    induction ns with
    | nil => rfl
    | cons n ns ih =>
      change (shortElement n k).val * ((ns.map (shortElement · k)).prod).val = _
      rw [shortElement_val, ih]; rfl
  simp only [productTest, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    bne_iff_ne] at h
  obtain ⟨⟨⟨h0,h1⟩,h2⟩,hne⟩ := h
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply threePoint_eq_one
    · change (((ns.map (shortElement · k)).prod).val ^ 13) 0 = 0
      rwa [hv]
    · change (((ns.map (shortElement · k)).prod).val ^ 13) 1 = 1
      rwa [hv]
    · change (((ns.map (shortElement · k)).prod).val ^ 13) 2 = 2
      rwa [hv]
  · intro he
    have he' : (ns.map fun n => fastNormalForm n * fastRep k).prod = 1 := by
      rw [← hv, he]; rfl
    simp only [he', Equiv.Perm.one_apply, ne_eq, not_true_eq_false, or_self] at hne

/-- Several recovered seed multiples give a product of conjugate short elements. -/
theorem representativeWitness_of_productTests
    (i : Fin 122) (a b : Fin 32) (k : Fin 18)
    (ws : List (Fin 2048 × List (Fin 2048)))
    (hw : ∀ nw ∈ ws, ∀ m ∈ nw.2, m ∈ seedIndices i)
    (hr : ∀ nw ∈ ws, recoveryTest nw.2 (transversalPattern (seedTransversalPattern i) a)
      (transversalPattern (seedTransversalPattern i) b) nw.1 = true)
    (ho : productTest (ws.map Prod.fst) k = true) : RepresentativeWitness i a b k := by
  let y := (ws.map fun nw => seedWord nw.2 * representative i a b k).prod
  have hy : y ∈ singleExtension i (representative i a b k) := by
    apply (singleExtension i (representative i a b k)).list_prod_mem
    intro z hz
    obtain ⟨nw, hnw, rfl⟩ := List.mem_map.mp hz
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (seedWord_mem i nw.2 (hw nw hnw)))
      (Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _)))
  refine Or.inr (Or.inr (Or.inr ⟨y, hy, ?_⟩))
  have he : y = MulAut.conj (transversal i b) (((ws.map Prod.fst).map (shortElement · k)).prod) := by
    rw [← List.prod_hom]
    simp only [y, List.map_map]
    congr 1
    apply List.map_congr_left
    intro nw hnw
    exact seed_mul_representative_eq_conj i a b k nw.1 (seedWord nw.2)
      (recoveryTest_sound _ _ _ _ (hr nw hnw))
  rw [he, MulEquiv.orderOf_eq]
  exact productTest_sound _ _ ho


end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates
