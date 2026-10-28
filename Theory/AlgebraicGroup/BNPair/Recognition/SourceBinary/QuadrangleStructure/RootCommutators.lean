module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.CoreCommutators
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderedProducts
public import Theory.GroupTheory.ElementaryPairCommutator
public import Theory.ElementaryAbelian.Join

/-!
# Quadrangle root commutators on the marked split quotient

For rotation order four, a crossed root is the intersection of two
conjugates of U. It is also the intersection of a parabolic radical with
its conjugate by the other simple reflection. Relative normality of the
radicals puts each opposite-root commutator in the intervening root.
Ordered two-root products and the opposite orientation prove that adjacent
roots commute. The three-root products give the full complementary sections.

When the two simple roots are elementary, the derived subgroup and embedded
Frattini subgroup of each complementary section equal its opposite-root
commutator. This identifies the exact earlier DGS radical datum needed for
the nonzero commutator in the linear/quadratic branch; no field ratio or
rank-one model is inferred from these structural identities.

Every subgroup lies in the same marked finite quotient, and conjugation
is on the right. The section 2/5 local-kernel containments remain explicit.
No restriction on the simple-root orders, including two and four, is used.
Source: Fong--Seitz I (3G), pp.14--16, specialized to the root arrangement
in (6A), pp.37--38; Carter 2.5.10 for the ordered product recurrence.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)
private theorem simple_sq (i : Fin 2) : Q.simple i * Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
private theorem simple_mul_cancel (i : Fin 2) (w : Weyl Q) :
    Q.simple i * (Q.simple i * w) = w := by
  rw [← mul_assoc, simple_sq, one_mul]
private theorem longest_four (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j) :
    longest Q = Q.simple i * (Q.simple j * (Q.simple i * Q.simple j)) := by
  have h (b : Bool) := alternatingWord_longest Q b
  rw [hm] at h
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simpa [alternatingWord] using (h false).symm
  · simpa [alternatingWord] using (h true).symm
  · exact (hij rfl).elim

/-- A crossed root is the literal intersection of two conjugates of U. -/
theorem cross_root_intersection (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j) = unipotentConjugate split (Q.simple j) ⊓
      unipotentConjugate split (Q.simple j * Q.simple i) := by
  have hw : (longest Q * Q.simple i) * Q.simple j = Q.simple j * Q.simple i := by
    rw [longest_four Q hm j i hij.symm]
    simp only [mul_assoc, simple_sq, mul_one]
  change rightConjugate (split.U ⊓ unipotentConjugate split (longest Q * Q.simple i))
    (representative (Q.simple j) : X ⧸ Q.D) = _
  rw [rightConjugate_inf, unipotentConjugate_right split _ _ _ (representative_spec _), hw]
  rfl

/-- Its own endpoint reflection fixes the crossed root, for every lift in N. -/
theorem cross_root_reflection_fixed (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i) :
    rightConjugate (rootAt Q split i (Q.simple j)) (n : X ⧸ Q.D) =
      rootAt Q split i (Q.simple j) := by
  rw [cross_root_intersection Q split hm i j hij, rightConjugate_inf,
    unipotentConjugate_right split _ _ n hn,
    unipotentConjugate_right split _ _ n hn, mul_assoc, simple_sq, mul_one, inf_comm]

/-- Intersecting a radical with its conjugate isolates exactly the intervening root. -/
theorem remainder_conjugate_intersection (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i) :
    simpleRemainder Q split j ⊓ rightConjugate (simpleRemainder Q split j) (n : X ⧸ Q.D) =
      rootAt Q split i (Q.simple j) := by
  apply le_antisymm
  · change (split.U ⊓ unipotentConjugate split (Q.simple j)) ⊓
      rightConjugate (split.U ⊓ unipotentConjugate split (Q.simple j)) (n : X ⧸ Q.D) ≤ _
    rw [rightConjugate_inf, unipotentConjugate_right split _ _ n hn,
      cross_root_intersection Q split hm i j hij]
    exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  · have hc := (opposite_roots_le_remainder Q split i j hij).2
    refine le_inf hc ?_
    rw [← cross_root_reflection_fixed Q split hm i j hij n hn]
    exact comap_mono hc

private theorem conjugate_commutator (A B : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) :
    rightConjugate ⁅A,B⁆ n = ⁅rightConjugate A n, rightConjugate B n⁆ := by
  simp only [rightConjugate, comap_equiv_eq_map_symm', map_commutator]

/-- Each crossed positive root belongs to both parabolic radicals. -/
theorem cross_root_le_own_remainder (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j) ≤ simpleRemainder Q split i := by
  have hpos := (opposite_roots_le_remainder Q split i j hij).2.trans inf_le_left
  apply le_inf hpos
  rw [← cross_root_reflection_fixed Q split hm i j hij
    (representative (Q.simple i)) (representative_spec _)]
  exact comap_mono hpos

/-- The quadrangle case of (3G) for the two nonadjacent roots of the same type. -/
theorem cross_root_commutator_le (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    ⁅simpleRoot Q split i, rootAt Q split i (Q.simple j)⁆ ≤
      rootAt Q split j (Q.simple i) := by
  let C := ⁅simpleRoot Q split i, rootAt Q split i (Q.simple j)⁆
  let n := representative (Q.simple j)
  have hC : C ≤ simpleRemainder Q split i := by
    have hn := (simpleRoot_le Q split i).trans (split.U_le.trans
      ((Q.tits.B_le_standardParabolic _).trans (remainder_parabolic_normalizes Q split i hV)))
    have hc := cross_root_le_own_remainder Q split hm i j hij
    exact (commutator_mono le_rfl hc).trans
      (le_normalizer_iff_commutator_le_right.mp hn)
  have hfixed : rightConjugate C (n : X ⧸ Q.D) = C := by
    rw [conjugate_commutator, ← rootAt_eq Q split i (Q.simple j) n (representative_spec _),
      rootAt_right Q split i (Q.simple j) (Q.simple j) n (representative_spec _),
      simple_sq, rootAt_one, commutator_comm]
  rw [← remainder_conjugate_intersection Q split hm j i hij.symm n (representative_spec _)]
  refine le_inf hC ?_
  change C ≤ rightConjugate (simpleRemainder Q split i) (n : X ⧸ Q.D)
  rw [← hfixed]
  exact comap_mono hC

private theorem orderedRoots_three (hm : rotationOrder Q = 4) (b : Bool) :
    orderedRoots Q split b 3 =
      [simpleRoot Q split (if b then 1 else 0),
       rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0)),
       rootAt Q split (if b then 1 else 0) (Q.simple (if b then 0 else 1))] := by
  cases b <;> simp only [orderedRoots, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ite_false, ite_true, List.map_cons, List.map_nil]
  · change [simpleRoot Q split 0, rootAt Q split 1 (Q.simple 0),
      rightConjugate (rootAt Q split 0 (Q.simple 1)) (representative (Q.simple 0) : X ⧸ Q.D)] = _
    rw [cross_root_reflection_fixed Q split hm 0 1 (by decide) _ (representative_spec _)]
  · change [simpleRoot Q split 1, rootAt Q split 0 (Q.simple 1),
      rightConjugate (rootAt Q split 1 (Q.simple 0)) (representative (Q.simple 1) : X ⧸ Q.D)] = _
    rw [cross_root_reflection_fixed Q split hm 1 0 (by decide) _ (representative_spec _)]

private theorem remainder_product (hm : rotationOrder Q = 4) (b : Bool) :
    (simpleRemainder Q split (if b then 0 else 1) : Set (X ⧸ Q.D)) =
      (simpleRoot Q split (if b then 1 else 0) : Set (X ⧸ Q.D)) *
        (rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0)) : Set (X ⧸ Q.D)) *
        (rootAt Q split (if b then 1 else 0) (Q.simple (if b then 0 else 1)) : Set (X ⧸ Q.D)) := by
  have hprod := orderedRoots_product Q split b 3 (by omega)
  rw [orderedRoots_three Q split hm b] at hprod
  change (simpleRoot Q split (if b then 1 else 0) : Set (X ⧸ Q.D)) *
    ((rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0)) : Set (X ⧸ Q.D)) *
    ((rootAt Q split (if b then 1 else 0) (Q.simple (if b then 0 else 1)) : Set (X ⧸ Q.D)) * 1)) = _ at hprod
  rw [mul_one, ← mul_assoc] at hprod
  have hs (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i := inv_eq_of_mul_eq_one_right (simple_sq Q i)
  have hw : longest Q * (alternatingWord Q b 3)⁻¹ = Q.simple (if b then 0 else 1) := by
    cases b
    · rw [longest_four Q hm 1 0 (by decide)]
      simp only [alternatingWord, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ite_false, ite_true, mul_one, mul_inv_rev, hs, mul_assoc, simple_mul_cancel, simple_sq]
    · rw [longest_four Q hm 0 1 (by decide)]
      simp only [alternatingWord, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ite_false, ite_true, mul_one, mul_inv_rev, hs, mul_assoc, simple_mul_cancel, simple_sq]
  rw [rootIntersection, hw] at hprod
  exact hprod.symm

/-- The complementary section is generated by the three actual positive roots. -/
theorem remainder_eq_three_roots (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j) :
    simpleRemainder Q split i = simpleRoot Q split j ⊔
      rootAt Q split i (Q.simple j) ⊔ rootAt Q split j (Q.simple i) := by
  have hprod : (simpleRemainder Q split i : Set (X ⧸ Q.D)) =
      (simpleRoot Q split j : Set (X ⧸ Q.D)) *
        (rootAt Q split i (Q.simple j) : Set (X ⧸ Q.D)) *
        (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) := by
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hij rfl).elim
    · exact remainder_product Q split hm true
    · exact remainder_product Q split hm false
    · exact (hij rfl).elim
  apply le_antisymm
  · intro x hx
    change x ∈ (simpleRemainder Q split i : Set (X ⧸ Q.D)) at hx
    rw [hprod] at hx
    obtain ⟨y, ⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩ := hx
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left ha))
      (mem_sup_left (mem_sup_right hb))) (mem_sup_right hc)
  · exact sup_le (sup_le (opposite_roots_le_remainder Q split j i hij.symm).1
      (cross_root_le_own_remainder Q split hm i j hij))
      (opposite_roots_le_remainder Q split j i hij.symm).2

private theorem adjacent_product_bool (b : Bool) :
    ((simpleRoot Q split (if b then 1 else 0) ⊔
      rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0)) :
        Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
      (simpleRoot Q split (if b then 1 else 0) : Set (X ⧸ Q.D)) *
        (rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0)) : Set (X ⧸ Q.D)) := by
  have hprod := orderedRoots_product Q split b 2 (rotationOrder_ge_two Q)
  have hlist : orderedRoots Q split b 2 =
      [simpleRoot Q split (if b then 1 else 0),
       rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0))] := by
    cases b <;> rfl
  rw [hlist] at hprod
  change (simpleRoot Q split (if b then 1 else 0) : Set (X ⧸ Q.D)) *
    ((rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0)) : Set (X ⧸ Q.D)) * 1) = _ at hprod
  rw [mul_one] at hprod
  rw [sup_eq_closure_mul, hprod, closure_eq]

private theorem adjacent_product (i j : Fin 2) (hij : i ≠ j) :
    ((simpleRoot Q split i ⊔ rootAt Q split j (Q.simple i) : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
      (simpleRoot Q split i : Set (X ⧸ Q.D)) * (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) := by
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · exact adjacent_product_bool Q split false
  · exact adjacent_product_bool Q split true
  · exact (hij rfl).elim

private theorem adjacent_commutator_le (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    ⁅simpleRoot Q split i, rootAt Q split j (Q.simple i)⁆ ≤ rootAt Q split j (Q.simple i) := by
  have hD := (opposite_roots_le_remainder Q split j i hij.symm).2
  have hn := (simpleRoot_le Q split i).trans (split.U_le.trans
    ((Q.tits.B_le_standardParabolic _).trans (remainder_parabolic_normalizes Q split i hV)))
  have hC := (commutator_mono le_rfl hD).trans
    (le_normalizer_iff_commutator_le_right.mp hn)
  intro x hx
  have hxV := hC hx
  have hxprod : x ∈ ((simpleRoot Q split i ⊔ rootAt Q split j (Q.simple i) :
      Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) := commutator_le_sup _ _ hx
  rw [adjacent_product Q split i j hij] at hxprod
  obtain ⟨a,ha,d,hd,rfl⟩ := hxprod
  have haV : a ∈ simpleRemainder Q split i := by
    have := (simpleRemainder Q split i).mul_mem hxV
      ((simpleRemainder Q split i).inv_mem (hD hd))
    simpa only [mul_inv_cancel_right] using this
  have he : a = 1 := (disjoint_iff.mp (simpleRoot_disjoint_remainder Q split i)).le ⟨ha,haV⟩
  change a * d ∈ rootAt Q split j (Q.simple i)
  rw [he,one_mul]
  exact hd

/-- Consecutive roots in the positive ordering commute. -/
theorem adjacent_roots_commute (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j) :
    ⁅simpleRoot Q split i, rootAt Q split j (Q.simple i)⁆ = ⊥ := by
  have hfirst := adjacent_commutator_le Q split i j hij hVi
  have hother := adjacent_commutator_le Q split j i hij.symm hVj
  have h := comap_mono (f := (MulAut.conj (representative (Q.simple i) : X ⧸ Q.D)).toMonoidHom) hother
  change rightConjugate _ _ ≤ rightConjugate _ _ at h
  rw [conjugate_commutator, ← rootAt_eq Q split j (Q.simple i) _ (representative_spec _),
    cross_root_reflection_fixed Q split hm i j hij _ (representative_spec _)] at h
  have hh := comap_mono (f := (MulAut.conj (representative (Q.simple j) : X ⧸ Q.D)).toMonoidHom) h
  change rightConjugate _ _ ≤ rightConjugate _ _ at hh
  rw [conjugate_commutator,
    cross_root_reflection_fixed Q split hm j i hij.symm _ (representative_spec _),
    rootAt_right Q split i (Q.simple j) (Q.simple j) _ (representative_spec _),
    simple_sq, rootAt_one, commutator_comm] at hh
  exact bot_unique ((le_inf hh hfirst).trans
    (disjoint_iff.mp ((simpleRoot_disjoint_remainder Q split i).mono_right
      (opposite_roots_le_remainder Q split j i hij.symm).2)).le)

/-- The two middle positive roots commute, including nonabelian simple-root cases. -/
theorem middle_roots_commute (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j) :
    ⁅rootAt Q split i (Q.simple j), rootAt Q split j (Q.simple i)⁆ = ⊥ := by
  have h := congrArg (fun A => rightConjugate A (representative (Q.simple j) : X ⧸ Q.D))
    (adjacent_roots_commute Q split hm i j hij hVi hVj)
  rw [conjugate_commutator, ← rootAt_eq Q split i (Q.simple j) _ (representative_spec _),
    cross_root_reflection_fixed Q split hm j i hij.symm _ (representative_spec _)] at h
  exact h.trans (by rw [rightConjugate, comap_equiv_eq_map_symm', Subgroup.map_bot])

/-- The intervening root centralizes both commutator factors, so the
commutator lies in its intrinsic center embedded in the same quotient.
This supplies the center inclusion needed in (6A)(c), without abelian-root assumptions. -/
theorem cross_root_commutator_le_center (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ ≤
      (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype := by
  have hC := cross_root_commutator_le Q split hm i j hij hVi
  have hA := commutator_eq_bot_iff_le_centralizer.mp
    (adjacent_roots_commute Q split hm i j hij hVi hVj)
  have hB := commutator_eq_bot_iff_le_centralizer.mp
    (middle_roots_commute Q split hm i j hij hVi hVj)
  have hc := (commutator_le_sup (simpleRoot Q split i) (rootAt Q split i (Q.simple j))).trans
    (sup_le hA hB)
  intro x hx
  refine ⟨⟨x,hC hx⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact mem_centralizer_iff.mp (hc hx) y y.property

private theorem cross_root_elementary (i : Fin 2) (w : Weyl Q)
    (hc : IsElementaryAbelian 2 (simpleRoot Q split i)) :
    IsElementaryAbelian 2 (rootAt Q split i w) := by
  let := hc
  rw [rootAt, rightConjugate, comap_equiv_eq_map_symm']
  exact IsElementaryAbelian.map _

private theorem commutator_join_central (A C F : Subgroup (X ⧸ Q.D))
    (hCA : ⁅C,A⁆ = ⊥) (hCF : ⁅C,F⁆ = ⊥) : ⁅A ⊔ C,F⁆ = ⁅A,F⁆ := by
  have hCc : C ≤ centralizer ((A ⊔ F : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hCA))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hCF))
  have hn : A ⊔ C ≤ normalizer ((⁅A,F⁆ : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) :=
    sup_le (normalizer_commutator_ge_left _ _)
      ((hCc.trans (centralizer_le (commutator_le_sup _ _))).trans (centralizer_le_normalizer _))
  exact le_antisymm (commutator_sup_le_of_relative_normal (A ⊔ C) A C F ⁅A,F⁆ hn
    le_sup_left le_sup_right le_rfl (hCF ▸ bot_le)) (commutator_mono le_sup_left le_rfl)

/-- For elementary simple roots, the entire radical's derived and Frattini
subgroups are the literal opposite-root commutator. -/
theorem remainder_derived_frattini (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hUi : IsElementaryAbelian 2 (simpleRoot Q split i))
    (hUj : IsElementaryAbelian 2 (simpleRoot Q split j)) :
    ⁅simpleRemainder Q split i, simpleRemainder Q split i⁆ =
        ⁅simpleRoot Q split j, rootAt Q split j (Q.simple i)⁆ ∧
      (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype =
        ⁅simpleRoot Q split j, rootAt Q split j (Q.simple i)⁆ := by
  let A := simpleRoot Q split j
  let C := rootAt Q split i (Q.simple j)
  let F := rootAt Q split j (Q.simple i)
  let E := A ⊔ C
  let := hUj
  let : IsElementaryAbelian 2 C := cross_root_elementary Q split i _ hUi
  let : IsElementaryAbelian 2 F := cross_root_elementary Q split j _ hUj
  have hAC : ⁅A,C⁆ = ⊥ := adjacent_roots_commute Q split hm j i hij.symm hVj hVi
  have hCF : ⁅C,F⁆ = ⊥ := middle_roots_commute Q split hm i j hij hVi hVj
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.sup_of_le_centralizer
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hAC))
  have heq : E ⊔ F = simpleRemainder Q split i :=
    (remainder_eq_three_roots Q split hm i j hij).symm
  have hcross : ⁅E,F⁆ = ⁅A,F⁆ := commutator_join_central Q A C F
    ((commutator_comm C A).trans hAC) hCF
  have hFE : F ≤ normalizer (E : Set (X ⧸ Q.D)) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [hcross]
    exact (cross_root_commutator_le Q split hm j i hij.symm hVj).trans le_sup_right
  have hp : IsPGroup 2 (E ⊔ F : Subgroup (X ⧸ Q.D)) := by
    rw [heq]
    exact split.isTwo.of_injective (inclusion (show simpleRemainder Q split i ≤ split.U from inf_le_left))
      (inclusion_injective _)
  constructor
  · rw [← heq, commutator_join_of_abelian, hcross]
  · rw [← heq]
    exact (frattini_sup_eq_cross_of_elementary_normalizes E F hp hFE).trans hcross

/-- The earlier radical-derived order turns the (3G) inclusion into the exact
(6A)(b) equality, without any assumption on that root commutator itself. -/
theorem cross_root_commutator_eq_of_derived_card (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hUi : IsElementaryAbelian 2 (simpleRoot Q split i))
    (hUj : IsElementaryAbelian 2 (simpleRoot Q split j))
    (hcard : Nat.card (⁅simpleRemainder Q split i, simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) =
      Nat.card (simpleRoot Q split i)) :
    ⁅simpleRoot Q split j, rootAt Q split j (Q.simple i)⁆ = rootAt Q split i (Q.simple j) := by
  apply eq_of_le_of_card_ge (cross_root_commutator_le Q split hm j i hij.symm hVj)
  rw [← (remainder_derived_frattini Q split hm i j hij hVi hVj hUi hUj).1,
    rootAt, card_rightConjugate]
  exact hcard.ge

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
