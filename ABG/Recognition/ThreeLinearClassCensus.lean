module

public import ABG.Recognition.ThreeMathieuEvenClasses
public import ABG.Recognition.ThreeLinearThirteenClasses
public import ABG.Recognition.ThreeCharacterDegreeInventory

/-!
# Class counting in Wong's order-5616 branch

The five transported GL₂(3) root classes remain distinct in the ambient group.
Their local centralizers are their ambient centralizers, so orbit–stabilizer
computes the five class sizes. We retain actual conjugacy classes as a finite
set, permitting subsequent class-function sums to use the original catalog.
The four order-thirteen classes then leave two classes of total size 728.
Element-order divisibility shows that their orders lie among 3, 9 and 27.

Source: W. J. Wong, “On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2” (1964), Appendix (b), p.108,
DOI 10.1017/S1446788700022771.
-/

namespace ABG.ThreeGlobalDegreeData
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)

/-- The five even classes, with the same indexing as the transported local
representatives: orders 2, 4, 6, 8, 8. -/
public def evenClass (i : Fin 5) : ConjClasses G :=
  ConjClasses.mk (c.evenRepresentative i : G)

/-- The class is represented by the corresponding transported even element. -/
public theorem evenClass_eq (i : Fin 5) :
    c.evenClass i = ConjClasses.mk (c.evenRepresentative i : G) := by rfl

/-- In particular, the two classes of elements of order eight do not fuse. -/
public theorem evenClass_injective : Function.Injective c.evenClass := by
  intro i j h
  exact c.evenRepresentative_not_fused i j (ConjClasses.mk_eq_mk_iff_isConj.mp h)

/-- The class sizes in the order-5616 branch. -/
public theorem evenClass_card (hG : Nat.card G = 5616) (i : Fin 5) :
    Nat.card (c.evenClass i).carrier = ![117,702,936,702,702] i := by
  have h := class_card_mul_centralizer_card (c.evenRepresentative i : G)
  have he : Nat.card {x : G // x * (c.evenRepresentative i : G) =
      (c.evenRepresentative i : G) * x} =
      Nat.card (Subgroup.centralizer ({(c.evenRepresentative i : G)} : Set G)) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun x => Subgroup.mem_centralizer_singleton_iff.symm
  rw [he, c.evenRepresentative_centralizer_card, hG] at h
  change Nat.card (c.evenClass i).carrier * ![48,8,6,8,8] i = 5616 at h
  fin_cases i <;> norm_num at h ⊢ <;> omega

/-- Actual finite set of the five even conjugacy classes. -/
public def evenClasses : Finset (ConjClasses G) :=
  Finset.univ.map ⟨c.evenClass, c.evenClass_injective⟩

public theorem mem_evenClasses (k : ConjClasses G) :
    k ∈ c.evenClasses ↔ ∃ i, c.evenClass i = k := by
  classical
  simp [evenClasses]

public theorem card_evenClasses : c.evenClasses.card = 5 := by
  simp [evenClasses]

/-- Membership in the finite class set characterizes even element order. -/
public theorem mk_mem_evenClasses_iff [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (x : G) :
    ConjClasses.mk x ∈ c.evenClasses ↔ 2 ∣ orderOf x := by
  rw [c.mem_evenClasses]
  constructor
  · rintro ⟨i, hi⟩
    have hc := ConjClasses.mk_eq_mk_iff_isConj.mp hi
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    have ho : orderOf x = ![2,4,6,8,8] i := by
      rw [← hg]
      exact (MulAut.conj g).orderOf_eq _ |>.trans (c.evenRepresentative_order i)
    rw [ho]
    fin_cases i <;> norm_num
  · intro hx
    obtain ⟨i, hi, _⟩ := c.even_conjugacy_coverage S hS x hx
    exact ⟨i, ConjClasses.mk_eq_mk_iff_isConj.mpr hi.symm⟩

/-- A finite sum over the even classes uses exactly the five supplied
representatives, without choosing a new class enumeration. -/
public theorem sum_evenClasses {M : Type*} [AddCommMonoid M]
    (f : ConjClasses G → M) :
    ∑ k ∈ c.evenClasses, f k = ∑ i : Fin 5, f (c.evenClass i) := by
  exact Finset.sum_map _ _ _

/-- Weighted class sums use the explicit class sizes in Wong's calculation. -/
public theorem weighted_sum_evenClasses {M : Type*} [AddCommMonoid M]
    (hG : Nat.card G = 5616) (f : ConjClasses G → M) :
    ∑ k ∈ c.evenClasses, Nat.card k.carrier • f k =
      117 • f (c.evenClass 0) + 702 • f (c.evenClass 1) +
        936 • f (c.evenClass 2) + 702 • f (c.evenClass 3) +
          702 • f (c.evenClass 4) := by
  rw [c.sum_evenClasses]
  simp only [c.evenClass_card hG]
  simp [Fin.sum_univ_succ, add_assoc]

/-- The five even classes account for 3159 elements. -/
public theorem sum_evenClasses_card (hG : Nat.card G = 5616) :
    ∑ k ∈ c.evenClasses, Nat.card k.carrier = 3159 := by
  rw [c.sum_evenClasses]
  simp only [c.evenClass_card hG]
  norm_num [Fin.sum_univ_succ]

/-- The identity class is separate from the five even classes. -/
public theorem identity_not_mem_evenClasses : ConjClasses.mk (1 : G) ∉ c.evenClasses := by
  rw [c.mem_evenClasses]
  rintro ⟨i, hi⟩
  have h := ConjClasses.mk_eq_mk_iff_isConj.mp hi
  have he : (c.evenRepresentative i : G) = 1 := isConj_one_left.mp h
  have ho := c.evenRepresentative_order i
  rw [he, orderOf_one] at ho
  fin_cases i <;> norm_num at ho

/-- The classes still to be analyzed after the identity and even classes. -/
public def oddNonidentityClasses : Finset (ConjClasses G) := by
  classical
  exact (insert (ConjClasses.mk (1 : G)) c.evenClasses)ᶜ

public theorem mem_oddNonidentityClasses (k : ConjClasses G) :
    k ∈ c.oddNonidentityClasses ↔ k ≠ ConjClasses.mk (1 : G) ∧ k ∉ c.evenClasses := by
  classical
  simp [oddNonidentityClasses]

/-- Element-level coverage for the six classes left to analyze. -/
public theorem mk_mem_oddNonidentityClasses_iff [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (x : G) :
    ConjClasses.mk x ∈ c.oddNonidentityClasses ↔ x ≠ 1 ∧ ¬ 2 ∣ orderOf x := by
  simp only [c.mem_oddNonidentityClasses, c.mk_mem_evenClasses_iff S hS,
    ne_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left]

/-- Exactly six classes remain after the identity and the five even classes. -/
public theorem card_oddNonidentityClasses (hG : Nat.card G = 5616) :
    c.oddNonidentityClasses.card = 6 := by
  classical
  have h := Finset.card_compl_add_card (insert (ConjClasses.mk (1 : G)) c.evenClasses)
  rw [Finset.card_insert_of_notMem c.identity_not_mem_evenClasses,
    c.card_evenClasses, ← Nat.card_eq_fintype_card, c.card_conjClasses hG] at h
  change c.oddNonidentityClasses.card + (5 + 1) = 12 at h
  omega

private theorem sum_class_card : ∑ k : ConjClasses G, Nat.card k.carrier = Nat.card G := by
  classical
  let e : (Σ k : ConjClasses G, k.carrier) ≃ G :=
    (Equiv.sigmaCongrRight (fun k => Equiv.subtypeEquivRight
      (fun _ => ConjClasses.mem_carrier_iff_mk_eq))).trans
      (Equiv.sigmaFiberEquiv ConjClasses.mk)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sigma] using Nat.card_congr e

omit [Finite G] in
private theorem identity_class_card : Nat.card (ConjClasses.mk (1 : G)).carrier = 1 := by
  have he : (ConjClasses.mk (1 : G)).carrier = ({1} : Set G) := by
    ext x
    change IsConj (1 : G) x ↔ x = 1
    exact isConj_one_right
  rw [he]
  simp

/-- The six odd nonidentity classes account for 2456 elements. -/
public theorem sum_oddNonidentityClasses_card (hG : Nat.card G = 5616) :
    ∑ k ∈ c.oddNonidentityClasses, Nat.card k.carrier = 2456 := by
  classical
  have h := Finset.sum_compl_add_sum (insert (ConjClasses.mk (1 : G)) c.evenClasses)
    (fun k => Nat.card k.carrier)
  rw [Finset.sum_insert c.identity_not_mem_evenClasses, identity_class_card,
    c.sum_evenClasses_card hG, sum_class_card, hG] at h
  change (∑ k ∈ c.oddNonidentityClasses, Nat.card k.carrier) + (1 + 3159) = 5616 at h
  omega


/-- The two classes left after the identity, even classes and thirteen classes. -/
public def remainingThreeClasses : Finset (ConjClasses G) := by
  classical
  exact c.oddNonidentityClasses \ threeLinearThirteenClasses G

public theorem mem_remainingThreeClasses (k : ConjClasses G) :
    k ∈ c.remainingThreeClasses ↔
      k ∈ c.oddNonidentityClasses ∧ k ∉ threeLinearThirteenClasses G := by
  classical
  simp [remainingThreeClasses]

/-- Element-level membership before reducing the possible odd orders. -/
public theorem mk_mem_remainingThreeClasses_iff [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (x : G) :
    ConjClasses.mk x ∈ c.remainingThreeClasses ↔
      (x ≠ 1 ∧ ¬ 2 ∣ orderOf x) ∧ orderOf x ≠ 13 := by
  rw [c.mem_remainingThreeClasses, c.mk_mem_oddNonidentityClasses_iff S hS,
    mem_threeLinearThirteenClasses]

/-- The order-thirteen classes belong to the six odd nonidentity classes. -/
public theorem thirteenClasses_subset_oddNonidentityClasses [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) :
    threeLinearThirteenClasses G ⊆ c.oddNonidentityClasses := by
  intro k hk
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective k
  have hx := (mem_threeLinearThirteenClasses x).mp hk
  rw [c.mk_mem_oddNonidentityClasses_iff S hS]
  constructor
  · intro he
    simp [he] at hx
  · rw [hx]
    decide

/-- The degree inventory leaves exactly two classes. -/
public theorem card_remainingThreeClasses [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616) : c.remainingThreeClasses.card = 2 := by
  classical
  rw [remainingThreeClasses, Finset.card_sdiff_of_subset
    (c.thirteenClasses_subset_oddNonidentityClasses S hS),
    c.card_oddNonidentityClasses hG, c.linear_thirteen_classes_card S hS hG]

/-- The two remaining classes together contain 728 elements. -/
public theorem sum_remainingThreeClasses_card [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616) :
    ∑ k ∈ c.remainingThreeClasses, Nat.card k.carrier = 728 := by
  classical
  have h := Finset.sum_sdiff (c.thirteenClasses_subset_oddNonidentityClasses S hS)
    (f := fun k => Nat.card k.carrier)
  rw [c.sum_oddNonidentityClasses_card hG, c.linear_thirteen_class_sum S hS hG] at h
  change (∑ k ∈ c.remainingThreeClasses, Nat.card k.carrier) + 1728 = 2456 at h
  omega

/-- Orders in the remaining classes can only be 3, 9 or 27. -/
public theorem remainingThreeClasses_order [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616) (x : G)
    (hx : ConjClasses.mk x ∈ c.remainingThreeClasses) :
    orderOf x = 3 ∨ orderOf x = 9 ∨ orderOf x = 27 := by
  obtain ⟨⟨hne, heven⟩, h13⟩ := (c.mk_mem_remainingThreeClasses_iff S hS x).mp hx
  have hn1 : orderOf x ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  have hn13 : ¬ 13 ∣ orderOf x := fun h =>
    h13 (c.linear_order_eq_thirteen_of_dvd S hS hG x h)
  have hd : orderOf x ∈ Nat.divisors 5616 :=
    Nat.mem_divisors.mpr ⟨hG ▸ orderOf_dvd_natCard x, by decide⟩
  have divs : Nat.divisors 5616 =
    {1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18, 24, 26, 27, 36, 39, 48, 52,
      54, 72, 78, 104, 108, 117, 144, 156, 208, 216, 234, 312, 351, 432,
      468, 624, 702, 936, 1404, 1872, 2808, 5616} := by
      set_option maxRecDepth 4096 in decide
  rw [divs] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  omega

/-- The remaining class set consists precisely of the nontrivial 3-power orders. -/
public theorem mk_mem_remainingThreeClasses_iff_order [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616) (x : G) :
    ConjClasses.mk x ∈ c.remainingThreeClasses ↔
      orderOf x = 3 ∨ orderOf x = 9 ∨ orderOf x = 27 := by
  constructor
  · exact c.remainingThreeClasses_order S hS hG x
  · intro hx
    rw [c.mk_mem_remainingThreeClasses_iff S hS]
    have hn : orderOf x ≠ 1 := by omega
    have hne : x ≠ 1 := fun h => hn (orderOf_eq_one_iff.mpr h)
    exact ⟨⟨hne, by rcases hx with h | h | h <;> simp [h]⟩, by omega⟩

/-- A class sum splits into the identity, five even, four thirteen and two
remaining classes. This formula also applies to carrier-weighted sums. -/
public theorem sum_class_census {M : Type*} [AddCommMonoid M] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (f : ConjClasses G → M) :
    ∑ k : ConjClasses G, f k = f (ConjClasses.mk (1 : G)) +
      (∑ k ∈ c.evenClasses, f k) + (∑ k ∈ threeLinearThirteenClasses G, f k) +
        ∑ k ∈ c.remainingThreeClasses, f k := by
  classical
  have h := Finset.sum_compl_add_sum (insert (ConjClasses.mk (1 : G)) c.evenClasses) f
  rw [Finset.sum_insert c.identity_not_mem_evenClasses] at h
  have ho := Finset.sum_sdiff (c.thirteenClasses_subset_oddNonidentityClasses S hS) (f := f)
  change (∑ k ∈ c.remainingThreeClasses, f k) +
    (∑ k ∈ threeLinearThirteenClasses G, f k) =
      ∑ k ∈ c.oddNonidentityClasses, f k at ho
  change (∑ k ∈ c.oddNonidentityClasses, f k) +
    (f (ConjClasses.mk (1 : G)) + ∑ k ∈ c.evenClasses, f k) = _ at h
  rw [← ho] at h
  simpa only [add_assoc, add_comm, add_left_comm] using h.symm

/-- Explicit weights for the nine nonidentity classes already determined. -/
public theorem weighted_sum_class_census {M : Type*} [AddCommMonoid M] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616) (f : ConjClasses G → M) :
    ∑ k : ConjClasses G, Nat.card k.carrier • f k = f (ConjClasses.mk (1 : G)) +
      (117 • f (c.evenClass 0) + 702 • f (c.evenClass 1) +
        936 • f (c.evenClass 2) + 702 • f (c.evenClass 3) + 702 • f (c.evenClass 4)) +
      (∑ k ∈ threeLinearThirteenClasses G, 432 • f k) +
        ∑ k ∈ c.remainingThreeClasses, Nat.card k.carrier • f k := by
  rw [c.sum_class_census S hS, identity_class_card, one_nsmul,
    c.weighted_sum_evenClasses hG]
  congr 2
  exact Finset.sum_congr rfl (fun k hk => by
    rw [c.linear_thirteen_carrier_card S hS hG k hk])

end
end ABG.ThreeGlobalDegreeData
