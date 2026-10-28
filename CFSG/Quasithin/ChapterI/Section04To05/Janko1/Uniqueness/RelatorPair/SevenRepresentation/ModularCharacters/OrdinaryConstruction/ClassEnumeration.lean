module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration.Blocks
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration.FixedOrder
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration.LocalClasses
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration.LargePrimeClasses
public import Theory.GroupTheory.ConjugacyOrderCensus

/-!
# Exhaustion in the J₁ class calculation

The prescribed centralizer orders give class sizes summing to 175560.
Consequently fifteen pairwise nonconjugate representatives with those
centralizer orders exhaust the group. We prove this by injecting the disjoint
union of their class carriers into the group and comparing cardinalities;
the resulting equivalence is the literal one required by `OrdinaryClassData`.

The identity and involution columns are constructed from the source local
data. The local and large-prime constructions supply the other thirteen
representatives. `nonempty_ordinaryClassData_of_order` combines these blocks
and exhaustion to complete the arbitrary-group class enumeration from the
source local data, simplicity, supplied order and involution fusion.
No character or recognition theorem is used.

Source: Janko, J. Algebra 3 (1966), 147–186; Gorenstein, *Finite Groups*,
§16.6, printed p.482. The latter confirms the arbitrary-group calculation
but omits its details. The two order lists are specified in `OrdinaryData`.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters

open scoped BigOperators

variable {G : Type*} [Group G] [Finite G]

/-- The centralizer orders account for every element of the source group. -/
public theorem class_size_sum :
    ∑ i : Fin 15, 175560 / centralizerOrder i = 175560 := by
  norm_num [Fin.sum_univ_succ, centralizerOrder]

/-- Distinct representatives with the prescribed centralizers automatically
exhaust the group of the supplied order. -/
public theorem class_representatives_bijective (horder : Nat.card G = 175560)
    (r : Fin 15 → G)
    (hd : Function.Injective (fun i => ConjClasses.mk (r i)))
    (hc : ∀ i, Nat.card (Subgroup.centralizer ({r i} : Set G)) = centralizerOrder i) :
    Function.Bijective (fun i => ConjClasses.mk (r i)) := by
  classical
  have hsize (i : Fin 15) :
      Nat.card (ConjClasses.mk (r i)).carrier = 175560 / centralizerOrder i := by
    have hpos : 0 < centralizerOrder i := by fin_cases i <;> decide
    have he := ConjClasses.nat_card_carrier_mul_card_centralizer (r i)
    rw [hc, horder] at he
    rw [← he, Nat.mul_div_cancel _ hpos]
  let f : (Σ i : Fin 15, (ConjClasses.mk (r i)).carrier) → G := fun x => x.2.val
  have hinj : Function.Injective f := by
    rintro ⟨i, x⟩ ⟨j, y⟩ he
    have hxy : x.val = y.val := he
    have hij : i = j := hd ((ConjClasses.mem_carrier_iff_mk_eq.mp x.property).symm.trans
      ((congrArg ConjClasses.mk hxy).trans
        (ConjClasses.mem_carrier_iff_mk_eq.mp y.property)))
    subst j
    congr 1
    exact Subtype.ext hxy
  have hcard : Nat.card (Σ i : Fin 15, (ConjClasses.mk (r i)).carrier) = Nat.card G := by
    rw [Nat.card_sigma, horder]
    simp_rw [hsize]
    exact class_size_sum
  have hsurj := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩).2
  refine ⟨hd, ?_⟩
  intro c
  obtain ⟨x, rfl⟩ := ConjClasses.exists_rep c
  obtain ⟨⟨i, y⟩, hy⟩ := hsurj x
  exact ⟨i, (ConjClasses.mem_carrier_iff_mk_eq.mp y.property).symm.trans
    (congrArg ConjClasses.mk hy)⟩

/-- Construct the actual class equivalence by the class-size exhaustion proof. -/
public noncomputable def ordinaryClassDataOfRepresentatives
    (horder : Nat.card G = 175560) (r : Fin 15 → G)
    (hd : Function.Injective (fun i => ConjClasses.mk (r i)))
    (hi : r 0 = 1) (ho : ∀ i, orderOf (r i) = classOrder i)
    (hc : ∀ i, Nat.card (Subgroup.centralizer ({r i} : Set G)) = centralizerOrder i) :
    OrdinaryClassData G where
  representatives := r
  classes := Equiv.ofBijective _ (class_representatives_bijective horder r hd hc)
  classes_eq _ := rfl
  identity := hi
  orders := ho
  centralizers := hc

open ClassEnumeration

private def blockRepresentatives (h : Janko1CentralizerData G)
    (a : LocalBlocks G) (b : LargePrimeBlocks G) : Fin 15 → G :=
  ![1, h.z, a.three.representatives 0, a.five.representatives 0, a.five.representatives 1,
    a.six.representatives 0, b.seven.representatives 0,
    a.ten.representatives 0, a.ten.representatives 1, b.eleven.representatives 0,
    a.fifteen.representatives 0, a.fifteen.representatives 1,
    b.nineteen.representatives 0, b.nineteen.representatives 1, b.nineteen.representatives 2]

private theorem blockRepresentatives_orders (h : Janko1CentralizerData G)
    (a : LocalBlocks G) (b : LargePrimeBlocks G) (i : Fin 15) :
    orderOf (blockRepresentatives h a b i) = classOrder i := by
  fin_cases i <;> simp [blockRepresentatives, classOrder, h.involution,
    a.three.orders, a.five.orders, a.six.orders, a.ten.orders, a.fifteen.orders,
    b.seven.orders, b.eleven.orders, b.nineteen.orders]

private theorem blockRepresentatives_centralizers (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560)
    (a : LocalBlocks G) (b : LargePrimeBlocks G) (i : Fin 15) :
    Nat.card (Subgroup.centralizer ({blockRepresentatives h a b i} : Set G)) =
      centralizerOrder i := by
  have hC : Subgroup.centralizer ({1} : Set G) = ⊤ := by
    ext x
    simp [Subgroup.mem_centralizer_singleton_iff]
  fin_cases i <;> simp [blockRepresentatives, centralizerOrder, h.centralizer_card, hC,
    horder, a.three.centralizers, a.five.centralizers, a.six.centralizers,
    a.ten.centralizers, a.fifteen.centralizers,
    b.seven.centralizers, b.eleven.centralizers, b.nineteen.centralizers]

private theorem blockRepresentatives_distinct (h : Janko1CentralizerData G)
    (a : LocalBlocks G) (b : LargePrimeBlocks G) :
    Function.Injective (fun i => ConjClasses.mk (blockRepresentatives h a b i)) := by
  intro i j he
  have ho : classOrder i = classOrder j := by
    obtain ⟨g, hg⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp he)
    rw [← blockRepresentatives_orders h a b i, ← blockRepresentatives_orders h a b j,
      ← hg]
    exact ((MulAut.conj g).orderOf_eq _).symm
  fin_cases i <;> fin_cases j <;> norm_num [classOrder] at ho
  all_goals first | rfl | skip
  all_goals simp only [blockRepresentatives] at he
  all_goals first
    | have hd := a.five.distinct he; cases hd
    | have hd := a.ten.distinct he; cases hd
    | have hd := a.fifteen.distinct he; cases hd
    | have hd := b.nineteen.distinct he; cases hd

/-- Assemble the actual class enumeration from the independent blocks.
The identity and distinguished involution are constructed here; class-size
exhaustion supplies surjectivity. Existence of the two blocks remains required. -/
public noncomputable def ordinaryClassDataOfBlocks (h : Janko1CentralizerData G) (horder : Nat.card G = 175560)
    (a : LocalBlocks G) (b : LargePrimeBlocks G) : OrdinaryClassData G :=
  ordinaryClassDataOfRepresentatives horder (blockRepresentatives h a b)
    (blockRepresentatives_distinct h a b) rfl (blockRepresentatives_orders h a b)
    (blockRepresentatives_centralizers h horder a b)

/-- The conditional assembly, retaining the independently useful block interface. -/
public theorem nonempty_ordinaryClassData_of_blocks
    (h : Janko1CentralizerData G) (horder : Nat.card G = 175560)
    (a : Nonempty (LocalBlocks G)) (b : Nonempty (LargePrimeBlocks G)) :
    Nonempty (OrdinaryClassData G) := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  exact ⟨ordinaryClassDataOfBlocks h horder a b⟩

/-- The fifteen actual conjugacy classes of the arbitrary source group, with
the prescribed representatives, element orders and ambient centralizer orders.
Both block constructions and class-size exhaustion are discharged from the
source hypotheses; no class, character or recognition premise remains. -/
public theorem nonempty_ordinaryClassData_of_order [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (horder : Nat.card G = 175560)
    (hfusion : ∀ x : G, orderOf x = 2 → ∃ g : G, g * x * g⁻¹ = h.z) :
    Nonempty (OrdinaryClassData G) :=
  nonempty_ordinaryClassData_of_blocks h horder
    (localBlocks_nonempty h horder hfusion)
    (nonempty_largePrimeBlocks_of_order h horder hfusion)

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
