module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Structure
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Context

/-!
# The elementary subgroups for exceptional normalizer control

We fix actual elementary subgroups F of order sixteen and V of order eight
inside the second permutation model. An index-two subgroup of the full local
group is specified by its action on an eight-point block. This is the other
transfer character: its involutions outside the kernel lie in F minus V.
The subgroup orders and elementary properties below are kernel checked.

Characteristicity in Q, the orbit calculation, and the ambient normalizer
argument are separate obligations. These definitions do not assert exclusion.
Source problem: Huppert--Blackburn III, XII.1.18(b), printed p.314.
-/

namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl
open NonsplitModels Model Subgroup

set_option maxRecDepth 100000

@[expose] public def fourRows (i : Fin 16) : Second :=
  element (![0, 1, 8, 9, 24, 25, 32, 33, 108, 109, 116, 117, 180, 181, 188, 189] i)

@[expose] public def threeRows (i : Fin 8) : Second :=
  element (![0, 1, 8, 9, 108, 109, 116, 117] i)

private theorem four_one : ∃ i, fourRows i = 1 := by decide +kernel
private theorem four_mul : ∀ i j, ∃ k, fourRows k = fourRows i * fourRows j := by
  decide +kernel
private theorem four_inv : ∀ i, ∃ j, fourRows j = (fourRows i)⁻¹ := by decide +kernel

/-- The concrete normal elementary subgroup of order sixteen. -/
@[expose] public def fourGroup : Subgroup Second where
  carrier := Set.range fourRows
  one_mem' := by exact four_one
  mul_mem' := by rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩; exact four_mul i j
  inv_mem' := by rintro _ ⟨i, rfl⟩; exact four_inv i

private theorem three_one : ∃ i, threeRows i = 1 := by decide +kernel
private theorem three_mul : ∀ i j, ∃ k, threeRows k = threeRows i * threeRows j := by
  decide +kernel
private theorem three_inv : ∀ i, ∃ j, threeRows j = (threeRows i)⁻¹ := by decide +kernel

/-- The distinguished subgroup of order eight inside `fourGroup`. -/
@[expose] public def threeGroup : Subgroup Second where
  carrier := Set.range threeRows
  one_mem' := by exact three_one
  mul_mem' := by rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩; exact three_mul i j
  inv_mem' := by rintro _ ⟨i, rfl⟩; exact three_inv i

public instance decidableMemFour : DecidablePred (· ∈ fourGroup) := fun x =>
  inferInstanceAs (Decidable (∃ i : Fin 16, fourRows i = x))

public instance decidableMemThree : DecidablePred (· ∈ threeGroup) := fun x =>
  inferInstanceAs (Decidable (∃ i : Fin 8, threeRows i = x))

public theorem fourGroup_card : Nat.card fourGroup = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

public theorem threeGroup_card : Nat.card threeGroup = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

public theorem fourGroup_square (x : Second) (hx : x ∈ fourGroup) : x ^ 2 = 1 := by
  obtain ⟨i, rfl⟩ := hx
  exact (by decide +kernel : ∀ i, fourRows i ^ 2 = 1) i

public theorem fourGroup_comm (x y : Second) (hx : x ∈ fourGroup) (hy : y ∈ fourGroup) :
    x * y = y * x := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  exact (by decide +kernel : ∀ i j, fourRows i * fourRows j = fourRows j * fourRows i) i j

public theorem threeGroup_le_fourGroup : threeGroup ≤ fourGroup := by
  rintro _ ⟨i, rfl⟩
  exact (by decide +kernel : ∀ i, threeRows i ∈ fourGroup) i

public theorem fourGroup_le_exceptionalSubgroup : fourGroup ≤ exceptionalSubgroup := by
  rintro _ ⟨i, rfl⟩
  exact (by decide +kernel : ∀ i, fourRows i ∈ exceptionalSubgroup) i

public theorem centralPoint_mem_threeGroup : centralPoint ∈ threeGroup := by decide +kernel
public theorem exceptionalPoint_mem_threeGroup : exceptionalPoint ∈ threeGroup := by decide +kernel

/-- The two colors of the model's preserved block system. -/
@[expose] public def blockColor (i : Fin 16) : Bool :=
  i ∈ ({0, 2, 3, 4, 8, 9, 10, 11} : Finset (Fin 16))

/-- The block kernel giving the alternative transfer character. -/
@[expose] public def blockKernel : Subgroup Second where
  carrier := {x | ∀ i : Fin 16, blockColor (x.val i) = blockColor i}
  one_mem' := by intro i; rfl
  mul_mem' := by
    intro x y hx hy i
    change blockColor (x.val (y.val i)) = blockColor i
    rw [hx, hy]
  inv_mem' := by
    intro x hx i
    have h := hx (x.val⁻¹ i)
    change blockColor (x.val⁻¹ i) = blockColor i
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h.symm

public instance decidableMemBlock : DecidablePred (· ∈ blockKernel) := fun x =>
  inferInstanceAs (Decidable (∀ i : Fin 16, blockColor (x.val i) = blockColor i))

public theorem blockKernel_card : Nat.card blockKernel = 192 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

public theorem blockKernel_index : blockKernel.index = 2 := by
  have h := blockKernel.index_mul_card
  rw [blockKernel_card, Model.card] at h
  omega

/-- An involution in F outside V, and outside the block kernel. -/
@[expose] public def outsidePoint : Second := element 24

public theorem outsidePoint_mem_fourGroup : outsidePoint ∈ fourGroup := by decide +kernel
public theorem outsidePoint_not_mem_threeGroup : outsidePoint ∉ threeGroup := by decide +kernel
public theorem outsidePoint_not_mem_blockKernel : outsidePoint ∉ blockKernel := by decide +kernel
public theorem outsidePoint_order : orderOf outsidePoint = 2 :=
  orderOf_eq_prime (fourGroup_square outsidePoint outsidePoint_mem_fourGroup) (by decide +kernel)

/-- The non-square local involution whose fusion is forced by an exceptional action. -/
@[expose] public def outerPoint : Second := element 20

/-- A local square involution in Q outside F. -/
@[expose] public def squarePoint : Second := element 48

public theorem squarePoint_mem_exceptionalSubgroup : squarePoint ∈ exceptionalSubgroup := by
  decide +kernel
public theorem squarePoint_not_mem_fourGroup : squarePoint ∉ fourGroup := by decide +kernel
public theorem squarePoint_order : orderOf squarePoint = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)
public theorem squarePoint_root : (element 163) ^ 2 = squarePoint := by decide +kernel
public theorem squarePoint_commuting_root :
    element 36 ∈ exceptionalSubgroup ∧
    element 36 * squarePoint = squarePoint * element 36 ∧
    (element 36) ^ 2 = centralPoint := by decide +kernel

public theorem outerPoint_order : orderOf outerPoint = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private def rootRow (i : Fin 384) : Fin 384 :=
  ⟨(11899788277317751494448974664013367829786902830861263856177789561169722245910350408217637934778439291753854639706319411231754756859691049343963360897943079085419813837133232869003217925018275874202829799887806623994969246301224521792319535891764276207515333404077612756249936344012721392819371333190397862623925108349136465330432403299268859872156361345540052793880209221101523505778365272207488339283553448137900149541424827179018416659535256018754206257346888070575164851739474518611931608105748215348747177732724078407283329262340184146620077573178411861435301498661420729080403918078743359815990871859445080017840582226850343207228062265938951057402253622311484041136634976068373596474241150987911853383251385041665671419006099998937757 / 384 ^ i.val) % 384, Nat.mod_lt _ (by decide)⟩

private def conjugatorRow (i : Fin 384) : Fin 384 :=
  ⟨(448810070516358278670146620796219658809024051307969764555954757983581433127915268408010974446542631169013918052150263342382688524287751923044216117226231951465406294702317697283925007409358799696065812278631023930762837494844181302381753509443158315155481978651997707275688400859657274954518106076506694235548679804721634824631083147262580642729282177537419203853369055644393609794795673077547044303637987679134326235887964801861676666780193527033501724884864260180001283009888579768567457601176974043801902051436625357677451833201395474791568347137424719653601190402741162011415255689775011083205822331094473410356639976512269666693604002236831126113472490439742497354808012089743739543571257489651394865528832 / 384 ^ i.val) % 384, Nat.mod_lt _ (by decide)⟩


private theorem kernel_rows : ∀ i : Fin 384,
    element i ∈ blockKernel → (element i) ^ 2 = 1 →
      (element (rootRow i)) ^ 2 = element i ∨
      element (conjugatorRow i) * outerPoint * (element (conjugatorRow i))⁻¹ = element i := by
  decide +kernel

/-- Every involution in the block kernel is a square or locally conjugate to
`outerPoint`. The identity is allowed in this version. -/
public theorem blockKernel_square_or_conjugate (x : Second) (hx : x ∈ blockKernel)
    (hx2 : x ^ 2 = 1) :
    (∃ r : Second, r ^ 2 = x) ∨ IsConj outerPoint x := by
  obtain ⟨i, rfl⟩ := element_bijective.2 x
  rcases kernel_rows i hx hx2 with hr | hc
  · exact Or.inl ⟨element (rootRow i), hr⟩
  · exact Or.inr (isConj_iff.mpr ⟨element (conjugatorRow i), hc⟩)

/-- The elementary subgroup with its actual embedding in the ambient group. -/
@[expose] public def ambientFourGroup {G : Type*} [Group G] (D : LocalData G)
    (e : D.centralizer ≃* Second) : Subgroup G := fourGroup.map (embedding D e)

public theorem ambientFourGroup_card {G : Type*} [Group G] (D : LocalData G)
    (e : D.centralizer ≃* Second) : Nat.card (ambientFourGroup D e) = 16 := by
  rw [ambientFourGroup, card_map_of_injective (embedding_injective D e), fourGroup_card]

end Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl
