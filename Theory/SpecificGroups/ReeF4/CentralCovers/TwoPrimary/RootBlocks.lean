module

public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Curves

/-!
# The eight actual positive Ree block groups

The four paired root groups are additive. The other four are nonabelian
B₂ groups with main and central parameters. Associativity of the established
main-curve product law proves that the central curve commutes with the main
curve. This gives the full block multiplication law and its two-coordinate
normal form, without a new matrix certificate.

Every element of each actual generated subgroup Xᵢ has that normal form.
The existing twelve-coordinate uniqueness then proves that the ordered
product of all eight subgroup carriers is bijective onto the literal fixed
positive subgroup. This is the coordinate input for collection in a central
extension; no assertion about lifting relations is made here.

The order is pairs 8, 2, 6, 4, then B₂ blocks 1, 5, 7, 3 in source numbering.
The B₂ correction is titsEnd(a)*b, with the existing centralWord convention.
All these coordinate results include m = 0, the full binary fixed group.

Source: GLS3 §2.4, especially Table 2.4 and 2.4.5(d), in
`refs/KGroup/GLS3/chapter2.tex`. The covering application is the defining-prime
part of GLS3 §6.1 used in Aschbacher–Smith I.1.3, printed p.407.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace ReeF4.CentralCovers.TwoPrimary
open ElementaryTwoBound ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics.RadicalCoordinates.FixedCoordinates

theorem main_mul (m : ℕ) (i : Fin 8) (hi : i.val % 2 = 0)
    (a b : CoefficientField m) :
    mainElement m i a * mainElement m i b =
      mainElement m i (a + b) * centralElement m i (titsEnd m a * b) :=
  Subtype.ext (MatrixRelations.rootWord_even_mul m i hi a b)

theorem main_central_commute (m : ℕ) (i : Fin 8) (hi : i.val % 2 = 0)
    (a b : CoefficientField m) :
    Commute (mainElement m i a) (centralElement m i b) := by
  have h := mul_assoc (mainElement m i 1) (mainElement m i b) (mainElement m i a)
  rw [main_mul m i hi 1 b, map_one, one_mul, main_mul m i hi b a,
    ← mul_assoc, main_mul m i hi 1 (b + a), map_one, one_mul] at h
  have h' : mainElement m i (1 + b) *
      (centralElement m i b * mainElement m i a) =
      mainElement m i (1 + b) *
      (mainElement m i a * centralElement m i b) := by
    calc
      _ = mainElement m i (1 + (b + a)) *
          centralElement m i (b + a) * centralElement m i (titsEnd m b * a) := by
        simpa only [mul_assoc] using h
      _ = mainElement m i ((1 + b) + a) *
          centralElement m i ((b + a) + titsEnd m b * a) := by
        rw [add_assoc, centralElement_add m i hi (b + a)]
        exact mul_assoc _ _ _
      _ = mainElement m i (1 + b) *
          (mainElement m i a * centralElement m i b) := by
        rw [← mul_assoc, main_mul m i hi, mul_assoc,
          ← centralElement_add m i hi, map_add, map_one]
        congr 2
        ring
  exact (mul_left_cancel h').symm

def blockPoint (m : ℕ) (i : Fin 8) (a b : CoefficientField m) : Model m :=
  mainElement m i a * centralElement m i b

theorem blockPoint_mul (m : ℕ) (i : Fin 8) (hi : i.val % 2 = 0)
    (a b c d : CoefficientField m) :
    blockPoint m i a b * blockPoint m i c d =
      blockPoint m i (a + c) (titsEnd m a * c + (b + d)) := by
  simp only [blockPoint]
  rw [(main_central_commute m i hi c b).symm.mul_mul_mul_comm,
    main_mul m i hi, ← centralElement_add m i hi,
    mul_assoc, ← centralElement_add m i hi]

private def blockSubgroup (m : ℕ) (i : Fin 8) (hi : i.val % 2 = 0) : Subgroup (Model m) where
  carrier := {x | ∃ a b, blockPoint m i a b = x}
  one_mem' := ⟨0, 0, by simp [blockPoint]⟩
  mul_mem' := by
    rintro x y ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
    exact ⟨a+c, titsEnd m a * c + (b+d), (blockPoint_mul m i hi a b c d).symm⟩
  inv_mem' := by
    rintro x ⟨a,b,rfl⟩
    refine ⟨a, titsEnd m a * a + b, ?_⟩
    apply eq_inv_of_mul_eq_one_left
    rw [blockPoint_mul m i hi]
    have hscalar : titsEnd m a * a + (titsEnd m a * a + b + b) = 0 := by
      rw [add_assoc (titsEnd m a * a) b b, CharTwo.add_self_eq_zero, add_zero,
        CharTwo.add_self_eq_zero]
    simp only [CharTwo.add_self_eq_zero, hscalar, blockPoint,
      mainElement_zero, centralElement_zero, mul_one]

theorem mem_X_even (m : ℕ) (i : Fin 8) (hi : i.val % 2 = 0) (x : Model m) :
    x ∈ X m i ↔ ∃ a b, blockPoint m i a b = x := by
  have he : X m i = blockSubgroup m i hi := by
    apply le_antisymm
    · apply (closure_le _).mpr
      rintro _ ⟨a,rfl⟩
      exact ⟨a,0,by simp [blockPoint]⟩
    · rintro _ ⟨a,b,rfl⟩
      exact mul_mem (mainElement_mem_X m i a) (Y_le_X m i hi (centralElement_mem_Y m i b))
  rw [he]
  rfl

abbrev BlockIndex := Fin 4 ⊕ Fin 4

def rootIndex : BlockIndex → Fin 8 :=
  Sum.elim positiveRootWordLayout.pairIndex positiveRootWordLayout.quartetIndex

abbrev Blocks (m : ℕ) := (i : BlockIndex) → X m (rootIndex i)

def blockProduct (m : ℕ) (a : Blocks m) : Model m :=
  (List.ofFn fun j : Fin 4 => (a (.inl j)).val).prod *
    (List.ofFn fun j : Fin 4 => (a (.inr j)).val).prod

def coordinateBlocks (m : ℕ) (p : PositiveParameters m) : Blocks m
  | .inl j => ⟨mainElement m _ (p.pair j), mainElement_mem_X m _ _⟩
  | .inr j => ⟨blockPoint m _ (p.main j) (p.central j),
      mul_mem (mainElement_mem_X m _ _)
        (Y_le_X m _ (positiveRootWordLayout.quartet_even j) (centralElement_mem_Y m _ _))⟩

theorem blockProduct_coordinateBlocks (m : ℕ) (p : PositiveParameters m) :
    blockProduct m (coordinateBlocks m p) = wordElement m p := rfl

theorem coordinateBlocks_surjective (m : ℕ) : Function.Surjective (coordinateBlocks m) := by
  intro a
  have hp (j : Fin 4) : ∃ t,
      mainElement m (positiveRootWordLayout.pairIndex j) t = (a (.inl j)).val :=
    (mem_X_iff m _ (positiveRootWordLayout.pair_odd j) _).mp (a (.inl j)).property
  have hq (j : Fin 4) : ∃ t u,
      blockPoint m (positiveRootWordLayout.quartetIndex j) t u = (a (.inr j)).val :=
    (mem_X_even m _ (positiveRootWordLayout.quartet_even j) _).mp (a (.inr j)).property
  choose t ht using hp
  choose u v huv using hq
  refine ⟨⟨t,u,v⟩, ?_⟩
  funext i
  cases i with
  | inl j => exact Subtype.ext (ht j)
  | inr j => exact Subtype.ext (huv j)

theorem blockProduct_injective (m : ℕ) : Function.Injective (blockProduct m) := by
  intro a b h
  obtain ⟨p,rfl⟩ := coordinateBlocks_surjective m a
  obtain ⟨q,rfl⟩ := coordinateBlocks_surjective m b
  rw [blockProduct_coordinateBlocks, blockProduct_coordinateBlocks] at h
  exact congrArg (coordinateBlocks m) (wordElement_injective m h)

theorem blockProduct_mem (m : ℕ) (a : Blocks m) :
    blockProduct m a ∈ Parabolics.unipotent m := by
  apply mul_mem
  all_goals
    apply list_prod_mem
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    exact X_le_unipotent m _ (a _).property

theorem blockProduct_surjective (m : ℕ) (x : Parabolics.unipotent m) :
    ∃ a : Blocks m, blockProduct m a = x.val := by
  obtain ⟨p,hp⟩ := exists_positiveWord m x.val x.property
  refine ⟨coordinateBlocks m p, ?_⟩
  rw [blockProduct_coordinateBlocks]
  apply toSplitGroup_injective m
  exact (wordElement_coe m p).trans hp.symm

def positiveEquiv (m : ℕ) : Blocks m ≃ Parabolics.unipotent m :=
  Equiv.ofBijective (fun a => ⟨blockProduct m a, blockProduct_mem m a⟩)
    ⟨fun _ _ h => blockProduct_injective m (congrArg Subtype.val h), fun x => by
      obtain ⟨a,ha⟩ := blockProduct_surjective m x
      exact ⟨a,Subtype.ext ha⟩⟩

theorem positiveEquiv_val (m : ℕ) (a : Blocks m) :
    (positiveEquiv m a).val = blockProduct m a := rfl

end ReeF4.CentralCovers.TwoPrimary
