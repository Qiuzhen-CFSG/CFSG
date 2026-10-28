module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.Collection

/-!
# Normal eights in the last four presentation coordinates

The ascending words on `g17,g18,g19,g20` form an actual subgroup `upperCube`.
Checked collection gives its sixteen-coordinate multiplication law, and
uniqueness of the full normal forms gives its order sixteen. The subgroup is
proved equal to the literal closure of these four generators.

A subgroup of order eight in this subgroup has an element using `g17` or
`g18`. If it is normal in the whole presentation, two explicit commutators
force `g19*g20` and `g20` into it. Removing these last coordinates gives one
of `g18`, `g17`, or `g17*g18`. Eight distinct words in the corresponding
literal `family` entry then prove equality by cardinality.

This proves `normal_eight_in_upperCube`. It does not identify `upperCube`
with the third upper center; that bound is a separate input to `Coverage`.
Only sixteen coordinates and their 256 products are checked, never all
2²¹ normal forms.

Source: the literal relations and candidate words in
`SylowNormalEights/source/pc.json` and `profile-data.json`; see their adjacent
README for conventions and provenance. Context: Kleidman–Wilson (1988),
pp. 484–510; Aschbacher–Smith, `refs/quasithin.pdf`, printed p. 511/PDF p. 528.
-/

@[expose] public section

open scoped commutatorElement
namespace Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.Coverage

def cubeWord (n : Fin 16) : List (Fin 21) := selectWord [17, 18, 19, 20] n.val
def cubePoint (n : Fin 16) : Carrier := wordValue (cubeWord n)
def cubeMask (n : Fin 16) : Fin (2 ^ 21) := ⟨131072 * n.val, by have := n.isLt; omega⟩
def cubeMul (a b : Fin 16) : Fin 16 := ⟨(a.val ^^^ b.val) % 16, Nat.mod_lt _ (by decide)⟩

theorem cubePoint_eq_normalForm (n : Fin 16) : cubePoint n = normalForm (cubeMask n) := by
  have hw : ∀ n : Fin 16, cubeWord n = maskWord (cubeMask n) := by decide +kernel
  exact (congrArg wordValue (hw n)).trans (wordValue_maskWord _)

theorem cubePoint_injective (hcard : Nat.card Carrier = 2 ^ 21) : Function.Injective cubePoint := by
  intro a b h
  simp only [cubePoint_eq_normalForm] at h
  have h := congrArg Fin.val ((normalForm_bijective_of_card hcard).injective h)
  apply Fin.ext
  dsimp [cubeMask] at h
  omega

theorem cubePoint_mul (a b : Fin 16) : cubePoint a * cubePoint b = cubePoint (cubeMul a b) := by
  have hc : ∀ a b : Fin 16,
      collect 32 (cubeWord a ++ cubeWord b) = cubeWord (cubeMul a b) := by decide +kernel
  exact (wordValue_append _ _).symm.trans (wordValue_eq_of_collect 32 _ _ (hc a b))

@[simp] theorem cubePoint_zero : cubePoint 0 = 1 := rfl

theorem cubePoint_inv (a : Fin 16) : (cubePoint a)⁻¹ = cubePoint a := by
  apply inv_eq_iff_mul_eq_one.mpr
  rw [cubePoint_mul]
  have h : ∀ a : Fin 16, cubeMul a a = 0 := by decide +kernel
  rw [h, cubePoint_zero]

def upperCube : Subgroup Carrier where
  carrier := Set.range cubePoint
  one_mem' := ⟨0, cubePoint_zero⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨cubeMul a b, (cubePoint_mul a b).symm⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, (cubePoint_inv a).symm⟩

theorem upperCube_card (hcard : Nat.card Carrier = 2 ^ 21) : Nat.card upperCube = 16 := by
  let f : Fin 16 → upperCube := fun n => ⟨cubePoint n, ⟨n, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact cubePoint_injective hcard (congrArg Subtype.val h)
    · rintro ⟨x,n,h⟩
      exact ⟨n, Subtype.ext h⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fin]


private def coreCoordinate (k : Fin 4) : Fin 16 := ⟨4*k.val, by have := k.isLt; omega⟩
private def topCoordinate (n : Fin 16) : Fin 16 := ⟨4*(n.val/4), by have := n.isLt; omega⟩
private def bottomCoordinate (n : Fin 16) : Fin 16 := ⟨n.val % 4, by omega⟩

/-- The three nonzero directions modulo the last two coordinates. -/
private def direction (i : Fin 3) : Fin 16 := ![2,1,3] i

private def familyCoordinate (i : Fin 3) (n : Fin 8) : Fin 16 :=
  ⟨4 * (n.val / 2) + (if n.val % 2 = 0 then 0 else (direction i).val), by
    have hd : (direction i).val < 4 := (by decide +kernel : ∀ i : Fin 3, (direction i).val < 4) i
    have := n.isLt
    split_ifs <;> omega⟩

private theorem familyCoordinate_injective (i : Fin 3) : Function.Injective (familyCoordinate i) := by
  have h : ∀ (i : Fin 3) (a b : Fin 8), familyCoordinate i a = familyCoordinate i b → a = b := by
    decide +kernel
  exact h i

private theorem cubePoint_familyCoordinate (i : Fin 3) (n : Fin 8) :
    cubePoint (familyCoordinate i n) =
      Theory.GroupTheory.BinaryCollection.product (List.ofFn (familyGenerator i)) n.val := by
  fin_cases i <;> fin_cases n <;>
    simp [cubePoint, cubeWord, familyCoordinate, direction, selectWord, wordValue,
      Theory.GroupTheory.BinaryCollection.product, List.ofFn_succ, familyGenerator, mul_assoc]

private theorem product_mem {G : Type*} [Group G] (H : Subgroup G) (l : List G)
    (hl : ∀ x ∈ l, x ∈ H) (n : ℕ) : Theory.GroupTheory.BinaryCollection.product l n ∈ H := by
  induction l generalizing n with
  | nil => exact H.one_mem
  | cons a l ih =>
    exact H.mul_mem (H.pow_mem (hl a (by simp)) _) (ih (fun x hx => hl x (by simp [hx])) _)

private theorem family_coordinate_mem (i : Fin 3) (n : Fin 8) :
    cubePoint (familyCoordinate i n) ∈ family i := by
  rw [cubePoint_familyCoordinate]
  apply product_mem
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  exact Subgroup.subset_closure (Set.mem_range_self _)

private theorem family_card_ge (hcard : Nat.card Carrier = 2 ^ 21) (i : Fin 3) : 8 ≤ Nat.card (family i) := by
  let f : Fin 8 → family i := fun n => ⟨cubePoint (familyCoordinate i n), family_coordinate_mem i n⟩
  have hf : Function.Injective f := by
    intro a b h
    exact familyCoordinate_injective i (cubePoint_injective hcard (congrArg Subtype.val h))
  simpa using Nat.card_le_card_of_injective f hf

private theorem normal_commutator_mem (A : Subgroup Carrier) (hA : A.Normal)
    {x : Carrier} (hx : x ∈ A) (g : Carrier) : ⁅g, x⁆ ∈ A := by
  exact A.mul_mem (hA.conj_mem x hx g) (A.inv_mem hx)

private theorem force_twelve (n : Fin 16) (hn : n.val % 4 ≠ 0) :
    ⁅(generator (if n.val % 2 = 1 then 1 else 2))⁻¹, cubePoint n⁆ = cubePoint 12 := by
  have hc : ∀ n : Fin 16, n.val % 4 ≠ 0 →
      collect 64 (inverseGeneratorWord (if n.val % 2 = 1 then 1 else 2) ++
        cubeWord n ++ [if n.val % 2 = 1 then 1 else 2] ++ inverseWord (cubeWord n)) = cubeWord 12 := by
    decide +kernel
  have he := wordValue_eq_of_collect 64 _ _ (hc n hn)
  simpa only [wordValue_append, wordValue_inverseGeneratorWord, wordValue_cons,
    wordValue_nil, mul_one, wordValue_inverseWord, commutatorElement_def, inv_inv, cubePoint] using he

private theorem force_eight : ⁅(generator 0)⁻¹, cubePoint 12⁆ = cubePoint 8 := by
  have he := wordValue_eq_of_collect 64
    (inverseGeneratorWord 0 ++ cubeWord 12 ++ [0] ++ inverseWord (cubeWord 12))
    (cubeWord 8) (by decide +kernel)
  simpa only [wordValue_append, wordValue_inverseGeneratorWord, wordValue_cons,
    wordValue_nil, mul_one, wordValue_inverseWord, commutatorElement_def, inv_inv, cubePoint] using he

private theorem normal_contains_last_two (A : Subgroup Carrier) (hA : A.Normal)
    (n : Fin 16) (hn : n.val % 4 ≠ 0) (hx : cubePoint n ∈ A) :
    cubePoint 4 ∈ A ∧ cubePoint 8 ∈ A := by
  have h12 : cubePoint 12 ∈ A := by
    rw [← force_twelve n hn]
    exact normal_commutator_mem A hA hx _
  have h8 : cubePoint 8 ∈ A := by
    rw [← force_eight]
    exact normal_commutator_mem A hA h12 _
  have h4 := A.mul_mem h12 h8
  rw [cubePoint_mul] at h4
  exact ⟨h4, h8⟩

private theorem exists_noncentral_coordinate (A : Subgroup Carrier) (hsize : Nat.card A = 8)
    (hle : A ≤ upperCube) : ∃ n : Fin 16, cubePoint n ∈ A ∧ n.val % 4 ≠ 0 := by
  classical
  by_contra! h
  have hex (x : A) : ∃ k : Fin 4,
      cubePoint ⟨4*k.val, by have := k.isLt; omega⟩ = x.val := by
    obtain ⟨n, hn⟩ := hle x.property
    have hz := h n (hn ▸ x.property)
    refine ⟨⟨n.val / 4, by have := n.isLt; omega⟩, ?_⟩
    convert hn using 2
    apply Fin.ext
    dsimp
    omega
  let f : A → Fin 4 := fun x => Classical.choose (hex x)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hx := Classical.choose_spec (hex x)
    have hy := Classical.choose_spec (hex y)
    change cubePoint ⟨4*(f x).val, _⟩ = x.val at hx
    change cubePoint ⟨4*(f y).val, _⟩ = y.val at hy
    exact hx.symm.trans ((congrArg cubePoint (Fin.ext (congrArg (fun k : Fin 4 => 4*k.val) hxy))).trans hy)
  have hc := Nat.card_le_card_of_injective f hf
  simp [hsize] at hc


private theorem cubePoint_mem_closure (n : Fin 16) :
    cubePoint n ∈ Subgroup.closure {x | x ∈ ([17, 18, 19, 20] : List (Fin 21)).map generator} := by
  unfold cubePoint cubeWord
  rw [wordValue_selectWord]
  apply product_mem
  exact fun x hx => Subgroup.subset_closure hx

/-- The coordinates enumerate precisely the literal four-generator subgroup. -/
theorem upperCube_eq_closure :
    upperCube = Subgroup.closure {x | x ∈ ([17, 18, 19, 20] : List (Fin 21)).map generator} := by
  apply le_antisymm
  · rintro _ ⟨n, rfl⟩
    exact cubePoint_mem_closure n
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨1, by simp [cubePoint, cubeWord, selectWord, wordValue]⟩
    · exact ⟨2, by simp [cubePoint, cubeWord, selectWord, wordValue]⟩
    · exact ⟨4, by simp [cubePoint, cubeWord, selectWord, wordValue]⟩
    · exact ⟨8, by simp [cubePoint, cubeWord, selectWord, wordValue]⟩

private theorem family_le_of_points (A : Subgroup Carrier) (i : Fin 3)
    (hdir : cubePoint (direction i) ∈ A) (h4 : cubePoint 4 ∈ A) (h8 : cubePoint 8 ∈ A) :
    family i ≤ A := by
  have h0 (i : Fin 3) : familyGenerator i 0 = cubePoint (direction i) := by
    fin_cases i
    · exact (mul_one (generator 18)).symm
    · exact (mul_one (generator 17)).symm
    · exact (congrArg (generator 17 * ·) (mul_one (generator 18))).symm
  have h1 (i : Fin 3) : familyGenerator i 1 = cubePoint 4 := by
    fin_cases i <;> exact (mul_one (generator 19)).symm
  have h2 (i : Fin 3) : familyGenerator i 2 = cubePoint 8 := by
    fin_cases i <;> exact (mul_one (generator 20)).symm
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨j,rfl⟩
  fin_cases j
  · exact (h0 i).symm ▸ hdir
  · exact (h1 i).symm ▸ h4
  · exact (h2 i).symm ▸ h8

/-- Every normal eight in the literal order-sixteen subgroup is a marked family
entry. Elementary abelianness is not needed for this calculation. -/
theorem normal_eight_in_upperCube (hcard : Nat.card Carrier = 2 ^ 21)
    (A : Subgroup Carrier) (hnormal : A.Normal) (hsize : Nat.card A = 8)
    (hle : A ≤ upperCube) : ∃ i, A = family i := by
  obtain ⟨n,hx,hn⟩ := exists_noncentral_coordinate A hsize hle
  obtain ⟨h4,h8⟩ := normal_contains_last_two A hnormal n hn hx
  have hcore (k : Fin 4) : cubePoint (coreCoordinate k) ∈ A := by
    fin_cases k
    · change cubePoint 0 ∈ A
      rw [cubePoint_zero]
      exact A.one_mem
    · exact h4
    · exact h8
    · have h := A.mul_mem h4 h8
      rw [cubePoint_mul] at h
      exact h
  let q : Fin 4 := ⟨n.val / 4, by have := n.isLt; omega⟩
  have hr := A.mul_mem hx (hcore q)
  rw [cubePoint_mul] at hr
  have he : ∀ n : Fin 16,
      cubeMul n (topCoordinate n) = bottomCoordinate n := by decide +kernel
  change cubePoint (cubeMul n (topCoordinate n)) ∈ A at hr
  rw [he] at hr
  have hd : ∀ n : Fin 16, n.val % 4 ≠ 0 →
      ∃ i : Fin 3, direction i = bottomCoordinate n := by decide +kernel
  obtain ⟨i,hi⟩ := hd n hn
  have hf : family i ≤ A := family_le_of_points A i (hi ▸ hr) h4 h8
  refine ⟨i, (Subgroup.eq_of_le_of_card_ge hf ?_).symm⟩
  rw [hsize]
  exact family_card_ge hcard i

end Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.Coverage
