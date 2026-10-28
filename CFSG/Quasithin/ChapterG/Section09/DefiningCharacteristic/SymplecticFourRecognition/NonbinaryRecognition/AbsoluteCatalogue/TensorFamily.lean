module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.TensorModels
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.AbsoluteCatalogue.TensorFamily.FullOrbit
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.AbsoluteCatalogue.TensorFamily.MarkedWeights

/-!
# Simplicity and distinctness of the symplectic tensor family

Every subset of the `2*n` natural and exceptional graph factors gives an
irreducible representation of the actual derived subgroup of Sp₄(F).
Genuine linear equivalence determines the subset. The argument works over
any coefficient field admitting the specified embedding of F.

Evaluate omitted coordinates at the lowest coordinate to obtain a surjective
unipotent intertwiner from the full tensor. Its regular orbit basis makes
the lowest vector of every subset cyclic. Extending by highest delta vectors
gives an injective unipotent intertwiner in the opposite direction, so the
full tensor's unique fixed line gives the unique highest line for every
subset, including the empty subset. A nonzero invariant subspace contains
a nonzero unipotent-fixed vector; the block exchange then gives the lowest
vector and its spanning orbit. Finally the marked coroot characters and
negative-root zero-label tests distinguish every pair of subsets.

Sources: GLS3, 2.8.2, 2.8.6(a), 2.8.10(d),
`refs/KGroup/GLS3/chapter2.tex`; Aschbacher--Smith, G.9.3,
printed pp.356–357 of `refs/quasithin.pdf`.
-/

noncomputable section
open scoped BigOperators
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary
namespace TensorFamily
open FullOrbit MarkedWeights
variable {n : ℕ} (S : Finset (Fin (2*n)))

private def includeIndex (j : S) : FullIndex n := ⟨j.val, Finset.mem_univ _⟩
private lemma includeIndex_injective : Function.Injective (includeIndex S) := by
  intro i j h
  exact Subtype.ext (congrArg (fun k : FullIndex n => k.val) h)
private lemma mem_range_includeIndex (j : FullIndex n) :
    j ∈ Set.range (includeIndex S) ↔ j.val ∈ S := by
  constructor
  · rintro ⟨i, rfl⟩; exact i.property
  · intro h; exact ⟨⟨j.val,h⟩, rfl⟩

private def restrictTuple (x : FullIndex n → Coordinate) : S → Coordinate :=
  fun j => x (includeIndex S j)
private def fillTuple (b : Coordinate) (x : S → Coordinate) : FullIndex n → Coordinate :=
  fun j => if h : j.val ∈ S then x ⟨j.val,h⟩ else b
private def Supported (b : Coordinate) (x : FullIndex n → Coordinate) : Prop :=
  ∀ j, j.val ∉ S → x j = b
private noncomputable instance (b : Coordinate) (x : FullIndex n → Coordinate) :
    Decidable (Supported S b x) := Classical.propDecidable _
private lemma restrict_fill (b : Coordinate) (x : S → Coordinate) :
    restrictTuple S (fillTuple S b x) = x := by
  funext j
  simp [restrictTuple, fillTuple, includeIndex, j.property]
private lemma fill_injective (b : Coordinate) : Function.Injective (fillTuple S b) :=
  Function.LeftInverse.injective (restrict_fill S b)
private lemma supported_fill (b : Coordinate) (x : S → Coordinate) :
    Supported S b (fillTuple S b x) := by
  intro j hj
  simp [fillTuple, hj]
private lemma fill_restrict (b : Coordinate) {x : FullIndex n → Coordinate}
    (hx : Supported S b x) : fillTuple S b (restrictTuple S x) = x := by
  funext j
  by_cases hj : j.val ∈ S
  · simp [fillTuple, hj, restrictTuple, includeIndex]
  · simp [fillTuple, hj, hx j hj]
private lemma mem_range_fill (b : Coordinate) (x : FullIndex n → Coordinate) :
    x ∈ Set.range (fillTuple S b) ↔ Supported S b x := by
  constructor
  · rintro ⟨y,rfl⟩; exact supported_fill S b y
  · intro hx; exact ⟨restrictTuple S x, fill_restrict S b hx⟩

variable {E : Type*} [Field E]

private lemma product_column (b : Coordinate)
    (m : FullIndex n → Coordinate → Coordinate → E)
    (hm : ∀ j i, m j i b = if i = b then 1 else 0)
    (x : FullIndex n → Coordinate) (y : S → Coordinate) :
    (∏ j, m j (x j) (fillTuple S b y j)) =
      if Supported S b x then ∏ j : S, m (includeIndex S j) (restrictTuple S x j) (y j)
      else 0 := by
  classical
  by_cases hx : Supported S b x
  · rw [if_pos hx]
    symm
    apply Fintype.prod_of_injective (includeIndex S) (includeIndex_injective S)
    · intro j hj
      have hj' := mt (mem_range_includeIndex S j).mpr hj
      simp [fillTuple, hj', hm, hx j hj']
    · intro j
      simp [fillTuple, includeIndex, j.property, restrictTuple]
  · rw [if_neg hx]
    obtain ⟨j, hj, hxb⟩ : ∃ j, j.val ∉ S ∧ x j ≠ b := by
      obtain ⟨j, hj⟩ := not_forall.mp hx
      exact ⟨j, (Classical.not_imp.mp hj).1, (Classical.not_imp.mp hj).2⟩
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [fillTuple, hj, hm, hxb])

/-- Evaluate omitted coordinates at a fixed coordinate. -/
def projection (b : Coordinate) : ((FullIndex n → Coordinate) → E) →ₗ[E] ((S → Coordinate) → E) where
  toFun v x := v (fillTuple S b x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extend a coefficient array by a delta vector in each omitted position. -/
def injection (b : Coordinate) : ((S → Coordinate) → E) →ₗ[E] ((FullIndex n → Coordinate) → E) := by
  classical
  exact {
    toFun := fun v x => if Supported S b x then v (restrictTuple S x) else 0
    map_add' := by intros; funext x; split_ifs <;> simp_all
    map_smul' := by intros; funext x; split_ifs <;> simp_all }

lemma projection_injection (b : Coordinate) (v : (S → Coordinate) → E) :
    projection S b (injection S b v) = v := by
  classical
  ext x
  simp [projection, injection, supported_fill, restrict_fill]

lemma injection_injective (b : Coordinate) : Function.Injective (injection (E := E) S b) :=
  Function.LeftInverse.injective (projection_injection S b)

lemma projection_surjective (b : Coordinate) : Function.Surjective (projection (E := E) S b) :=
  Function.LeftInverse.surjective (projection_injection S b)

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] (e : F →+* E)

lemma injection_intertwines (b : Coordinate) (g : Derived F)
    (hg : ∀ j i, ((graphDerived F ^ j) g).val.val i b = if i = b then 1 else 0)
    (v : (S → Coordinate) → E) :
    tensorModel e (FullIndex n) g (injection S b v) = injection S b (tensorModel e S g v) := by
  classical
  ext x
  change (∑ y, tensorMatrix e (FullIndex n) g x y * injection S b v y) = _
  rw [← Fintype.sum_of_injective (fillTuple S b) (fill_injective S b)
    (fun y => tensorMatrix e (FullIndex n) g x (fillTuple S b y) * v y)
    (fun y => tensorMatrix e (FullIndex n) g x y * injection S b v y)]
  · have hm := product_column S b
      (fun j i k => e (((graphDerived F ^ (j.val : ℕ)) g).val.val i k))
      (by intro j i; rw [hg]; split_ifs <;> simp) x
    simp only [tensorMatrix] at *
    simp_rw [hm]
    change _ = if Supported S b x then
      (∑ y, (∏ j : S, e (((graphDerived F ^ (j.val : ℕ)) g).val.val (restrictTuple S x j) (y j))) * v y)
      else 0
    split_ifs <;> simp [includeIndex]
  · intro y hy
    have hy' := mt (mem_range_fill S b y).mpr hy
    simp [injection, hy']
  · intro y
    simp [injection, supported_fill, restrict_fill]

lemma projection_intertwines (b : Coordinate) (g : Derived F)
    (hg : ∀ j i, ((graphDerived F ^ j) g).val.val b i = if i = b then 1 else 0)
    (v : (FullIndex n → Coordinate) → E) :
    projection S b (tensorModel e (FullIndex n) g v) = tensorModel e S g (projection S b v) := by
  classical
  ext x
  change (∑ y, tensorMatrix e (FullIndex n) g (fillTuple S b x) y * v y) = _
  have hm := product_column S b
    (fun j i k => e (((graphDerived F ^ (j.val : ℕ)) g).val.val k i))
    (by intro j i; rw [hg]; split_ifs <;> simp)
  rw [← Fintype.sum_of_injective (fillTuple S b) (fill_injective S b)
    (fun y => tensorMatrix e S g x y * v (fillTuple S b y))
    (fun y => tensorMatrix e (FullIndex n) g (fillTuple S b x) y * v y)]
  · rfl
  · intro y hy
    have hy' := mt (mem_range_fill S b y).mpr hy
    have hh := hm y x
    simp only [tensorMatrix]
    rw [hh, if_neg hy', zero_mul]
  · intro y
    have hh := hm (fillTuple S b y) x
    simp only [supported_fill, if_true, restrict_fill] at hh
    simp only [tensorMatrix]
    rw [hh]
    rfl

local notation "a" => (Sum.inl (0 : Fin 2) : Coordinate)
local notation "c" => (Sum.inr (0 : Fin 2) : Coordinate)

lemma injection_single (b : Coordinate) (x : S → Coordinate) :
    injection (E := E) S b (Pi.single x 1) = Pi.single (fillTuple S b x) 1 := by
  classical
  ext y
  by_cases hy : Supported S b y
  · have he : restrictTuple S y = x ↔ y = fillTuple S b x := by
      constructor
      · intro h; rw [← h, fill_restrict S b hy]
      · intro h; rw [h, restrict_fill]
    simp [injection, hy, Pi.single_apply, he]
  · have he : y ≠ fillTuple S b x := by
      intro h; apply hy; rw [h]; exact supported_fill S b x
    simp [injection, hy, he]

lemma projection_single (b : Coordinate) (x : S → Coordinate) :
    projection (E := E) S b (Pi.single (fillTuple S b x) 1) = Pi.single x 1 := by
  classical
  ext y
  simp [projection, Pi.single_apply, (fill_injective S b).eq_iff]

private lemma fill_const (b : Coordinate) : fillTuple S b (fun _ => b) = (fun _ => b) := by
  funext j
  simp [fillTuple]

lemma injection_highest : injection (E := E) S a (highestVector S) = highest n := by
  simpa only [highestVector, highest, fill_const] using injection_single (E := E) S a (fun _ => a)

/-- The lowest coordinate tensor for any subset, including the empty subset. -/
def lowestVector : (S → Coordinate) → E := Pi.single (fun _ => c) 1

lemma projection_lowest : projection (E := E) S c (lowest n) = lowestVector S := by
  simpa only [lowestVector, lowest, fill_const] using projection_single (E := E) S c (fun _ => c)

lemma sylowMap_mem_U (hq : 2 < Nat.card F) (u : Theory.SpecificGroups.SymplecticFour.unipotent (F := F)) :
    sylowMap hq u ∈ U := by
  change (sylowMap hq u).val ∈ Theory.SpecificGroups.SymplecticFour.unipotent
  rw [sylowMap_val]
  exact u.property

lemma highest_fixed_line (hq : 2 < Nat.card F) (hF : Nat.card F = 2^n)
    (v : (S → Coordinate) → E) :
    (∀ g ∈ U, tensorModel e S g v = v) ↔ ∃ z : E, v = z • highestVector S := by
  constructor
  · intro hv
    obtain ⟨z, hz⟩ := (FullOrbit.fixed_line e hq hF (injection S a v)).mp (by
      intro u
      rw [injection_intertwines S e a _
        (fun j i => graph_unipotent_column _ (sylowMap_mem_U hq u) j i),
        hv _ (sylowMap_mem_U hq u)])
    refine ⟨z, injection_injective S a ?_⟩
    rw [map_smul, injection_highest]
    exact hz
  · rintro ⟨z,rfl⟩ g hg
    rw [map_smul, highestVector_fixed e S g hg]

open Theory.SpecificGroups.SymplecticFour Representation
local instance : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
noncomputable local instance : Fintype (unipotent (F := F)) := Fintype.ofFinite _

/-- Every subset's lowest tensor is cyclic under the marked unipotent subgroup. -/
lemma lowest_cyclic (hq : 2 < Nat.card F) (hF : Nat.card F = 2^n)
    (v : (S → Coordinate) → E) :
    ∃ f : unipotent (F := F) → E,
      v = ∑ u, f u • tensorModel e S (sylowMap hq u) (lowestVector S) := by
  obtain ⟨w, rfl⟩ := projection_surjective (E := E) S c v
  obtain ⟨f, rfl⟩ := (orbitEquiv e hq hF).surjective w
  refine ⟨f, ?_⟩
  rw [orbitEquiv_apply, map_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [map_smul, projection_intertwines S e c _
    (fun j i => graph_unipotent_row _ (sylowMap_mem_U hq u) j i), projection_lowest]

lemma longElement_highest_subset (hq : 2 < Nat.card F) :
    tensorModel e S (longElement hq) (highestVector S) = lowestVector S := by
  classical
  ext x
  rw [tensorModel_highest_apply]
  simp_rw [graph_power_longElement, longElement_val]
  have hh (i : Coordinate) : (blockExchange (F := F)).val i a =
      if i = c then 1 else 0 := by
    rcases i with i | i <;> fin_cases i <;> rfl
  simp_rw [hh]
  simp only [apply_ite e, map_one, map_zero]
  rw [Fintype.prod_ite_zero]
  simp [lowestVector, Pi.single_apply, funext_iff]

lemma irreducible (hq : 2 < Nat.card F) (hF : Nat.card F = 2^n) :
    IsIrreducible (tensorModel e S) := by
  classical
  let ρ := tensorModel e S
  have : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, fun h =>
    bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro W hW
  have : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr
    (fun hh => hW (Subrepresentation.toSubmodule_injective hh))
  have hc : ringChar E ≠ 0 := by rw [coefficient_ringChar e]; decide
  have hp : IsPGroup (ringChar E) (unipotent (F := F)) := by
    rw [coefficient_ringChar e]
    exact isPGroup_unipotent hF
  obtain ⟨v, hv, hfix⟩ := pGroup_fix_nonzero_vector hc hp
    (W.toRepresentation.comp (sylowMap hq))
  have hfix' : ∀ g ∈ U, tensorModel e S g v.val = v.val := by
    intro g hg
    rw [← unipotentLift_range hq] at hg
    obtain ⟨u, rfl⟩ := hg
    exact congrArg Subtype.val (hfix u)
  obtain ⟨z, hz⟩ := (highest_fixed_line S e hq hF v.val).mp hfix'
  have hz0 : z ≠ 0 := by
    intro h
    apply hv
    apply Subtype.ext
    simpa [h] using hz
  have hhigh : highestVector S ∈ W := by
    have hh := W.toSubmodule.smul_mem z⁻¹ v.property
    rw [hz, inv_smul_smul₀ hz0] at hh
    exact hh
  have hlow : lowestVector S ∈ W := by
    have hh := W.apply_mem_toSubmodule (longElement hq) hhigh
    rwa [longElement_highest_subset S e hq] at hh
  apply le_antisymm le_top
  intro w _
  obtain ⟨f, rfl⟩ := lowest_cyclic S e hq hF w
  apply W.toSubmodule.sum_mem
  intro u _
  exact W.toSubmodule.smul_mem _ (W.apply_mem_toSubmodule (sylowMap hq u) hlow)

end TensorFamily

public section

variable {F E : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Field E]
  {n : ℕ}

omit [Field F] [Finite F] [Algebra (ZMod 2) F] in
private lemma card_gt_two_of_exponent (hF : Nat.card F = 2^n) (hn : 2 ≤ n) :
    2 < Nat.card F := by
  rw [hF]
  calc
    2 < 2^2 := by decide
    _ ≤ 2^n := Nat.pow_le_pow_right (by decide) hn

/-- Every concrete tensor has precisely its marked highest line as the fixed space
of the standard unipotent subgroup. This includes the empty tensor. -/
theorem tensorModel_highest_fixed_line (e : F →+* E)
    (hF : Nat.card F = 2^n) (hn : 2 ≤ n)
    (S : Finset (Fin (2*n))) (v : (S → Coordinate) → E) :
    (∀ g ∈ MarkedWeights.U, tensorModel e S g v = v) ↔
      ∃ z : E, v = z • MarkedWeights.highestVector S :=
  TensorFamily.highest_fixed_line S e (card_gt_two_of_exponent hF hn) hF v

/-- All subsets of the natural and exceptional graph factors are irreducible
on the actual derived symplectic group, over any field admitting the embedding. -/
theorem tensorModel_irreducible (e : F →+* E)
    (hF : Nat.card F = 2^n) (hn : 2 ≤ n) (S : Finset (Fin (2*n))) :
    Representation.IsIrreducible (tensorModel e S) :=
  TensorFamily.irreducible S e (card_gt_two_of_exponent hF hn) hF

/-- Genuine linear equivalence distinguishes all tensor subsets. The negative-root
markers separate zero labels from q-1, which have the same finite-torus character. -/
theorem tensorModel_equiv_imp_eq (e : F →+* E)
    (hF : Nat.card F = 2^n) (hn : 2 ≤ n) (S T : Finset (Fin (2*n)))
    (h : Nonempty ((tensorModel e S).Equiv (tensorModel e T))) : S = T :=
  MarkedWeights.tensorModel_distinguish_of_fixed_lines e hn hF
    (tensorModel_highest_fixed_line e hF hn) S T h

end

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary
