module
public import Theory.Mathieu.M12.Properties.SylowAutomorphismGroup.Certificate
public import Theory.Mathieu.M12.ExceptionalParabolics.EightExtensions.Coordinates
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry.WordCompleteness
/-!
# A 128-signature bound for the marked M₁₂ parabolic pair

There are 32 elements of order three in the second parabolic. For each such
image y of the moving cubic, the order-four condition on a and the order-eight
condition on yay permit four overlap images a. The order conditions on b, ab,
and yb then determine b. The original overlap and second-parabolic word
certificates identify every element; the finite calculation below uses checked
compact integer point tables for their literal permutations. All table entries are untrusted
data, checked in the kernel before application to actual automorphisms.

Source: Goldschmidt, Automorphisms of trivalent graphs, §3.8; the marked
M₁₂ permutations of Aschbacher--Smith 14.2.21 and F.1.12.
-/
@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.Certificate
open SylowAutomorphismGroup SylowEnumeration
set_option maxRecDepth 1000000
set_option Elab.async false

def cubicIndices : Array (Fin 192) := #[20,22,29,31,48,52,59,63,64,68,75,79,84,86,93,95,101,103,108,110,133,135,140,142,161,165,170,174,177,181,186,190]
def cubicIndex (i : Fin 32) : Fin 192 := cubicIndices[i.val]!
def cubic (i : Fin 32) : M12 := wordElement (cubicIndex i)
def cubicDecoder : Array (Fin 32) := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,2,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,5,0,0,0,0,0,0,6,0,0,0,7,8,0,0,0,9,0,0,0,0,0,0,10,0,0,0,11,0,0,0,0,12,0,13,0,0,0,0,0,0,14,0,15,0,0,0,0,0,16,0,17,0,0,0,0,18,0,19,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20,0,21,0,0,0,0,22,0,23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,0,0,0,25,0,0,0,0,26,0,0,0,27,0,0,28,0,0,0,29,0,0,0,0,30,0,0,0,31,0]
def decodeCubic (i : Fin 192) : Fin 32 := cubicDecoder[i.val]!
def imageTable : Array (Array (Fin 64 × Fin 64)) := #[
  #[(1,2),(11,2),(20,56),(23,56)],
  #[(1,12),(11,12),(20,58),(23,58)],
  #[(2,11),(12,11),(56,23),(58,23)],
  #[(2,1),(12,1),(56,20),(58,20)],
  #[(1,12),(11,12),(20,58),(23,58)],
  #[(1,2),(11,2),(20,56),(23,56)],
  #[(2,1),(12,1),(56,23),(58,23)],
  #[(2,11),(12,11),(56,20),(58,20)],
  #[(1,2),(11,2),(20,56),(23,56)],
  #[(1,12),(11,12),(20,58),(23,58)],
  #[(2,11),(12,11),(56,20),(58,20)],
  #[(2,1),(12,1),(56,23),(58,23)],
  #[(1,2),(11,2),(20,56),(23,56)],
  #[(1,12),(11,12),(20,58),(23,58)],
  #[(2,11),(12,11),(56,23),(58,23)],
  #[(2,1),(12,1),(56,20),(58,20)],
  #[(1,2),(11,2),(20,58),(23,58)],
  #[(1,12),(11,12),(20,56),(23,56)],
  #[(2,1),(12,1),(56,23),(58,23)],
  #[(2,11),(12,11),(56,20),(58,20)],
  #[(1,2),(11,2),(20,58),(23,58)],
  #[(1,12),(11,12),(20,56),(23,56)],
  #[(2,1),(12,1),(56,23),(58,23)],
  #[(2,11),(12,11),(56,20),(58,20)],
  #[(2,1),(12,1),(56,20),(58,20)],
  #[(2,11),(12,11),(56,23),(58,23)],
  #[(1,12),(11,12),(20,56),(23,56)],
  #[(1,2),(11,2),(20,58),(23,58)],
  #[(2,11),(12,11),(56,23),(58,23)],
  #[(2,1),(12,1),(56,20),(58,20)],
  #[(1,2),(11,2),(20,58),(23,58)],
  #[(1,12),(11,12),(20,56),(23,56)]]
def images (y : Fin 32) (k : Fin 4) : Fin 64 × Fin 64 := (imageTable[y.val]!)[k.val]!
def choice (y : Fin 32) (a : Fin 64) : Fin 4 :=
  if (images y 0).1 = a then 0 else if (images y 1).1 = a then 1
  else if (images y 2).1 = a then 2 else 3


def cubicCodeTable : Array ℕ := #[133502788044081,166483857515841,35611800597921,2630728783281,148054923875331,115078129079331,23788491662451,89750630728851,115138025837316,148131929199396,89827640247156,23848384226196,166625038836021,133635410886981,2763353723301,35752979820981,35575655135286,2586026940486,166383085168806,133402013599926,2316502013496,35297571731016,133123932292776,166113558144696,89366343355146,23404200094506,147618841041786,114624933485466,23327194769931,89306446596651,114565040921211,147541831522971]
def sylowCodeTable : Array ℕ := #[205163983024656,147515135580471,147998050161216,114849903612576,188662747972176,188179836844311,204514087156071,205014115238496,73839184361241,74185193529936,57816457650816,114534064134471,115016980320816,147830972961456,147352336013751,23753237364786,23133418973511,89215123089831,89241018599241,89587033072176,23723062616736,147484960954281,114392884909881,89698037301936,23620612424256,204681063385431,188038523341191,188504326025856,57337949431641,57683966865936,74292021342816,74313543426066,73693721704791,57333544302951,188658342965346,205018520367186,73809103923591,57209607923991,188158314760041,204535609116441,73689316697961,188534406463506,188051486947161,204668099901321,114362709793191,89728212295746,89108395755831,23240146061751,23274600294201,114503889016761,147382510638921,114982526455986,147865427316786,23590437675186,114875798999106,147972154282146,89073941768121,89556858077346,23107523217321,57829421133906,205133902463106,57179527362441,74172229922946,57662444904546]
def orderNumberTable : Array ℕ := #[1,4,4,8,2,2,4,2,4,2,4,4,4,8,8,8,8,2,8,8,4,8,2,4,8,2,4,2,4,2,4,2,4,2,2,2,2,4,4,2,2,2,2,4,8,8,8,2,8,8,2,8,2,2,2,8,4,2,4,2,2,2,4,4]
def orderNumber (a : Fin 64) : ℕ := orderNumberTable[a.val]!
def point (code x : ℕ) : ℕ := (code >>> (4 * x)) % 16
def cubicPoint (y : Fin 32) (x : ℕ) : ℕ := point (cubicCodeTable[y.val]!) x
def sylowPoint (a : Fin 64) (x : ℕ) : ℕ := point (sylowCodeTable[a.val]!) x
def mixPoint (y : Fin 32) (b : Fin 64) (x : ℕ) : ℕ := cubicPoint y (sylowPoint b x)
def pointPower (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | n + 1, x => f (pointPower f n x)
def pointOrderTest (f : ℕ → ℕ) (n : ℕ) : Prop :=
  (∀ x : Fin 12, pointPower f n x.val = x.val) ∧
  ¬ (∀ x : Fin 12, pointPower f (n / 2) x.val = x.val)
instance (f : ℕ → ℕ) (n : ℕ) : Decidable (pointOrderTest f n) :=
  inferInstanceAs (Decidable (_ ∧ _))
def sandwichPoint (y : Fin 32) (a : Fin 64) (x : ℕ) : ℕ :=
  cubicPoint y (sylowPoint a (cubicPoint y x))

set_option maxHeartbeats 2000000 in
private theorem first_check : ∀ y : Fin 32, ∀ a : Fin 64, orderNumber a = 4 →
    pointOrderTest (sandwichPoint y a) 8 → (images y (choice y a)).1 = a := by
  intro y
  fin_cases y <;> decide +kernel

set_option maxHeartbeats 2000000 in
private theorem second_check : ∀ y : Fin 32, ∀ k : Fin 4, ∀ b : Fin 64,
    orderNumber b = 4 → orderNumber (multiply (images y k).1 b) = 2 →
    pointOrderTest (mixPoint y b) 4 → (images y k).2 = b := by
  intro y
  fin_cases y <;> decide +kernel

private theorem cubic_point : ∀ (y : Fin 32) (x : Fin 12),
    cubicPoint y x.val = ((cubic y).val x).val := by
  decide +kernel

private theorem sylow_point (a : Fin 64) (x : Fin 12) :
    sylowPoint a x.val = ((element a : M12).val x).val := by
  have h := EightExtensions.Coordinates.element_point
    (EightExtensions.Coordinates.overlapIndex a) x
  rw [EightExtensions.Coordinates.element_overlap] at h
  have check : ∀ (a : Fin 64) (x : Fin 12), sylowPoint a x.val =
      (EightExtensions.Coordinates.point
        (EightExtensions.Coordinates.overlapIndex a) x).val := by
    decide +kernel
  exact (check a x).trans (congrArg Fin.val h).symm

private theorem pointPower_perm (f : ℕ → ℕ) (g : M12)
    (hf : ∀ x : Fin 12, f x.val = (g.val x).val) (n : ℕ) (x : Fin 12) :
    pointPower f n x.val = ((g ^ n).val x).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pointPower, ih, hf, pow_succ']
    rfl

private theorem pointOrderTest_iff (f : ℕ → ℕ) (g : M12)
    (hf : ∀ x : Fin 12, f x.val = (g.val x).val) (n : ℕ) :
    pointOrderTest f n ↔ g ^ n = 1 ∧ g ^ (n / 2) ≠ 1 := by
  have he (k : ℕ) : (∀ x : Fin 12, pointPower f k x.val = x.val) ↔ g ^ k = 1 := by
    constructor
    · intro h
      apply Subtype.ext
      apply Equiv.ext
      intro x
      apply Fin.ext
      exact (pointPower_perm f g hf k x).symm.trans (h x)
    · intro h x
      rw [pointPower_perm f g hf, h]
      rfl
  exact and_congr (he n) (not_congr (he (n / 2)))

private theorem powerTest_iff (a : Fin 64) (n : ℕ) :
    powerTest a n ↔ (element a : M12) ^ n = 1 ∧
      (element a : M12) ^ (n / 2) ≠ 1 := by
  have he (k : ℕ) : power a k = 0 ↔ (element a : M12) ^ k = 1 := by
    rw [← element_injective.eq_iff, element_power, element_zero]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  exact and_congr (he n) (not_congr (he (n / 2)))

private theorem orderNumber_four : ∀ a : Fin 64, orderNumber a = 4 ↔ powerTest a 4 := by
  decide +kernel

private theorem orderNumber_two : ∀ a : Fin 64, orderNumber a = 2 ↔ powerTest a 2 := by
  decide +kernel

/-- Every cubic image in the literal second parabolic occurs in the checked list. -/
theorem cubic_surjective (g : secondParabolic) (hg : g ^ 3 = 1) (hne : g ≠ 1) :
    ∃ y : Fin 32, cubic y = (g : M12) := by
  have h : g.val.val ∈ wordCarrier :=
    (mem_wordCarrier_iff _).mpr
      ⟨(mem_M12_iff_preservesBlocks _).mp g.val.property,
        (mem_secondParabolic_iff _).mp g.property⟩
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  have he : wordElement i = (g : M12) := Subtype.ext hi
  have check : ∀ i : Fin 192, wordElement i ^ 3 = 1 → wordElement i ≠ 1 →
      cubic (decodeCubic i) = wordElement i := by
    decide +kernel
  refine ⟨decodeCubic i, (check i ?_ ?_).trans he⟩
  · rw [he]
    exact congrArg Subtype.val hg
  · rw [he]
    exact fun h => hne (Subtype.ext h)

/-- The necessary orders select one of four generator-image pairs for each cubic. -/
theorem covers (y : Fin 32) (a b : Fin 64)
    (ha : (element a : M12) ^ 4 = 1 ∧ (element a : M12) ^ 2 ≠ 1)
    (hb : (element b : M12) ^ 4 = 1 ∧ (element b : M12) ^ 2 ≠ 1)
    (hab : ((element a : M12) * (element b : M12)) ^ 2 = 1 ∧
      (element a : M12) * (element b : M12) ≠ 1)
    (hay : (cubic y * (element a : M12) * cubic y) ^ 8 = 1 ∧
      (cubic y * (element a : M12) * cubic y) ^ 4 ≠ 1)
    (hby : (cubic y * (element b : M12)) ^ 4 = 1 ∧
      (cubic y * (element b : M12)) ^ 2 ≠ 1) :
    ∃ k : Fin 4, images y k = (a,b) := by
  have hs (x : Fin 12) : sandwichPoint y a x.val =
      ((cubic y * (element a : M12) * cubic y).val x).val := by
    dsimp only [sandwichPoint]
    rw [cubic_point, sylow_point, cubic_point]
    rfl
  have hm (x : Fin 12) : mixPoint y b x.val =
      ((cubic y * (element b : M12)).val x).val := by
    dsimp only [mixPoint]
    rw [sylow_point, cubic_point]
    rfl
  have hA := first_check y a ((orderNumber_four a).mpr ((powerTest_iff a 4).mpr ha))
    ((pointOrderTest_iff _ _ hs 8).mpr hay)
  have hB : (images y (choice y a)).2 = b := by
    apply second_check y (choice y a) b
      ((orderNumber_four b).mpr ((powerTest_iff b 4).mpr hb))
    · rw [hA, orderNumber_two, powerTest_iff, element_multiply]
      change ((element a : M12) * (element b : M12)) ^ 2 = 1 ∧
        ((element a : M12) * (element b : M12)) ^ (2 / 2) ≠ 1
      simpa only [Nat.reduceDiv, pow_one] using hab
    · exact (pointOrderTest_iff _ _ hm 4).mpr hby
  exact ⟨choice y a, Prod.ext hA hB⟩

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms.Certificate

