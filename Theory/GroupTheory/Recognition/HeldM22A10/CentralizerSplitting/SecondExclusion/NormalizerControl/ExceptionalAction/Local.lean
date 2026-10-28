module
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Structure
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Context
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.NormalizerControl.Geometry
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.NormalizerControl.ExceptionalAction.CharacteristicThree

/-!
# Local normality, orbits, and square fusion

Conjugation by the two actual generators preserves F and V, proving normality
in the full local group. Checked conjugators give the six-point orbit in V.
A second finite calculation detects the outer involution class from a commuting
square different from 1 and z. All certificates use the existing carrier.

These are local ingredients for the independent normalizer argument toward
Huppert--Blackburn III, XII.1.18(b), printed p.314.
-/
namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl.ExceptionalAction
open NonsplitModels Model Subgroup
set_option maxRecDepth 100000

private def fusionRow (i : Fin 384) : Fin 384 :=
  ⟨(448810070516358278670146620796219658809024051307969764555954757983581433127915268408010974446542631169013918052150263342382688524287751923044216117226231951465406294702317697283925007409358799696065812278631023930762837494844181302381753509443158315155481978651997707275688400859657274954518106076506694235548679804721634824631083147262580642729282177537419203853369055644393609794795673077547044303637987679134326235887964801861676666780193527033501724884864260180001283009888579768567457601176974043801902051436625357677451833201395474791568347137424719653601190402741162011415255689775011083205822331094473410356639976512269666693604002236831126113472490439742497354808012089743739543571257489651394865528832 / 384 ^ i.val) % 384, Nat.mod_lt _ (by decide)⟩

private def orbitRow (i : Fin 8) : Second :=
  element (![0, 353, 305, 379, 355, 383, 381, 0] i)

private def localGenerator (i : Fin 2) : Second := element (![97, 149] i)

private theorem normalizer_of_two_sided (K : Subgroup Second) (a : Second)
    (hf : ∀ x : Second, x ∈ K → a * x * a⁻¹ ∈ K)
    (hb : ∀ x : Second, x ∈ K → a⁻¹ * x * a ∈ K) :
    a ∈ normalizer (K : Set Second) := by
  intro x
  refine ⟨hf x, fun hx => ?_⟩
  have h := hb _ hx
  change x ∈ K
  simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using h

private theorem conj_of_generator_normalizers (K : Subgroup Second)
    (hgen : ∀ i : Fin 2, localGenerator i ∈ normalizer (K : Set Second))
    (a x : Second) (hx : x ∈ K) : a * x * a⁻¹ ∈ K := by
  have hle : secondSubgroup ≤ (normalizer (K : Set Second)).map secondSubgroup.subtype := by
    change Subgroup.closure {secondA, secondB} ≤ _
    rw [Subgroup.closure_le]
    intro p hp
    rcases hp with rfl | rfl
    · exact ⟨localGenerator 0, hgen 0, by decide +kernel⟩
    · exact ⟨localGenerator 1, hgen 1, by decide +kernel⟩
  have ha : a ∈ normalizer (K : Set Second) := by
    obtain ⟨b, hb, he⟩ := hle a.property
    have hba : b = a := Subtype.ext he
    exact hba ▸ hb
  exact (ha x).mp hx

private theorem four_generator_rows : ∀ i : Fin 2, ∀ j : Fin 16,
    localGenerator i * fourRows j * (localGenerator i)⁻¹ ∈ fourGroup ∧
    (localGenerator i)⁻¹ * fourRows j * localGenerator i ∈ fourGroup := by decide +kernel

private theorem three_generator_rows : ∀ i : Fin 2, ∀ j : Fin 8,
    localGenerator i * threeRows j * (localGenerator i)⁻¹ ∈ threeGroup ∧
    (localGenerator i)⁻¹ * threeRows j * localGenerator i ∈ threeGroup := by decide +kernel

/-- F is normal in the full local group. -/
public theorem four_conj (a x : Second) (hx : x ∈ fourGroup) :
    a * x * a⁻¹ ∈ fourGroup := by
  apply conj_of_generator_normalizers fourGroup ?_ a x hx
  intro i
  apply normalizer_of_two_sided
  · rintro _ ⟨j, rfl⟩
    exact (four_generator_rows i j).1
  · rintro _ ⟨j, rfl⟩
    exact (four_generator_rows i j).2

/-- V is normal in the full local group. -/
public theorem three_conj (a x : Second) (hx : x ∈ threeGroup) :
    a * x * a⁻¹ ∈ threeGroup := by
  apply conj_of_generator_normalizers threeGroup ?_ a x hx
  intro i
  apply normalizer_of_two_sided
  · rintro _ ⟨j, rfl⟩
    exact (three_generator_rows i j).1
  · rintro _ ⟨j, rfl⟩
    exact (three_generator_rows i j).2

private theorem orbit_rows : ∀ i : Fin 8, threeRows i ≠ 1 → threeRows i ≠ centralPoint →
    orbitRow i * exceptionalPoint * (orbitRow i)⁻¹ = threeRows i := by decide +kernel

/-- The six nonidentity, noncentral points of V form one local conjugacy class. -/
public theorem three_fusion (x y : Second) (hx : x ∈ threeGroup) (hy : y ∈ threeGroup)
    (hx1 : x ≠ 1) (hxz : x ≠ centralPoint) (hy1 : y ≠ 1) (hyz : y ≠ centralPoint) :
    IsConj x y := by
  have h (u : Second) (hu : u ∈ threeGroup) (h1 : u ≠ 1) (hz : u ≠ centralPoint) :
      IsConj exceptionalPoint u := by
    obtain ⟨i, rfl⟩ := hu
    exact isConj_iff.mpr ⟨orbitRow i, orbit_rows i h1 hz⟩
  exact (h x hx hx1 hxz).symm.trans (h y hy hy1 hyz)

private theorem fusion_rows : ∀ i : Fin 384,
    element i ∈ exceptionalSubgroup → element i ∉ fourGroup → (element i) ^ 2 = 1 →
    element (fusionRow i) * outerPoint * (element (fusionRow i))⁻¹ = element i ∨
    ∀ j : Fin 384, element j ∈ exceptionalSubgroup →
      element j * element i = element i * element j →
      (element j) ^ 2 = 1 ∨ (element j) ^ 2 = centralPoint := by decide +kernel

/-- A commuting square different from 1 and z detects the required outer class. -/
public theorem square_fusion (q r : exceptionalSubgroup)
    (hq : (q : Second) ∉ fourGroup) (hq2 : q ^ 2 = 1)
    (hc : r * q = q * r) (hr1 : r ^ 2 ≠ 1)
    (hrz : ((r ^ 2 : exceptionalSubgroup) : Second) ≠ centralPoint) :
    IsConj outerPoint (q : Second) := by
  obtain ⟨i, hi⟩ := element_bijective.2 (q : Second)
  have h := fusion_rows i (hi ▸ q.property) (hi ▸ hq)
    (by simpa only [hi, Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hq2)
  rcases h with h | h
  · exact isConj_iff.mpr ⟨element (fusionRow i), h.trans hi⟩
  · obtain ⟨j, hj⟩ := element_bijective.2 (r : Second)
    rw [hi] at h
    have hh := h j (hj ▸ r.property) (by simpa only [hj, Subgroup.coe_mul] using congrArg Subtype.val hc)
    rw [hj] at hh
    rcases hh with hh | hh
    · exact (hr1 (Subtype.ext hh)).elim
    · exact (hrz hh).elim
end Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl.ExceptionalAction
