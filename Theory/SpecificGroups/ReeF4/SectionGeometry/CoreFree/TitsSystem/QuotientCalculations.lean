module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientDefs
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.Torus
public import Theory.AlgebraicGroup.BNPair.Representatives

/-!
# Quotient reductions for the concrete Ree word calculations

The normalizer, torus, Borel and orbit words are the concrete subgroups and
matrices from `Basic` and `Torus`. Generation of the normalizer by its fixed
torus and orbit words gives generation of its quotient. A word leaving the
Borel under conjugation proves both nonidentity of its quotient class and the
BN nontriviality axiom. Finally, the pointwise word exchange law implies the
representative-independent exchange law used by `TitsSystem`.

All geometric premises remain explicit. In particular these reductions do
not construct a relative Weyl presentation or prove the word exchange law.
The final Tits-system owner must discharge them in the actual fixed group.

Source: GLS3 2.3.4(b), `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.SectionGeometry.BNPair
open Theory.AlgebraicGroup Subgroup LargeLocalSeeds Parabolics Parabolics.Binary.FixedGeometry
open scoped Pointwise

/-- The actual Borel double coset of a specified fixed matrix. -/
def borelCell (m : ℕ) (n : Model m) : Set (Model m) :=
  (borel m : Set (Model m)) * {n} * (borel m : Set (Model m))

variable (m : ℕ)
variable [((borel m ⊓ normalizerWords m).subgroupOf (normalizerWords m)).Normal]

/-- The fixed torus dies in the quotient, leaving the two orbit generators. -/
theorem simpleReflections_generate_of_normalizerWords
    (hN : normalizerWords m ≤ fixedTorus m ⊔ weylSubgroup m) :
    closure (simpleReflections m) = ⊤ := by
  let q : normalizerWords m →* WeylQuotient m := QuotientGroup.mk' _
  let K := (closure (simpleReflections m)).comap q
  have hT : fixedTorus m ≤ K.map (normalizerWords m).subtype := by
    intro t ht
    let n : normalizerWords m := ⟨t, fixedTorus_le_normalizerWords m ht⟩
    refine ⟨n, ?_, rfl⟩
    change q n ∈ closure (simpleReflections m)
    have hn : q n = 1 := (QuotientGroup.eq_one_iff n).mpr
      (show t ∈ borel m ⊓ normalizerWords m from fixedTorus_le_intersection m ht)
    rw [hn]
    exact one_mem _
  have hW : weylSubgroup m ≤ K.map (normalizerWords m).subtype := by
    apply (closure_le _).mpr
    rintro x ⟨s, rfl⟩
    exact ⟨simpleLift m s, subset_closure (simpleReflection_mem m s), rfl⟩
  apply top_unique
  intro w _
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective
    ((borel m ⊓ normalizerWords m).subgroupOf (normalizerWords m)) w
  obtain ⟨n', hn', he⟩ := (hN.trans (sup_le hT hW)) n.property
  have he' : n' = n := Subtype.ext he
  subst n'
  exact hn'

/-- A conjugation witness outside the Borel rules out the identity class. -/
theorem simpleReflection_ne_one_of_witness (s : Side)
    (hw : ∃ b ∈ borel m, weylLift m s * b * weylLift m s ∉ borel m) :
    simpleReflection m s ≠ 1 := by
  intro he
  have hn := (QuotientGroup.eq_one_iff (simpleLift m s)).mp he
  have hB : weylLift m s ∈ borel m := hn.1
  obtain ⟨b, hb, hw⟩ := hw
  exact hw ((borel m).mul_mem ((borel m).mul_mem hB hb) hB)

/-- Separation of the two actual word cosets distinguishes their classes. -/
theorem simpleReflection_linear_ne_suzuki_of_separation
    (hsep : (weylLift m .linear)⁻¹ * weylLift m .suzuki ∉ borel m) :
    simpleReflection m .linear ≠ simpleReflection m .suzuki := by
  intro he
  let q : normalizerWords m →* WeylQuotient m := QuotientGroup.mk' _
  have hq : q ((simpleLift m .linear)⁻¹ * simpleLift m .suzuki) = 1 := by
    rw [map_mul, map_inv]
    change (simpleReflection m .linear)⁻¹ * simpleReflection m .suzuki = 1
    rw [he, inv_mul_cancel]
  have hn := (QuotientGroup.eq_one_iff
    ((simpleLift m .linear)⁻¹ * simpleLift m .suzuki)).mp hq
  exact hsep hn.1

/-- Exchange for actual word representatives descends to the quotient classes. -/
theorem exchange_of_word_exchange
    (he : ∀ s : Side, ∀ n ∈ normalizerWords m, ∀ b ∈ borel m,
      weylLift m s * b * n ∈ borelCell m (weylLift m s * n) ∪ borelCell m n) :
    ∀ s ∈ simpleReflections m, ∀ w : WeylQuotient m,
      TitsSystem.representativeSet (borel m) (normalizerWords m) s *
        (borel m : Set (Model m)) *
        TitsSystem.representativeSet (borel m) (normalizerWords m) w ⊆
      ((borel m : Set (Model m)) *
        TitsSystem.representativeSet (borel m) (normalizerWords m) (s * w) *
        (borel m : Set (Model m))) ∪
      ((borel m : Set (Model m)) *
        TitsSystem.representativeSet (borel m) (normalizerWords m) w *
        (borel m : Set (Model m))) := by
  rintro _ ⟨s, rfl⟩ w
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective
    ((borel m ⊓ normalizerWords m).subgroupOf (normalizerWords m)) w
  have hprod : QuotientGroup.mk' _ (simpleLift m s * n) =
      simpleReflection m s * QuotientGroup.mk' _ n := map_mul _ _ _
  rw [TitsSystem.B_mul_representativeSet_mul_B (borel m) (normalizerWords m)
      _ (simpleLift m s * n) hprod,
    TitsSystem.B_mul_representativeSet_mul_B (borel m) (normalizerWords m) _ n rfl]
  rw [mul_assoc, TitsSystem.B_mul_representativeSet (borel m) (normalizerWords m)
      _ n rfl, ← mul_assoc,
    TitsSystem.representativeSet_mul_B (borel m) (normalizerWords m)
      (simpleReflection m s) (simpleLift m s) rfl]
  rintro _ ⟨y, ⟨a, ha, b, hb, rfl⟩, z, hz, rfl⟩
  rw [Set.mem_singleton_iff] at ha hz
  subst a z
  exact he s n n.property b hb

/-- A word conjugation witness also proves the representative-set inequality. -/
theorem nontrivial_of_word_witness
    (hw : ∀ s : Side, ∃ b ∈ borel m,
      weylLift m s * b * weylLift m s ∉ borel m) :
    ∀ s ∈ simpleReflections m,
      TitsSystem.representativeSet (borel m) (normalizerWords m) s *
        (borel m : Set (Model m)) *
        TitsSystem.representativeSet (borel m) (normalizerWords m) s ≠
          (borel m : Set (Model m)) := by
  rintro _ ⟨s, rfl⟩ he
  obtain ⟨b, hb, hw⟩ := hw s
  apply hw
  have hn : weylLift m s ∈
      TitsSystem.representativeSet (borel m) (normalizerWords m)
        (simpleReflection m s) := ⟨simpleLift m s, rfl, rfl⟩
  have hx : weylLift m s * b * weylLift m s ∈
      TitsSystem.representativeSet (borel m) (normalizerWords m)
        (simpleReflection m s) * (borel m : Set (Model m)) *
      TitsSystem.representativeSet (borel m) (normalizerWords m)
        (simpleReflection m s) :=
    ⟨weylLift m s * b, ⟨weylLift m s, hn, b, hb, rfl⟩, weylLift m s, hn, rfl⟩
  rwa [he] at hx

end ReeF4.SectionGeometry.BNPair
