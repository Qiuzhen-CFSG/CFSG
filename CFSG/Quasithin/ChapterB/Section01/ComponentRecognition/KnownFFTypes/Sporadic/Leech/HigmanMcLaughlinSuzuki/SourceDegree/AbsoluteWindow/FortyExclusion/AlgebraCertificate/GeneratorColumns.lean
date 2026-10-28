module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.NormIdeal
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.GeneratorCover

/-!
# Finite generator columns suffice for the HS norm certificate

A finite family containing the identity spans modulo an ideal once its span
is stable under left multiplication by the two actual HS generators.
Finite-group generation supplies the inverse steps. Combining this spanning
argument with a nilpotence proof constructs exactly the existing
`NormCertificate`; the finite column relations remain explicit here.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, HS paragraph, author-preprint p.16.
-/

@[expose] public section
open scoped BigOperators MonoidAlgebra
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion
namespace AlgebraCertificate

/-- The literal defining generators, in ATLAS order. -/
noncomputable def generator (s : Fin 2) : KnownSimple.SporadicName.hs.Carrier :=
  if s = 0 then _root_.Sporadic.LeechRelated.HS.generatorAElement
  else _root_.Sporadic.LeechRelated.HS.generatorBElement

/-- Lift a finite vector using actual group elements. -/
noncomputable def lift {n : ℕ} (b : Fin n → KnownSimple.SporadicName.hs.Carrier) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] BinaryAlgebra :=
  ∑ i, (LinearMap.proj i).smulRight (MonoidAlgebra.single (b i) 1)

theorem lift_apply {n : ℕ} (b : Fin n → KnownSimple.SporadicName.hs.Carrier)
    (v : Fin n → ZMod 2) : lift b v = ∑ i, MonoidAlgebra.single (b i) (v i) := by
  simp [lift, LinearMap.sum_apply, MonoidAlgebra.smul_single]

theorem lift_single {n : ℕ} (b : Fin n → KnownSimple.SporadicName.hs.Carrier)
    (j : Fin n) : lift b (Pi.single j 1) = MonoidAlgebra.single (b j) 1 := by
  classical
  rw [lift_apply]
  simp [Pi.single_apply, apply_ite]

private theorem smul_mem (J : TwoSidedIdeal BinaryAlgebra) (c : ZMod 2)
    {x : BinaryAlgebra} (hx : x ∈ J) : c • x ∈ J := by
  rw [Algebra.smul_def]
  exact J.mul_mem_left _ _ hx

private theorem linear_mem_of_single {n : ℕ} (J : TwoSidedIdeal BinaryAlgebra)
    (f : (Fin n → ZMod 2) →ₗ[ZMod 2] BinaryAlgebra)
    (h : ∀ j, f (Pi.single j 1) ∈ J) (v : Fin n → ZMod 2) : f v ∈ J := by
  classical
  rw [pi_eq_sum_univ' v, map_sum]
  apply sum_mem
  intro j _
  rw [map_smul]
  exact smul_mem J _ (h j)

private theorem generators_monoid_closure : Submonoid.closure (Set.range generator) = ⊤ := by
  let : Finite KnownSimple.SporadicName.hs.Carrier :=
    inferInstanceAs (Finite _root_.Sporadic.LeechRelated.HS.Carrier)
  have h : Subgroup.closure (Set.range generator) = ⊤ := by
    apply _root_.Sporadic.LeechRelated.HS.eq_top_of_generators_mem
    · exact Subgroup.subset_closure ⟨0, by simp [generator]; rfl⟩
    · exact Subgroup.subset_closure ⟨1, by simp [generator]; rfl⟩
  rw [← Subgroup.closure_toSubmonoid_of_finite, h]
  rfl

/-- Only the two sets of basis columns, rather than all group elements, need
finite witnesses. The ideal is the literal ideal supplied to the constructor. -/
def GeneratorColumns {n : ℕ} (J : TwoSidedIdeal BinaryAlgebra)
    (b : Fin n → KnownSimple.SporadicName.hs.Carrier) : Prop :=
  ∀ (s : Fin 2) (j : Fin n), ∃ c : Fin n → ZMod 2,
    MonoidAlgebra.single (generator s * b j) 1 - lift b c ∈ J

/-- The finite column relations extend to the whole actual group algebra. -/
theorem exists_lift_of_generatorColumns {n : ℕ} (J : TwoSidedIdeal BinaryAlgebra)
    (b : Fin n → KnownSimple.SporadicName.hs.Carrier)
    (e : Fin n) (he : b e = 1) (h : GeneratorColumns J b)
    (g : KnownSimple.SporadicName.hs.Carrier) :
    ∃ c : Fin n → ZMod 2, MonoidAlgebra.single g 1 - lift b c ∈ J := by
  classical
  choose columns hc using h
  let action (s : Fin 2) : Module.End (ZMod 2) (Fin n → ZMod 2) :=
    ∑ j, (LinearMap.proj j).smulRight (columns s j)
  have ha (s : Fin 2) (j : Fin n) : action s (Pi.single j 1) = columns s j := by
    simp [action, LinearMap.sum_apply, Pi.single_apply]
  have compat (s : Fin 2) (v : Fin n → ZMod 2) :
      MonoidAlgebra.single (generator s) 1 * lift b v - lift b (action s v) ∈ J := by
    let f := (LinearMap.mulLeft (ZMod 2) (MonoidAlgebra.single (generator s) 1)).comp
      (lift b) - (lift b).comp (action s)
    apply linear_mem_of_single J f
    intro j
    change MonoidAlgebra.single (generator s) 1 * lift b (Pi.single j 1) -
      lift b (action s (Pi.single j 1)) ∈ J
    rw [lift_single, ha, MonoidAlgebra.single_mul_single, one_mul]
    exact hc s j
  apply Submonoid.induction_of_closure_eq_top_left
    (motive := fun g => ∃ c : Fin n → ZMod 2,
      MonoidAlgebra.single g 1 - lift b c ∈ J) generators_monoid_closure g
  · refine ⟨Pi.single e 1, ?_⟩
    rw [lift_single, he, sub_self]
    exact J.zero_mem
  · rintro _ ⟨s, rfl⟩ y ⟨v, hv⟩
    refine ⟨action s v, ?_⟩
    have h₁ := J.mul_mem_left (MonoidAlgebra.single (generator s) 1) _ hv
    have h₂ := compat s v
    have hsum : MonoidAlgebra.single (generator s * y) 1 - lift b (action s v) =
        MonoidAlgebra.single (generator s) 1 *
          (MonoidAlgebra.single y 1 - lift b v) +
        (MonoidAlgebra.single (generator s) 1 * lift b v - lift b (action s v)) := by
      rw [mul_sub, MonoidAlgebra.single_mul_single, one_mul]
      abel
    rw [hsum]
    exact J.add_mem h₁ h₂

/-- Assemble the existing contract from finite generator columns and the
separate nilpotence calculation. No certificate data are asserted here. -/
noncomputable def of_generatorColumns (J : TwoSidedIdeal BinaryAlgebra) (r : ℕ)
    (hr : ∀ xs : List BinaryAlgebra, xs.length = r →
      (∀ x ∈ xs, x ∈ J) → xs.prod ∈ fiveNormIdeal)
    {n : ℕ} (hn : n < 1600) (b : Fin n → KnownSimple.SporadicName.hs.Carrier)
    (e : Fin n) (he : b e = 1) (hc : GeneratorColumns J b) : NormCertificate where
  ideal := J
  exponent := r
  nilpotent := hr
  size := n
  size_lt := hn
  basis := b
  spanning g := by
    simpa only [lift_apply] using exists_lift_of_generatorColumns J b e he hc g

/-- The direct norm quotient route needs no radical premise when fewer than
1600 group elements already satisfy the column criterion modulo the norm ideal. -/
noncomputable def of_normColumns {n : ℕ} (hn : n < 1600)
    (b : Fin n → KnownSimple.SporadicName.hs.Carrier) (e : Fin n) (he : b e = 1)
    (hc : GeneratorColumns fiveNormIdeal b) : NormCertificate :=
  of_generatorColumns fiveNormIdeal 1 (by
    intro xs hlen hmem
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    simpa using hmem x (by simp)) hn b e he hc

end AlgebraCertificate
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion
