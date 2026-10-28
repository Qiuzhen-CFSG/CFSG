module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Normalizer
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Canonical quotient pentagons for the original parabolic family

Two original H-conjugates of F₁ agree exactly when their conjugators carry
the quotient Sylow five-subgroup to the same subgroup. This follows from
the proved original normalizer F₁Q. Hence every quotient pentagon determines
one original conjugate parabolic, independently of the chosen conjugator.
The equivalence retains the literal H/Q map and original endpoint.
Source: the family E(z) in J.4.7, printed p.443.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers.Choices
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (p : Plane d) (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
  (hi : ∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹)

/-- The fixed original quotient pentagon. -/
def basePentagon : Sylow 5 S5 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact B5.mapSurjective d.ru2.quotient_surjective

/-- The literal H-conjugate family of the original first endpoint. -/
def conjugateFamily : Set (Subgroup G) :=
  Set.range fun h : d.toTypeRuSetup.H => (p.F₁ B5).conjBy (h : G)

/-- The original family whose members contain the specified second involution. -/
def family (u : G) : Set (Subgroup G) := {E | E ∈ conjugateFamily p B5 ∧ u ∈ E}

include s hi in
/-- The normalizer condition is preserved by the original quotient map. -/
theorem mem_normalizer_iff_quotient (h : d.toTypeRuSetup.H) :
    (h : G) ∈ normalizer (p.F₁ B5 : Set G) ↔
      d.ru2.quotientMap h ∈ normalizer (basePentagon B5 : Set S5) := by
  have hm : (h : G) ∈ d.toTypeRuSetup.H ⊓ normalizer (p.F₁ B5 : Set G) ↔
      (h : G) ∈ normalizer (p.F₁ B5 : Set G) := and_iff_right h.property
  rw [first_relative_normalizer p s B5 hi] at hm
  rw [← hm]
  change h ∈ (p.F₁ B5 ⊔ d.toTypeRuSetup.Q).subgroupOf d.toTypeRuSetup.H ↔ _
  rw [← preimage_fiveNormalizer p s B5 hi]
  rfl

include s hi in
/-- Equality of actual conjugate parabolics is exactly equality of their quotient pentagons. -/
theorem conjugates_eq_iff (h k : d.toTypeRuSetup.H) :
    (p.F₁ B5).conjBy (h : G) = (p.F₁ B5).conjBy (k : G) ↔
      d.ru2.quotientMap h • basePentagon B5 = d.ru2.quotientMap k • basePentagon B5 := by
  have hstep : (p.F₁ B5).conjBy (h : G) = (p.F₁ B5).conjBy (k : G) ↔
      ((h⁻¹*k : d.toTypeRuSetup.H) : G) ∈ normalizer (p.F₁ B5 : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change _ ↔ (p.F₁ B5).conjBy ((h : G)⁻¹*(k : G)) = p.F₁ B5
    constructor
    · exact (p.F₁ B5).conjBy_inv_mul_cancel
    · intro hh
      have he := congrArg (fun A : Subgroup G => A.conjBy (h : G)) hh
      rw [conjBy_conjBy, mul_inv_cancel_left] at he
      exact he.symm
  rw [hstep, mem_normalizer_iff_quotient p s B5 hi, ← Sylow.smul_eq_iff_mem_normalizer,
    map_mul, map_inv, mul_smul]
  rw [inv_smul_eq_iff, eq_comm]

theorem exists_conjugator (P : Sylow 5 S5) :
    ∃ h : d.toTypeRuSetup.H, d.ru2.quotientMap h • basePentagon B5 = P := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S5 (basePentagon B5) P
  obtain ⟨h, rfl⟩ := d.ru2.quotient_surjective g
  exact ⟨h, hg⟩

/-- One representative, whose resulting parabolic is proved independent of its choice. -/
def pentagonConjugator (P : Sylow 5 S5) : d.toTypeRuSetup.H :=
  Classical.choose (exists_conjugator B5 P)

theorem pentagonConjugator_spec (P : Sylow 5 S5) :
    d.ru2.quotientMap (pentagonConjugator B5 P) • basePentagon B5 = P :=
  Classical.choose_spec (exists_conjugator B5 P)

/-- The original parabolic canonically determined by a quotient pentagon. -/
def parabolicFor (P : Sylow 5 S5) : Subgroup G :=
  (p.F₁ B5).conjBy (pentagonConjugator B5 P : G)

include s hi in
/-- Any original conjugator realizing a quotient pentagon gives this same parabolic. -/
theorem parabolicFor_eq_conjugate (h : d.toTypeRuSetup.H) :
    parabolicFor p B5 (d.ru2.quotientMap h • basePentagon B5) = (p.F₁ B5).conjBy (h : G) := by
  exact (conjugates_eq_iff p s B5 hi _ h).mpr (pentagonConjugator_spec B5 _)

include s hi in
theorem parabolicFor_injective : Function.Injective (parabolicFor p B5) := by
  intro P Q he
  have hh := (conjugates_eq_iff p s B5 hi (pentagonConjugator B5 P)
    (pentagonConjugator B5 Q)).mp he
  simpa only [pentagonConjugator_spec] using hh

theorem parabolicFor_mem (P : Sylow 5 S5) : parabolicFor p B5 P ∈ conjugateFamily p B5 :=
  ⟨pentagonConjugator B5 P, rfl⟩

include s hi in
/-- The canonical pentagons parametrize all original H-conjugates of F₁. -/
def conjugateEquiv : Sylow 5 S5 ≃ conjugateFamily p B5 :=
  Equiv.ofBijective (fun P => ⟨parabolicFor p B5 P, parabolicFor_mem p B5 P⟩) ⟨
    fun _ _ hh => parabolicFor_injective p s B5 hi (congrArg Subtype.val hh), by
      rintro ⟨E, h, rfl⟩
      exact ⟨d.ru2.quotientMap h • basePentagon B5,
        Subtype.ext (parabolicFor_eq_conjugate p s B5 hi h)⟩⟩

theorem conjugateEquiv_apply (P : Sylow 5 S5) :
    (conjugateEquiv p s B5 hi P : Subgroup G) = parabolicFor p B5 P := rfl

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
