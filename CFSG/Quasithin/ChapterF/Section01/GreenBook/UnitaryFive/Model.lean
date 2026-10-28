module

public import Theory.SpecificGroups.ClassicalUnitary.FiveFlag
public import Theory.GroupTheory.Amalgam.RankTwo
public import Theory.Quasithin.EmbeddedNormalTwoRank
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.QuasithinExclusions

/-!
# The marked unitary-five model for F.1.12

The model is the actual image of SU₅ in PGL over a field of order `q²`,
with Frobenius involution `x ↦ x^q` and the identity Hermitian matrix.
Its two parabolics stabilize the explicit isotropic line and plane in
`Theory.SpecificGroups.ClassicalUnitary.FiveFlag`. Their intersection,
with both inclusion maps, gives the marked subgroup amalgam.

We also prove the arithmetic existence of an odd obstruction prime when
`q ≠ 4` and its conditional consequence in any quasithin completion. An
embedding of the base parabolic suffices, including inside an extension.
The concrete rank bound and normal 2-subgroup remain to be constructed;
this module does not assert those calculations or the q = 4 local data.
The source's q = 4 quotient claims concern `Lᵢ/O₂(Lᵢ)`, not the full
parabolic quotients.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
A.2.18, printed p. 40, and F.1.12(7) and its proof, printed pp. 263--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive

open BenderSuzuki.MatrixGroups

/-- Field and form data only: no parabolic structural conclusions are stored. -/
structure Model (q : ℕ) where
  F : Type
  [field : Field F]
  [finite : Finite F]
  [charTwo : CharP F 2]
  form : HermitianForm 5 F
  card : Nat.card F = q ^ 2
  conjugation : ∀ x, form.conj x = x ^ q
  matrix : form.form = 1

attribute [instance] Model.field Model.finite Model.charTwo

/-- The concrete marked model exists for every even prime power. -/
theorem model_nonempty {q : ℕ} (hq : IsPrimePow q) (heven : Even q) :
    Nonempty (Model q) := by
  obtain ⟨F, hF, hfin, hchar, J, hc, hconj, hJ⟩ :=
    Theory.SpecificGroups.UnitaryFive.exists_field q hq heven
  exact ⟨@Model.mk q F hF hfin hchar J hc hconj hJ⟩

/-- One choice of the constructed finite-field model. -/
noncomputable def standardModel {q : ℕ} (hq : IsPrimePow q) (heven : Even q) :
    Model q := Classical.choice (model_nonempty hq heven)

namespace Model

variable {q : ℕ} (M : Model q)

/-- The actual projective special unitary group, rather than a family label. -/
abbrev Carrier := ProjectiveSpecialUnitaryMatrixGroup M.form

instance : Finite M.Carrier := by
  let : Finite (GL (Fin 5) M.F) := Finite.of_injective Units.val Units.val_injective
  exact Finite.of_surjective _ (Theory.SpecificGroups.UnitaryFive.project_surjective M.form)

/-- Stabilizer image for the isotropic line. -/
abbrev leftParabolic : Subgroup M.Carrier :=
  Theory.SpecificGroups.UnitaryFive.lineParabolic M.form

/-- Stabilizer image for the isotropic plane. -/
abbrev rightParabolic : Subgroup M.Carrier :=
  Theory.SpecificGroups.UnitaryFive.planeParabolic M.form

/-- The whole overlap of the two parabolics. -/
def overlap : Subgroup M.Carrier := M.leftParabolic ⊓ M.rightParabolic

/-- The overlap is the projective image of the full common flag stabilizer. -/
theorem overlap_eq_map_flag :
    M.overlap =
      (Theory.SpecificGroups.UnitaryFive.specialStabilizer M.form
          (Theory.SpecificGroups.UnitaryFive.line M.F) ⊓
        Theory.SpecificGroups.UnitaryFive.specialStabilizer M.form
          (Theory.SpecificGroups.UnitaryFive.plane M.F)).map
        (Theory.SpecificGroups.UnitaryFive.project M.form) :=
  (Theory.SpecificGroups.UnitaryFive.parabolic_inf M.form _ _).symm

/-- The marked amalgam with its actual inclusion maps. -/
def amalgam : Theory.GroupTheory.RankTwoAmalgam M.leftParabolic M.overlap M.rightParabolic :=
  .ofSubgroups _ _ _ inf_le_left inf_le_right

/-- The left marking is injective. -/
theorem amalgam_left_injective : Function.Injective M.amalgam.left :=
  Subgroup.inclusion_injective inf_le_left

/-- The right marking is injective. -/
theorem amalgam_right_injective : Function.Injective M.amalgam.right :=
  Subgroup.inclusion_injective inf_le_right

end Model
/-- A nonexceptional even parameter has an odd prime surviving the projective scalar factor. -/
theorem exists_odd_prime {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) (hne : q ≠ 4) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ (q + 1) / Nat.gcd (q + 1) 5 := by
  have hquot : (q + 1) / Nat.gcd (q + 1) 5 ≠ 1 := by
    intro h
    apply hne
    apply ChapterA.Section02.EvenLie.unitary_five_field_size_eq_four hq hq2
    have heq := Nat.div_mul_cancel (Nat.gcd_dvd_left (q + 1) 5)
    rwa [h, one_mul, eq_comm] at heq
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hquot
  refine ⟨p, hp, ?_, hdvd⟩
  have hdiv : p ∣ q + 1 := hdvd.trans
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (q + 1) 5))
  rcases hp.eq_two_or_odd with htwo | hodd
  · subst p
    obtain ⟨k, hk⟩ := hq
    obtain ⟨m, hm⟩ := hdiv
    omega
  · exact Nat.odd_iff.mpr hodd

/-- Conditional exclusion after the actual parabolic rank and normal 2-subgroup are proved. -/
theorem field_size_eq_four_of_embedding
    {G P : Type*} [Group G] [Finite G] [Group P] [Finite P]
    (hG : IsQuasithin G) (f : P →* G) (hf : Function.Injective f)
    (Q : Subgroup P) [Q.Normal] (hQ : Q ≠ ⊥) (hQp : IsPGroup 2 Q)
    {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q)
    (hr : ∀ p : ℕ, p.Prime → p ∣ (q + 1) / Nat.gcd (q + 1) 5 →
      3 ≤ primeRank p P) : q = 4 := by
  by_contra hne
  obtain ⟨p, hp, ho, hdvd⟩ := exists_odd_prime hq hq2 hne
  exact Theory.Quasithin.not_quasithin_of_embedded_normal_two_rank f hf Q hQ hQp p hp ho
    (hr p hp hdvd) hG

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive
