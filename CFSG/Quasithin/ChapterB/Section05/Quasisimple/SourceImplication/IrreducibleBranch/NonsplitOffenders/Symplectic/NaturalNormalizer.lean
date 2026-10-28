module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.NonsplitOffenders.Symplectic.SemilinearOffenders
public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.Coefficients
public import Theory.Representation.FirstCohomologySymplecticFour.LargeField

/-!
# The literal normalizer of the natural symplectic module

The binary normalizer acts semilinearly by the proved scalar-commutant theorem.
An involution with trivial coefficient action has trivial scalar factor:
preservation of the alternating form gives a fourth power equal to one.
For fields larger than two, perfectness places it in the genuine derived image.

The final theorem reduces offender containment to the explicitly displayed
outer-involution centralizer bound. This numerical input is not assumed to
follow from the normalizer description, and remains to be discharged by the
B.5.1 symplectic assembly owner.

Source: Aschbacher--Smith B.5.1, printed p.100; natural-action conventions
B.4.2(3), p.86. This gives an alternative through the faithful natural quotient
to the orthogonal-cover calculation cited as I.2.3, p.413.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair SymplecticConjugatePair.Ambient
open SymplecticConjugatePair.Ambient.Normalizer
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch.Symplectic
open SemilinearCoefficients
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Evaluation on the natural four-space by its actual binary normalizer. -/
noncomputable def naturalNormalizerAction :
    Representation (ZMod 2) (naturalNormalizer (F := F)) (Vector F) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp naturalNormalizer.subtype

omit [Finite F] [CharP F 2] in
/-- The tautological normalizer action is faithful. -/
theorem naturalNormalizerAction_faithful :
    Function.Injective (naturalNormalizerAction (F := F)) := by
  intro g h he
  apply Subtype.ext
  exact LinearEquiv.ext (fun v => LinearMap.congr_fun he v)

/-- Every natural normalizer operator has a coefficient automorphism. -/
theorem naturalNormalizerAction_semilinear (s : naturalNormalizer (F := F)) :
    ∃ σ : F ≃+* F, ∀ (c : F) (v : Vector F),
      naturalNormalizerAction s (c • v) = σ c • naturalNormalizerAction s v := by
  obtain ⟨a, g, σ, he⟩ := naturalNormalizer_semilinear s.val s.property
  refine ⟨σ, fun c v => ?_⟩
  change s.val (c • v) = σ c • s.val v
  rw [he, he]
  have hfield : fieldVector σ (c • v) = σ c • fieldVector σ v := by
    ext i
    exact map_mul σ c (v i)
  change a.val • (symplecticNatural 2 g (fieldVector σ (c • v))) =
    σ c • (a.val • (symplecticNatural 2 g (fieldVector σ v)))
  rw [hfield, map_smul, smul_comm a.val (σ c)]

/-- The genuine homomorphism recording the coefficient automorphism. -/
noncomputable def naturalCoefficient : naturalNormalizer (F := F) →* (F ≃+* F) :=
  coefficientHom naturalNormalizerAction naturalNormalizerAction_semilinear

/-- The coefficient homomorphism describes actual scalar multiplication. -/
theorem naturalCoefficient_smul (s : naturalNormalizer (F := F)) (c : F) (v : Vector F) :
    naturalNormalizerAction s (c • v) = naturalCoefficient s c • naturalNormalizerAction s v :=
  coefficientHom_smul naturalNormalizerAction naturalNormalizerAction_semilinear s c v

/-- The coefficient-trivial involutions are in the genuine natural matrix image. -/
theorem linear_involution_mem_naturalDerivedImage
    (hF : 2 < Nat.card F) (s : naturalNormalizer (F := F)) (hs : s ^ 2 = 1)
    (hc : naturalCoefficient s = 1) : s.val ∈ naturalDerivedImage := by
  obtain ⟨a, g, σ, he⟩ := naturalNormalizer_semilinear s.val s.property
  have hσ : σ = RingEquiv.refl F := by
    apply coefficient_unique naturalNormalizerAction s
    · intro c v
      change s.val (c • v) = σ c • s.val v
      rw [he, he]
      have hfield : fieldVector σ (c • v) = σ c • fieldVector σ v := by
        ext i
        exact map_mul σ c (v i)
      change a.val • (symplecticNatural 2 g (fieldVector σ (c • v))) =
        σ c • (a.val • (symplecticNatural 2 g (fieldVector σ v)))
      rw [hfield, map_smul, smul_comm a.val (σ c)]
    · intro c v
      simpa only [hc, RingAut.one_apply, RingEquiv.refl_apply] using naturalCoefficient_smul s c v
  have hfull (v : Vector F) : s.val v = a.val • (g • v) := by
    rw [he, hσ]
    rfl
  have hform (v w : Vector F) :
      form F (s.val v) (s.val w) = a.val ^ 2 * form F v w := by
    rw [hfull, hfull]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, preserves_form]
    ring
  have hs2 (v : Vector F) : s.val (s.val v) = v :=
    congrArg (fun x : naturalNormalizer (F := F) => x.val v) hs
  let v : Vector F := Pi.single (Sum.inl 0) 1
  let w : Vector F := Pi.single (Sum.inr 0) 1
  have hvw : form F v w = 1 := by simp [form_apply, v, w, Fin.sum_univ_two]
  have ha4 : a.val ^ 2 * a.val ^ 2 = 1 := by
    have hh := hform (s.val v) (s.val w)
    rw [hs2, hs2, hform, hvw, mul_one] at hh
    exact hh.symm
  have ha : a.val = 1 := by
    apply CharTwo.sq_injective
    apply CharTwo.sq_injective
    simpa only [pow_two, one_mul] using ha4
  have hsval : linearAction naturalDerivedAction
      ⟨g, by rw [Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hF]; trivial⟩ = s.val := by
    apply LinearEquiv.ext
    intro x
    change Matrix.mulVec g.val x = s.val x
    simpa only [ha, one_smul, smul_eq_mulVec] using (hfull x).symm
  exact ⟨_, hsval⟩


/-- The natural derived group has trivial coefficient action. -/
theorem naturalCoefficient_eq_one_of_mem (s : naturalNormalizer (F := F))
    (hs : s.val ∈ naturalDerivedImage) : naturalCoefficient s = 1 := by
  apply (coefficient_eq_one_iff naturalNormalizerAction naturalCoefficient
    naturalCoefficient_smul s).mpr
  obtain ⟨g, hg⟩ := hs
  intro c v
  change s.val (c • v) = c • s.val v
  rw [← hg]
  exact (symplecticNatural 2 g.val).map_smul c v

/-- A bound on the actual outer centralizers excludes every outer offender,
including the equality case at degree two. The bound remains an explicit input. -/
theorem naturalNormalizer_offender_le_of_centralizer_bound {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hbound : ∀ s : naturalNormalizer (F := F), orderOf s = 2 →
      s.val ∉ naturalDerivedImage →
      primeRank 2 (centralizer ({s} : Set (naturalNormalizer (F := F)))) ≤ 2 * n)
    {A : Subgroup (naturalNormalizer (F := F))}
    (hA : IsOffender naturalNormalizerAction A) : A ≤ naturalDerivedImage.subgroupOf _ := by
  let : Finite (naturalNormalizer (F := F)) := Finite.of_injective
    (fun s : naturalNormalizer (F := F) => (s.val : Vector F → Vector F))
    (fun s t h => Subtype.ext (LinearEquiv.ext (congrFun h)))
  have hcoeff : A ≤ (naturalCoefficient (F := F)).ker :=
    offender_le_coefficient_kernel_of_centralizer_bound (F := F)
    (naturalNormalizerAction (F := F)) (naturalNormalizerAction_faithful (F := F))
    (naturalCoefficient (F := F)) (naturalCoefficient_smul (F := F)) (by omega : 1 < 2 * n)
    (by rw [finrank_vector hF]; omega :
      Module.finrank (ZMod 2) (Vector F) = 2 * (2 * n))
    (fun s hs hc => hbound s hs (fun hi => hc (naturalCoefficient_eq_one_of_mem s hi))) hA
  have hcard : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
  let := hA.1.2
  intro s hs
  exact linear_involution_mem_naturalDerivedImage hcard s
    (elemPow_eq_one_of_isElementaryAbelian s hs) (hcoeff hs)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch.Symplectic
