module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.Hyperplane
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryParabolicNatural.RepeatedOffender
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison

/-!
# Natural-copy ratios and the missing A.3.19 multiplicity premise

For s positive, the repeated natural SL₃ action has quadratic ratio s/2.
The same hyperplane actor has rank 2n and fixed codimension sn, and acts
faithfully by conjugation on full SL₃ because its scalar center has odd
order. Thus three copies give a faithful action of cubic ratio at most
two and dimension 9n. This also holds over the smallest nonbinary even
field F₄. It disproves the proposed deduction of fewer than three copies
from the numerical budget and actor faithfulness alone.

This is not a counterexample to the original chosen-module statement:
no simple QTKE ambient group or Fundamental Setup is constructed here.
`Multiplicity.SourceRatio` applies these calculations to the literal
chosen quotient and LT action. The preliminary source owner retains the
ambient argument needed for unconditional 11.0.4.

Source: Aschbacher--Smith, D.3.9(1), pp.199--200, and A.3.19, pp.54--55,
as invoked in 11.0.4, p.760. The hyperplane calculation reuses K.3.2.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups ENNReal
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
namespace NaturalMultiplicity
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

/-- The same actor pays its fixed codimension separately on every copy. -/
theorem repeated_fixedCodim [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (s : ℕ) (A : Subgroup H) :
    fixedCodim (repeated ρ s) A = s * fixedCodim ρ A := by
  have he : repeated ρ s = BinaryParabolicNatural.copies (Fin s) ρ := by
    ext g v i
    rfl
  rw [he]
  simpa only [Fintype.card_fin] using
    BinaryParabolicNatural.fixedCodim_copies (Fin s) ρ A

/-- Repetition multiplies the cost while retaining the original actor rank. -/
theorem repeated_actionRatio [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (s : ℕ) (A : Subgroup H) :
    actionRatio (repeated ρ s) A = s * actionRatio ρ A := by
  rw [actionRatio, repeated_fixedCodim, Nat.cast_mul, mul_div_assoc, actionRatio]

/-- Quadraticity holds coordinatewise on the repeated action. -/
theorem repeated_quadratic (ρ : Representation (ZMod 2) H W) (s : ℕ)
    {A : Subgroup H} (hq : IsQuadratic ρ A) : IsQuadratic (repeated ρ s) A := by
  intro a ha b hb v
  funext i
  exact hq a ha b hb (v i)

/-- The exact quadratic ratio on a positive number of natural SL₃ copies. -/
theorem natural_quadraticRatio (F : BinaryField) {s : ℕ} (hs : 0 < s) :
    quadraticRatio (repeated (linearNatural F 3) s) = s / 2 := by
  apply le_antisymm
  · apply iInf_le_of_le (ChapterK.Linear.Natural.hyperplaneCentralizer F 3 0)
    apply iInf_le_of_le ⟨ChapterK.Linear.Natural.hyperplaneCentralizer_elementary F 3 0
      (by decide), repeated_quadratic _ s
        (ChapterK.Linear.Natural.hyperplaneCentralizer_quadratic F 3 0)⟩
    rw [repeated_actionRatio, ChapterK.Linear.Natural.hyperplaneCentralizer_actionRatio F 3 0
      (by decide)]
    norm_num [div_eq_mul_inv]
  · apply le_iInf
    intro A
    apply le_iInf
    rintro ⟨hA,hq⟩
    have hq₀ : IsQuadratic (linearNatural F 3) A := by
      intro a ha b hb v
      exact congrFun (hq a ha b hb (fun _ => v)) ⟨0,hs⟩
    have h := ChapterK.Linear.Natural.quadratic_actionRatio_ge F 3 (by decide) hA hq₀
    rw [repeated_actionRatio]
    have hh : (s : ℝ≥0∞) * (1 / (3 - 1 : ℕ)) ≤ s * actionRatio (linearNatural F 3) A := by
      gcongr
    simpa only [show 3 - 1 = 2 from rfl, Nat.cast_ofNat, mul_one_div] using hh

/-- The hyperplane actor also witnesses this cubic-ratio upper bound. -/
theorem natural_cubicRatio_le (F : BinaryField) {s : ℕ} (hs : 0 < s) :
    cubicRatio (repeated (linearNatural F 3) s) ≤ s / 2 :=
  (cubicRatio_le_quadraticRatio _).trans_eq (natural_quadraticRatio F hs)

/-- A positive number of natural copies retains the full SL₃ group faithfully. -/
theorem natural_repeated_faithful (F : BinaryField) {s : ℕ} (hs : 0 < s) :
    Function.Injective (repeated (linearNatural F 3) s) := by
  intro a b hab
  apply specialLinearNatural_injective 3
  apply LinearMap.ext
  intro v
  exact congrFun (LinearMap.congr_fun hab (fun _ => v)) ⟨0,hs⟩

/-- The binary dimension of the repeated natural coordinates. -/
theorem natural_finrank (F : BinaryField) (s : ℕ) :
    Module.finrank (ZMod 2) (Fin s → Fin 3 → F.Carrier) = s * (3 * F.degree) := by
  have hF : Module.finrank (ZMod 2) F.Carrier = F.degree := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
    rw [Nat.card_zmod,F.card_eq] at hc
    exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm
  simp only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,hF]

/-- Every elementary two-subgroup of the full SL₃ group is faithful by
conjugation on that group: its kernel lies in the odd scalar center. -/
theorem elementary_conjugation_injective (F : BinaryField)
    (A : Subgroup SL(3,F.Carrier)) [IsElementaryAbelian 2 A] :
    Function.Injective ((MulAut.conj : SL(3,F.Carrier) →* MulAut SL(3,F.Carrier)).comp
      A.subtype) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz : IsPGroup 3 (center SL(3,F.Carrier)) :=
    IsPGroup.of_card_dvd_pow (n := 1)
      (by simpa using Matrix.SL3.card_center_dvd_three F.Carrier)
  have hd : Disjoint A (center SL(3,F.Carrier)) :=
    (IsElementaryAbelian.isPGroup 2 A).disjoint_of_coprime hz (by decide)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have haZ : (a : SL(3,F.Carrier)) ∈ center SL(3,F.Carrier) := by
    apply mem_center_iff.mpr
    intro g
    have he : MulAut.conj (a : SL(3,F.Carrier)) = 1 := ha
    have he' : (a : SL(3,F.Carrier)) * g * (a : SL(3,F.Carrier))⁻¹ = g :=
      DFunLike.congr_fun he g
    exact ((mul_inv_eq_iff_eq_mul).mp he').symm
  exact Subtype.ext (mem_bot.mp (hd.eq_bot ▸ ⟨a.property,haZ⟩))

/-- The same faithful hyperplane actor has rank 2n on every repeated
natural module and costs exactly sn fixed codimensions. -/
theorem natural_hyperplane_cost (F : BinaryField) (s : ℕ) :
    let A := ChapterK.Linear.Natural.hyperplaneCentralizer F 3 0
    IsElementaryTwo A ∧
    Function.Injective ((MulAut.conj : SL(3,F.Carrier) →* MulAut SL(3,F.Carrier)).comp
      A.subtype) ∧
    IsQuadratic (repeated (linearNatural F 3) s) A ∧
    rank A = 2 * F.degree ∧
    fixedCodim (repeated (linearNatural F 3) s) A = s * F.degree := by
  let A := ChapterK.Linear.Natural.hyperplaneCentralizer F 3 0
  have hA : IsElementaryTwo A :=
    ChapterK.Linear.Natural.hyperplaneCentralizer_elementary F 3 0 (by decide)
  let := hA.2
  refine ⟨hA,elementary_conjugation_injective F A,
    repeated_quadratic _ s (ChapterK.Linear.Natural.hyperplaneCentralizer_quadratic F 3 0),
    ?_,?_⟩
  · simpa only [show 3 - 1 = 2 from rfl,mul_comm] using
      ChapterK.Linear.Natural.hyperplaneCentralizer_rank F 3 0
  · rw [repeated_fixedCodim]
    rw [ChapterK.Linear.Natural.subgroup_fixedCodim F 3 0 le_rfl hA.1]

/-- The numerical budget and faithful action admit three natural copies.
The hyperplane actor's conjugation faithfulness and exact cost are supplied
by `natural_hyperplane_cost`; ambient FSU hypotheses are not asserted. -/
theorem three_copy_obstruction (F : BinaryField) :
    Function.Injective (repeated (linearNatural F 3) 3) ∧
    quadraticRatio (repeated (linearNatural F 3) 3) = 3 / 2 ∧
    cubicRatio (repeated (linearNatural F 3) 3) ≤ 2 ∧
    ¬ Module.finrank (ZMod 2) (Fin 3 → Fin 3 → F.Carrier) < 9 * F.degree := by
  refine ⟨natural_repeated_faithful F (by decide), natural_quadraticRatio F (by decide),
    (natural_cubicRatio_le F (by decide : 0 < 3)).trans
      (by norm_num [ENNReal.div_le_iff]), ?_⟩
  rw [natural_finrank]
  omega


variable {H K W : Type*} [Group H] [Group K]
    [AddCommGroup W] [Module (ZMod 2) W]

/-- A literal natural quotient of a subgroup supplies a half-ratio actor
in the faithful ambient action image. No elementary actor is lifted through
the covering kernel. -/
theorem cubicRatio_le_half_of_natural_quotient (F : BinaryField)
    (ρ : Representation (ZMod 2) H W) (i : K →* H)
    (η : K →* SL(3,F.Carrier)) (hη : Function.Surjective η)
    (e : W ≃ₗ[ZMod 2] (Fin 3 → F.Carrier))
    (he : ∀ k v, e (ρ (i k) v) = (linearNatural F 3) (η k) (e v)) :
    cubicRatio (imageRepresentation ρ) ≤ 1 / 2 := by
  let a := (actionHom ρ).comp i
  have hk : η.ker ≤ a.ker := by
    intro k hk
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (ρ (i k) v) = e v
    rw [he,show η k = 1 from hk,map_one,Module.End.one_apply]
  let j := η.liftOfSurjective hη ⟨a,hk⟩
  have hj (k : K) : j (η k) = a k := η.liftOfRightInverse_comp_apply _ _ _ k
  have hjact (g : SL(3,F.Carrier)) (v : W) :
      e (imageRepresentation ρ (j g) v) = (linearNatural F 3) g (e v) := by
    obtain ⟨k,rfl⟩ := hη g
    rw [hj]
    exact he k v
  have hinj : Function.Injective j := by
    intro g h hgh
    apply ChapterK.Linear.Natural.natural_injective F 3
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    rw [← hjact,← hjact,hgh]
  have hq := quadraticRatio_le_of_injective_equivariant
    (linearNatural F 3) (imageRepresentation ρ) j hinj e.symm (by
      intro g v
      apply e.injective
      simp only [e.apply_symm_apply,hjact])
  exact (cubicRatio_le_quadraticRatio _).trans (hq.trans_eq (by
    simpa using ChapterK.Linear.Natural.quadraticRatio_eq F 3 (by decide)))

end NaturalMultiplicity
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
