module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.FactorOrbit
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree.SourceFactor
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product
public import Theory.SpecificGroups.PSL3.OddDegreeProjectiveComparison
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import FeitThompson.FinalTheorem
public import CFSG.Quasithin.ChapterB.Section06To07.OffenderGeneration
/-!
# The actual SL3 factor rows are impossible in a minimal parabolic

An odd-degree binary SL3 factor is simple and perfect. In an original B.5.6
product it is subnormal in the ambient group, and its Sylow conjugates
therefore generate the full residual. Its actual normalizer module chart
has two invariant parabolics, contradicting the proved component-automizer
minimal-parabolic theorem. All component, orbit and parity conditions are
derived from the original marked factor; no representation descent through
centralizer scalars is used.

The final consumer applies this to both original offender factors. Natural
SL2, symmetric-five and the genuine four-dimensional exceptional extension
are retained with their exact source modules.

Source: Aschbacher–Smith, B.5.6(3) and B.6.9, pp.105 and 115–116.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

/-- The marked source factor supplies its component and full residual orbit. -/
theorem source_linearThree_factor_structure
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (A : Subgroup Y) [A.Normal]
    (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (F : BinaryField) (hodd : Odd F.degree)
    (e : A ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :
    IsSimpleGroup (A.map Y.subtype) ∧ IsComponent G (A.map Y.subtype) ∧
      2 ∣ Nat.card (A.map Y.subtype) ∧
      componentOrbit (A.map Y.subtype) (T : Subgroup G) = pResidual 2 G := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F.Carrier) :=
    Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :=
    (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv F.card_eq hodd).isSimpleGroup
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :=
    Atlas.sl_perfect 3 (by decide)
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (Matrix.PSL3.OddDegreeProjectiveComparison.center_eq_bot F.card_eq hodd)).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  let : IsSimpleGroup A := e.isSimpleGroup
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv e.symm
  let eA := A.equivMapOfInjective Y.subtype Y.subtype_injective
  let : IsSimpleGroup (A.map Y.subtype) := eA.symm.isSimpleGroup
  let : IsQuasisimple (A.map Y.subtype) := IsQuasisimple.of_mulEquiv eA
  have hc : IsComponent G (A.map Y.subtype) :=
    ⟨(inferInstance : A.Normal).isSubnormal.trans' (inferInstance : Y.Normal).isSubnormal,
      inferInstance⟩
  have hn : Y ≤ normalizer (A.map Y.subtype : Set G) := by
    have hh := A.le_normalizer_map Y.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have heven : 2 ∣ Nat.card (A.map Y.subtype) := by
    by_contra hh
    have ho : Odd (Nat.card (A.map Y.subtype)) := Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using hh)
    exact Group.IsPerfect.not_isSolvable (A.map Y.subtype) (odd_order_theorem _ ho)
  exact ⟨inferInstance,hc,heven,source_factor_orbit_eq_residual T hP Y _ hn hgen⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- No doubled-natural SL3 row survives in the original normal Sylow supplement. -/
theorem source_normal_repeated_three_factor_excluded
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (A : Subgroup Y) [A.Normal]
    (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (U : Subrepresentation (ρ.comp Y.subtype))
    (hU : U.toSubmodule = moved (ρ.comp Y.subtype) A)
    (F : BinaryField) (hodd : Odd F.degree) (r : ℕ) (hr : 0 < r)
    (h : IsRepeatedLinearNatural
      (((fixed (ρ.comp Y.subtype)).quotientImage U).toRepresentation.comp A.subtype) F 3 r) :
    False := by
  obtain ⟨e⟩ := h
  obtain ⟨hs,hc,he,ho⟩ := source_linearThree_factor_structure T hP Y A hgen F hodd e.groupEquiv
  let := hs
  exact source_repeated_three_factor_excluded ρ Y A U T hP hc he ho hU F r hr ⟨e⟩

/-- No single-natural SL3 row survives in the original normal Sylow supplement. -/
theorem source_normal_natural_three_factor_excluded
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (A : Subgroup Y) [A.Normal]
    (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (U : Subrepresentation (ρ.comp Y.subtype))
    (hU : U.toSubmodule = moved (ρ.comp Y.subtype) A)
    (F : BinaryField) (hodd : Odd F.degree)
    (h : IsLinearNatural
      (((fixed (ρ.comp Y.subtype)).quotientImage U).toRepresentation.comp A.subtype) F 3) :
    False := by
  obtain ⟨e⟩ := h
  obtain ⟨hs,hc,he,ho⟩ := source_linearThree_factor_structure T hP Y A hgen F hodd e.groupEquiv
  let := hs
  exact source_natural_three_factor_excluded ρ Y A U T hP hc he ho hU F ⟨e⟩

/-- The surviving source factor rows after excluding both actual SL3 natural rows. -/
inductive RankOneOrExceptionalFactor
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (A : Subgroup D) (U : Subrepresentation σ) : Prop
  | linearTwo (moved_eq : U.toSubmodule = moved σ A) (F : BinaryField)
      (natural : IsLinearNatural
        (((fixed σ).quotientImage U).toRepresentation.comp A.subtype) F 2)
  | symmetricFive (moved_eq : U.toSubmodule = moved σ A)
      (natural : IsSymmetricNatural
        (((fixed σ).quotientImage U).toRepresentation.comp A.subtype) 5)
  | exceptional (moved_le : moved σ A ≤ U.toSubmodule)
      (extension : FourDimensionalSource
        (((fixed σ).quotientImage U).toRepresentation.comp A.subtype))

/-- The literal source row reduces to rank one or its actual exceptional extension. -/
theorem source_normal_factor_rankOne_or_exceptional
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (A : Subgroup Y) [A.Normal]
    (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (U : Subrepresentation (ρ.comp Y.subtype))
    (h : SourceInduction.SourceFactorCase (ρ.comp Y.subtype) A U) :
    RankOneOrExceptionalFactor (ρ.comp Y.subtype) A U := by
  cases h with
  | natural hU hn =>
      cases hn with
      | linearTwo F hn => exact .linearTwo hU F hn
      | symmetricFive hn => exact .symmetricFive hU hn
      | linearThree F ho hn =>
          exact (source_normal_natural_three_factor_excluded ρ T hP Y A hgen U hU F ho hn).elim
  | doubleNatural F ho hU hn =>
      exact (source_normal_repeated_three_factor_excluded ρ T hP Y A hgen U hU F ho 2
        (by decide) hn).elim
  | exceptional hm he => exact .exceptional hm he

/-- The first original factor of an internal product is normal. -/
theorem SourceInduction.InternalProduct.first_normal {D : Type*} [Group D] {A B : Subgroup D}
    (h : SourceInduction.InternalProduct A B) : A.Normal := by
  have he : h.snd.ker = A := by
    ext g
    obtain ⟨a,b,rfl⟩ := h.exists_mul g
    have hs : h.snd ((a : D) * b) = b := by
      rw [← h.apply_eq]
      exact congrArg Prod.snd (h.equiv.symm_apply_apply (a,b))
    change h.snd ((a : D) * b) = 1 ↔ (a : D) * b ∈ A
    rw [hs]
    constructor
    · rintro rfl
      exact A.mul_mem a.property A.one_mem
    · intro hab
      have hb : (b : D) ∈ A := by
        simpa only [inv_mul_cancel_left] using A.mul_mem (A.inv_mem a.property) hab
      have hv : h.equiv (1,b) = h.equiv (⟨b,hb⟩,1) := by
        simp only [h.apply_eq, coe_one, one_mul, mul_one]
      exact congrArg Prod.snd (h.equiv.injective hv)
  rw [← he]
  infer_instance

/-- Apply the reduction to both actual factors in the earlier product decomposition. -/
theorem source_two_factor_rows
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (c : SourceInduction.SourceTwoFactorCase (ρ.comp Y.subtype)) :
    RankOneOrExceptionalFactor (ρ.comp Y.subtype) c.first c.firstSpace ∧
      RankOneOrExceptionalFactor (ρ.comp Y.subtype) c.second c.secondSpace := by
  let := c.product.first_normal
  let := c.product.second_normal
  exact ⟨source_normal_factor_rankOne_or_exceptional ρ T hP Y c.first hgen _ c.firstCase,
    source_normal_factor_rankOne_or_exceptional ρ T hP Y c.second hgen _ c.secondCase⟩

/-- Actual original-offender consumer: generation and normality are derived. -/
theorem source_offender_two_factor_rows [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : Representation.BinaryOffender.IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (c : SourceInduction.SourceTwoFactorCase
      (ρ.comp (Representation.BinaryOffender.offenderSubgroup ρ).subtype)) :
    RankOneOrExceptionalFactor
      (ρ.comp (Representation.BinaryOffender.offenderSubgroup ρ).subtype) c.first c.firstSpace ∧
      RankOneOrExceptionalFactor
        (ρ.comp (Representation.BinaryOffender.offenderSubgroup ρ).subtype) c.second c.secondSpace := by
  let := Representation.BinaryOffender.offenderSubgroup_normal ρ
  exact source_two_factor_rows ρ T hP _ (offender_generation T hP ρ hff hcore).2 c
end CFSG.Quasithin.ChapterB
