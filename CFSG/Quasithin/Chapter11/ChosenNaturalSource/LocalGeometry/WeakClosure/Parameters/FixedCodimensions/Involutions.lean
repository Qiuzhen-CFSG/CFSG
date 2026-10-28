module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Centralizers
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.FullAutomizer
public import Theory.Representation.SL3OddNaturalNormalizer.Semilinear
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner
public import Theory.Representation.G2NaturalInvolutionExclusion
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.SymplecticConjugatePair.Ambient.Semilinear
public import Theory.Representation.BinaryOffender.FaithfulRankOne

/-!
# Involution bounds for the full natural automizer

The faithful quotient action retains every ambient automizer actor. For SL₃
and Sp₄, semilinearity gives the lower bound n: a field-linear nonidentity
operator has positive codimension divisible by n, and a nontrivial field
involution moves half the binary space. The genuine G₂ normalizer theorem
improves the bound to 2n. Passing back through the original coordinate
surjection preserves these lower bounds, including nonsplit central covers.

The local-minimum and residual applications below use these unconditional
bounds. Attainment and odd-prime actors remain explicit here; the Source
endpoint discharges attainment, and the owning parameter task retains the
odd-prime calculation and the hyperplane/root branches.

Source: Aschbacher--Smith, I.2.3(1), B.4.6, and 11.2.2(1--2),
printed pp.413,88--90,767--768.
-/

open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
variable {H F W : Type*} [Group H] [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module F W] [Module (ZMod 2) W] [IsScalarTower (ZMod 2) F W]
  [FiniteDimensional F W]

/-- A faithful semilinear involution on a field space of dimension at least two
moves at least one coefficient-field degree of binary dimensions. -/
private theorem semilinear_involution_lower (ρ : Representation (ZMod 2) H W)
    (hρ : Function.Injective ρ) (hdim : 2 ≤ Module.finrank F W)
    (a : H) (ha : orderOf a = 2)
    (σ : F ≃+* F) (hσ : ∀ r v, ρ a (r • v) = σ r • ρ a v) :
    Module.finrank (ZMod 2) F ≤ fixedCodim ρ (zpowers a) := by
  let : FiniteDimensional (ZMod 2) W := Module.Finite.trans F W
  have ha2 : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
  have haa (v : W) : ρ a (ρ a v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, ha2, map_one,
      Module.End.one_apply]
  by_cases hσ1 : σ = RingEquiv.refl F
  · let Q : Submodule F W := {
      carrier := {v | ρ a v = v}
      zero_mem' := map_zero _
      add_mem' := fun hv hw => by exact (ρ a).map_add _ _ |>.trans (congrArg₂ (· + ·) hv hw)
      smul_mem' := fun r v hv => by
        change ρ a (r • v) = r • v
        rw [hσ, hσ1, RingEquiv.refl_apply, show ρ a v = v from hv] }
    have hfix : fixedSpace ρ (zpowers a) = Q.restrictScalars (ZMod 2) := by
      ext v
      exact mem_fixedSpace_zpowers_iff ρ a v
    have hcod : fixedCodim ρ (zpowers a) =
        Module.finrank (ZMod 2) F * Module.finrank F (W ⧸ Q) := by
      unfold fixedCodim
      rw [hfix, (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) Q).finrank_eq,
        Module.finrank_mul_finrank]
    have hpos := fixedCodim_pos_of_faithful ρ hρ
      (show zpowers a ≠ ⊥ by
        intro h
        have ha1 : a = 1 := mem_bot.mp (h ▸ (mem_zpowers a))
        simp [ha1] at ha)
    exact Nat.le_of_dvd hpos (hcod ▸ dvd_mul_right _ _)
  · have hnon : Nontrivial W := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank F W)
    let := hnon
    obtain ⟨v,hv⟩ := exists_ne (0 : W)
    have hσσ : Function.Involutive σ := by
      intro r
      apply smul_left_injective F hv
      have hh := haa (r • v)
      rw [hσ, hσ, haa] at hh
      exact hh
    have he := SymplecticConjugatePair.Ambient.semilinear_involution_twice_codim
      ρ a ha2 σ hσσ hσ1 hσ
    have hd := Module.finrank_mul_finrank (ZMod 2) F W
    nlinarith
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open SymplecticConjugatePair.Ambient
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Every full-automizer involution in the SL₃ row moves at least n dimensions. -/
theorem sl3_involution_lower
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := D.elementary
    ∀ a : Automizer V, orderOf a = 2 → S.field.degree ≤
      fixedCodim (automizerRepresentation V) (zpowers a) := by
  let := D.elementary
  intro a ha
  let c := Coordinates.sl3 m
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  let := layer_normal D S
  obtain ⟨σ,hσ⟩ := Representation.SL3OddNaturalNormalizer.normalizer_semilinear
    (inducedAutomizer V L) (layerEquiv D S c) ρ hres a
  have hd := semilinear_involution_lower ρ hρ
    (show 2 ≤ Module.finrank S.field.Carrier c.Space by
      change 2 ≤ Module.finrank S.field.Carrier (Fin 3 → S.field.Carrier)
      simp only [Module.finrank_pi, Fintype.card_fin]; omega) a ha σ hσ
  rw [Representation.OneCohomology.coefficient_finrank_of_card 2 _ S.field.card_eq] at hd
  exact hd.trans (fixedCodim_le_of_equivariant_surjection
    (automizerRepresentation V) ρ (projectionLinear D S c)
    (projectionLinear_surjective D S c) he (zpowers a))

/-- The same full-automizer lower bound holds for nonsplit symplectic covers. -/
theorem sp4_involution_lower
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    letI := D.elementary
    ∀ a : Automizer V, orderOf a = 2 → S.field.degree ≤
      fixedCodim (automizerRepresentation V) (zpowers a) := by
  let := D.elementary
  intro a ha
  let c := Coordinates.sp4 m
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  let := layer_normal D S
  have hq : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    have hn := S.nonbinary
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hn
  have hn := SymplecticNaturalNormalizer.operator_mem_naturalNormalizer
    (inducedAutomizer V L) hq (layerEquiv D S c) ρ hres a
  obtain ⟨σ,hσ⟩ := SymplecticNaturalNormalizer.exists_field_twist
    ⟨linearAction ρ a, hn⟩
  have hd := semilinear_involution_lower ρ hρ
    (show 2 ≤ Module.finrank S.field.Carrier c.Space by
      change 2 ≤ Module.finrank S.field.Carrier ((Fin 2 ⊕ Fin 2) → S.field.Carrier)
      simp only [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin]; omega) a ha σ hσ
  rw [Representation.OneCohomology.coefficient_finrank_of_card 2 _ S.field.card_eq] at hd
  exact hd.trans (fixedCodim_le_of_equivariant_surjection
    (automizerRepresentation V) ρ (projectionLinear D S c)
    (projectionLinear_surjective D S c) he (zpowers a))

/-- The genuine six-dimensional G₂ normalizer gives the stronger bound 2n. -/
theorem g2_involution_lower
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) :
    letI := D.elementary
    ∀ a : Automizer V, orderOf a = 2 → 2 * S.field.degree ≤
      fixedCodim (automizerRepresentation V) (zpowers a) := by
  let := D.elementary
  intro a ha
  let c := Coordinates.g2 m
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  let := layer_normal D S
  let : Algebra (ZMod 2) S.field.Carrier := ZMod.algebra S.field.Carrier 2
  let f : c.Space →+ Atlas.G2.Natural.Space S.field.Carrier := {
    toFun := id
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  let E : c.Space ≃ₗ[ZMod 2] Atlas.G2.Natural.Space S.field.Carrier :=
    LinearEquiv.ofBijective (f.toZModLinearMap 2) Function.bijective_id
  have hd := Atlas.G2.Natural.Normalizer.ambient_involution_displacement_ge
    S.field.Carrier ρ (inducedAutomizer V L) (layerEquiv D S c)
    E hres hρ
    (show 2 ≤ S.field.degree from S.nonbinary) S.field.card_eq a ha
  change 2 * S.field.degree ≤ Module.finrank (ZMod 2) ((ρ a - LinearMap.id).range) at hd
  rw [← fixedCodim_zpowers_eq_displacement_rank] at hd
  exact hd.trans (fixedCodim_le_of_equivariant_surjection
    (automizerRepresentation V) ρ (projectionLinear D S c)
    (projectionLinear_surjective D S c) he (zpowers a))

/-- The first fixed-codimension clause is unconditional on the chosen input,
for the full literal automizer and all three source markings. -/
theorem involution_lower (c : Coordinates D S.field) :
    letI := D.elementary
    ∀ a : Automizer V, orderOf a = 2 → naturalParameter D S c ≤
      fixedCodim (automizerRepresentation V) (zpowers a) := by
  cases c with
  | sl3 m => exact sl3_involution_lower D S m
  | sp4 m => exact sp4_involution_lower D S m
  | g2 m => exact g2_involution_lower D S m

/-- Application to the genuine local minimum. Only the still-required attaining
actor remains explicit; there is no full-automizer lower-bound premise. -/
theorem localM_of_attainment {c : Coordinates D S.field}
    (hattains : letI := D.elementary; ∃ a : Automizer V, orderOf a = 2 ∧
      fixedCodim (automizerRepresentation V) (zpowers a) = naturalParameter D S c) :
    @localM G _ V D.elementary = naturalParameter D S c := by
  let := D.elementary
  obtain ⟨a,ha,hca⟩ := hattains
  obtain ⟨b,hb,hcb⟩ := moduleM_attained (automizerRepresentation V) ⟨a,ha⟩
  exact le_antisymm ((moduleM_le_involution _ ha).trans_eq hca)
    ((involution_lower D S c b hb).trans_eq hcb)

/-- The remaining fixed-codimension work is exactly attainment and odd-prime
actors. The full-automizer lower bound and dimension require no extra premise.
The owning task must discharge both remaining calculations before source assembly. -/
theorem fixedCodimensions_of_attainment_and_odd {c : Coordinates D S.field}
    (hattains : letI := D.elementary; ∃ a : Automizer V, orderOf a = 2 ∧
      fixedCodim (automizerRepresentation V) (zpowers a) = naturalParameter D S c)
    (hodd : letI := D.elementary; ∀ p : ℕ, p.Prime → Odd p → ∀ a : Automizer V,
      orderOf a = p → 2 * naturalParameter D S c ≤
        fixedCodim (automizerRepresentation V) (zpowers a)) : FixedCodimensions D S c :=
  ⟨involution_lower D S c, hattains, hodd, NaturalDimensions.dimension D S c⟩

/-- The actual residual consumer now needs only the remaining attaining and
odd-prime calculations. Hyperplane geometry supplies hr in the owning parameter
assembly; the source residual is O^{2′} on both ambient centralizers. -/
theorem centralizer_control_of_attainment_and_odd {c : Coordinates D S.field}
    (hattains : letI := D.elementary; ∃ a : Automizer V, orderOf a = 2 ∧
      fixedCodim (automizerRepresentation V) (zpowers a) = naturalParameter D S c)
    (hodd : letI := D.elementary; ∀ p : ℕ, p.Prime → Odd p → ∀ a : Automizer V,
      orderOf a = p → 2 * naturalParameter D S c ≤
        fixedCodim (automizerRepresentation V) (zpowers a))
    (hE : Section06.HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hr : (naturalParameter D S c : ℕ∞) ≤ globalR V)
    {U : Subgroup G} (hUV : U ≤ V)
    (hk : subgroupCorank V U < 2 * naturalParameter D S c)
    (hres : Section06.oddCentralizerCondition (normalizer (L : Set G)) V U) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
      (primeToResidual 2 ↥(centralizer (U : Set G))).map
        (centralizer (U : Set G)).subtype ≤
          normalizer (L : Set G) ⊓ centralizer (V : Set G) :=
  centralizer_control D S (fixedCodimensions_of_attainment_and_odd D S hattains hodd)
    hE hr hUV hk hres

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
