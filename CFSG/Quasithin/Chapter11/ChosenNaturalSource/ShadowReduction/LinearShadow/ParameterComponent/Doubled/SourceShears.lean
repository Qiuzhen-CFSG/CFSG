module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Shears
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Moved
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.SourceRecognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.SourceMovingCover

/-!
# Reciprocal shears exclude the rank-one natural quotient

The doubled reciprocal action supplies the maximal Sylow displacement dimension
and equal nonzero individual commutator planes. The literal star projection
identifies the actors and its kernel is the centralizer of the original omega
orbit. Thus the previously constructed nonsplit orthogonal coordinates give a
contradiction without assuming any commutator conclusion.

Source: Aschbacher--Smith, 11.3.6, printed pp.772--773.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
open CommonCore
variable {G : Type*} [Group G] {T : Sylow 2 G} {H B : Subgroup G}
    {F K : Type*} [Field F] [Field K]

/-- The matrix parameter uses exactly the source star projection. -/
def sourceParameter (e : residualStar T H ≃* SL(2,K)) (hBH : B ≤ H)
    (hBK : (B.subgroupOf H).map (starProjection T H) ≤ residualStar T H) :
    B →* SL(2,K) :=
  e.toMonoidHom.comp (((starProjection T H).comp (inclusion hBH)).codRestrict _
    (fun b => hBK (mem_map_of_mem (starProjection T H) b.property)))

theorem sourceParameter_eq_one (e : residualStar T H ≃* SL(2,K)) (hBH : B ≤ H)
    (hBK : (B.subgroupOf H).map (starProjection T H) ≤ residualStar T H) (b : B) :
    sourceParameter e hBH hBK b = 1 ↔
      (b : G) ∈ centralizer (omegaClosure T H : Set G) := by
  change e _ = 1 ↔ _
  rw [map_eq_one_iff e e.injective,Subtype.ext_iff]
  change starProjection T H (inclusion hBH b) = 1 ↔ _
  exact QuotientGroup.eq_one_iff _

/-- The selected source Sylow equality gives surjectivity onto its matrix Sylow. -/
theorem sourceParameter_range [Finite G] (e : residualStar T H ≃* SL(2,K)) (hBH : B ≤ H)
    (hBK : (B.subgroupOf H).map (starProjection T H) ≤ residualStar T H)
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (B.subgroupOf H).map (starProjection T H)) :
    (sourceParameter e hBH hBK).range =
      (R.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup SL(2,K)) := by
  let φ := ((starProjection T H).comp (inclusion hBH)).codRestrict _
    (fun b => hBK (mem_map_of_mem (starProjection T H) b.property))
  have hφ : φ.range = R := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      have hb : starProjection T H (inclusion hBH b) ∈
          (R : Subgroup (residualStar T H)).map (residualStar T H).subtype := by
        rw [hR]
        exact mem_map_of_mem _ b.property
      obtain ⟨r,hr,he⟩ := hb
      exact (Subtype.ext he : r = φ b) ▸ hr
    · intro hx
      have hh : (x : Star T H) ∈ (B.subgroupOf H).map (starProjection T H) := by
        rw [← hR]
        exact mem_map_of_mem _ hx
      obtain ⟨b,hb,he⟩ := hh
      exact ⟨⟨b,hb⟩,Subtype.ext he⟩
  change (e.toMonoidHom.comp φ).range = _
  rw [MonoidHom.range_comp,hφ]
  rfl

variable [Finite G] [IsElementaryAbelian 2 (omegaClosure T H)]
  [Finite F] [CharP F 2] [Finite K] [CharP K 2]

omit [CharP F 2] [Finite K] [CharP K 2] in
/-- The 4n-dimensional reciprocal commutator is the actual Sylow displacement
span on V_H, through the literal star projection. -/
theorem source_shear_moved_dimension
    (d : ShearCoordinates (omegaClosure T H) B F)
    (e : residualStar T H ≃* SL(2,K)) (hBH : B ≤ H)
    (hBK : (B.subgroupOf H).map (starProjection T H) ≤ residualStar T H)
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (B.subgroupOf H).map (starProjection T H))
    (n : ℕ) (hF : Nat.card F = 2^n) :
    Module.finrank (ZMod 2) (Coinvariants.ker
      ((NaturalRecognition.binaryAction T H e).comp
        (R.mapSurjective (f := e.toMonoidHom) e.surjective).toSubgroup.subtype)) = 4*n := by
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let σ := sourceParameter e hBH hBK
  have hσ : σ.range = P := sourceParameter_range e hBH hBK R hR
  let f : B →* P := σ.codRestrict _ (fun b => hσ ▸ (show σ b ∈ σ.range from ⟨b,rfl⟩))
  have hf : Function.Surjective f := by
    intro p
    have hp : p.val ∈ σ.range := hσ.symm ▸ p.property
    obtain ⟨b,hb⟩ := hp
    exact ⟨b,Subtype.ext hb⟩
  have he : ∀ b : B, ∀ w : omegaClosure T H,
      (((NaturalRecognition.binaryAction T H e).comp P.toSubgroup.subtype)
        (f b) (Additive.ofMul w)).toMul =
      (omegaClosure T H).normalizerMonoidHom
        (inclusion (hBH.trans (omegaClosure_normalized T H)) b) w := by
    intro b w
    exact NaturalRecognition.binaryAction_equiv T H e _ _
  have hc := coinvariants_card_of_conjugation
    (hBH.trans (omegaClosure_normalized T H)) _ f hf he
  rw [commutator_comm B, d.commutator_card n hF] at hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc

omit [IsElementaryAbelian 2 (omegaClosure T H)] in
/-- The two equal commutator planes contradict orthogonal coordinates. Their
nonzero, distinct Sylow parameters follow from the source centralizer kernel. -/
theorem source_shear_orthogonal_contradiction
    (d : ShearCoordinates (omegaClosure T H) B F)
    (e : residualStar T H ≃* SL(2,K)) (hBH : B ≤ H)
    (hBK : (B.subgroupOf H).map (starProjection T H) ≤ residualStar T H)
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (B.subgroupOf H).map (starProjection T H))
    (hF : 2 < Nat.card F)
    (c : OrthogonalMarking T H B K)
    (hc : ∀ b, c.parameter b = sourceParameter e hBH hBK b) : False := by
  obtain ⟨u,hu0,hu1⟩ := ENat.exists_ne_ne_of_three_le
    (α := F) (by rw [ENat.card_eq_coe_natCard]; exact_mod_cast hF) 0 1
  let a := d.axisElement 1
  let b := d.axisElement u
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP (v : B) : c.parameter v ∈ P := by
    rw [hc]
    change sourceParameter e hBH hBK v ∈
      (R.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup SL(2,K))
    rw [← sourceParameter_range e hBH hBK R hR]
    exact ⟨v,rfl⟩
  have h1 (t : F) (ht : t ≠ 0) : c.parameter (d.axisElement t) ≠ 1 := by
    rw [hc]
    exact fun he => d.axis_not_central t ht ((sourceParameter_eq_one e hBH hBK _).mp he)
  have hab : c.parameter a ≠ c.parameter b := by
    intro he
    have hz : sourceParameter e hBH hBK (a*b⁻¹) = 1 := by
      rw [map_mul,map_inv,← hc,← hc,he,mul_inv_cancel]
    exact d.axis_quotient_not_central 1 u (Ne.symm hu1)
      ((sourceParameter_eq_one e hBH hBK _).mp hz)
  apply c.false_of_equal_commutators P a b (d.element_square a) (d.element_square b)
    (hP a) (hP b) (h1 1 one_ne_zero) (h1 u hu0) hab
  · rw [d.axis_commutator 1 one_ne_zero,d.axis_commutator u hu0]
  · rw [d.axis_commutator 1 one_ne_zero]
    exact d.axisPlane_ne_bot

/-- At degree 2n, reciprocal doubled shears rule out the single natural
quotient. The maximal moved dimension and the nonsplit contradiction are
proved here rather than retained as source assumptions. -/
theorem source_shear_quotient_contradiction
    (d : ShearCoordinates (omegaClosure T H) B F)
    (e : residualStar T H ≃* SL(2,K)) (hBH : B ≤ H)
    (hBK : (B.subgroupOf H).map (starProjection T H) ≤ residualStar T H)
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (B.subgroupOf H).map (starProjection T H))
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n) (hK : Nat.card K = 2^(2*n))
    (hP : SL2SylowFixedRecognition.FixedSpaceHypotheses
      (NaturalRecognition.binaryAction T H e)
      (R.mapSurjective (f := e.toMonoidHom) e.surjective))
    (c : SL2SylowFixedRecognition.QuotientCoordinates
      (NaturalRecognition.binaryAction T H e)) (hc : c.multiplicity = 1) : False := by
  have hmove := source_shear_moved_dimension d e hBH hBK R hR n hF
  have he : 4*n = 2*(2*n) := by omega
  rw [he] at hmove
  obtain ⟨m,hm⟩ := source_orthogonalMarking_of_coordinates e hBH hBK (2*n)
    (by omega) hK _ hP c hc hmove
  apply source_shear_orthogonal_contradiction d e hBH hBK R hR ?_ m hm
  rw [hF]
  calc
    2 < 2^2 := by decide
    _ ≤ 2^n := Nat.pow_le_pow_right (by decide) hn

variable {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Conditional assembly on the original chosen source: the doubled geometry
and reciprocal shear coordinates are the remaining local source obligations.
Rank-one recognition is the independent earlier-source input. -/
theorem source_contradiction_of_reciprocal_shears
    (s : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (d : Coordinates D S) (z : Geometry d H) (r : RankOneReduction S H)
    (hu : ChapterE.generationParameter H ≤ 2 * S.field.degree)
    (hK : Nat.card K = 2 ^ (2 * S.field.degree))
    (hrec : ∀ g : G,
      (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ T →
      ¬ (fullModule L V).map (MulAut.conj g).toMonoidHom ≤
        centralizer (omegaClosure T H : Set G) →
      Nonempty (ShearCoordinates (omegaClosure T H)
        ((fullModule L V).map (MulAut.conj g).toMonoidHom) S.field.Carrier)) : False := by
  obtain ⟨e,R,g,hg,ha,hR,hP,hm⟩ := source_recognition_inputs s p hc d z r hu hK
  obtain ⟨c⟩ := SL2SylowFixedRecognition.quotientCoordinates_of_fixedSpaceHypotheses
    (NaturalRecognition.binaryAction T H e)
    (R.mapSurjective (f := e.toMonoidHom) e.surjective) hP
    (2 * S.field.degree) (by have := S.nonbinary; omega) hK
  have hBK : ((((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map
      (starProjection T H)) ≤ residualStar T H := by
    rw [← hR]
    exact map_subtype_le _
  obtain ⟨ds⟩ := hrec g hg ha
  exact source_shear_quotient_contradiction ds e (hg.trans s.outside.1.1.2) hBK R hR
    S.field.degree S.nonbinary S.field.card_eq hK hP c (hm c)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
