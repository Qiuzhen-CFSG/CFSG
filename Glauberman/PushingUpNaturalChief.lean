module
public import Glauberman.PushingUpActionRecognition
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual
public import Theory.GroupTheory.NoncentralChiefRefinement.BinaryFlagSections
public import Theory.GroupTheory.NoncentralChiefRefinement.UniqueFactor
/-!
# The actual natural chief factor in the original Niles group

Write V = Ω₁(Z(O₂(H))) and Z = V ∩ Z(H). The original conjugation action's
natural global-fixed quotient gives equivariant coordinates on the literal
group section V/Z. Transitivity of SL₂(4) on nonzero natural vectors proves
irreducibility, so Z < V is an ambient chief interval; it is noncentral and
has order sixteen. All central fixed attachments are retained in Z.

Given any chief series on O₂(H) with exactly one noncentral factor, insert
Z < V into another series and use equivariant Jordan–Hölder to identify the
unique factor. Both one-copy representation coordinates and direct group
coordinates preserve the original quotient map q. The final source consumer
constructs q and its coordinates from the proved original action recognition;
only the independently established count-one conclusion is needed to identify
a factor of a supplied series.

Source: Niles, “Pushing-up in finite groups” (1979), Theorem B, printed p.28,
and Lemma 2.9, printed p.33. The Sylow class/exponent and noncentral count are
separate source branches, not assertions of this module.
-/

set_option backward.isDefEq.respectTransparency false
public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender NoncentralChiefRefinement
open SL2FourNatural
namespace Glauberman
variable {H : Type*} [Group H]
local instance omega_normal : (omegaCenterIn (pCore 2 H)).Normal :=
  omegaCenterIn_normal_of_normal (pCore 2 H)

/-- The original central omega subgroup as an ambient-normal node. -/
abbrev omegaNode (H : Type*) [Group H] : NormalNode H :=
  ⟨omegaCenterIn (pCore 2 H), omegaCenterIn_normal_of_normal (pCore 2 H)⟩

/-- Precisely the globally central vectors in the original omega subgroup. -/
abbrev centralOmegaNode (H : Type*) [Group H] : NormalNode H :=
  omegaNode H ⊓ ⟨center H, inferInstanceAs (center H).Normal⟩

private theorem natural_pullback_irreducible (q : H →* SL) (hq : Function.Surjective q) :
    IsIrreducible (naturalRepresentation.comp q) := by
  apply BorelFactors.irreducible_of_transitive
  intro v w hv hw
  obtain ⟨g, hg⟩ := transitive_nonzero v w hv hw
  obtain ⟨h, rfl⟩ := hq g
  exact ⟨h, hg⟩

private theorem natural_pullback_nontrivial (q : H →* SL) (hq : Function.Surjective q) :
    ∃ h v, (naturalRepresentation.comp q) h v ≠ v := by
  obtain ⟨h, hh⟩ := hq (upper 1)
  refine ⟨h, ![0, 1], ?_⟩
  intro he
  have hv := congrFun he 0
  change action (q h) ![0, 1] 0 = 0 at hv
  rw [hh, upper_action] at hv
  simp at hv

variable (q : H →* SL)
  (E : (Additive (omegaCenterIn (pCore 2 H)) ⧸ fixedSpace (omegaAction H) ⊤) ≃ₗ[ZMod 2] V)
  (hE : ∀ h v, E (fixedQuotient (omegaAction H) ⊤ h v) = specialLinearNatural 2 (q h) (E v))

include q E hE

private noncomputable def naturalChiefMap : BinaryFlag.Map (omegaNode H) (naturalRepresentation.comp q) where
  hom := (E.toLinearMap.comp (fixedSpace (omegaAction H) ⊤).mkQ).toAddMonoidHom.toMultiplicativeRight
  equivariant h b := by
    change E ((fixedSpace (omegaAction H) ⊤).mkQ (Additive.ofMul (MulAut.conjNormal h b))) =
      specialLinearNatural 2 (q h) (E ((fixedSpace (omegaAction H) ⊤).mkQ (Additive.ofMul b)))
    have hc : Additive.ofMul (MulAut.conjNormal h b) = omegaAction H h (Additive.ofMul b) := by
      let _ := omegaCenterIn_normal_of_normal (pCore 2 H)
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (omegaAction_apply H h (Additive.ofMul b)).symm
    rw [hc]
    exact hE h ((fixedSpace (omegaAction H) ⊤).mkQ (Additive.ofMul b))

private theorem naturalChiefMap_surjective : Function.Surjective (naturalChiefMap q E hE).hom := by
  intro v
  obtain ⟨x, hx⟩ := E.surjective v.toAdd
  obtain ⟨b, rfl⟩ := (fixedSpace (omegaAction H) ⊤).mkQ_surjective x
  exact ⟨b.toMul, congrArg Multiplicative.ofAdd hx⟩

private theorem naturalChiefMap_kernel :
    (naturalChiefMap q E hE).hom.ker = (centralOmegaNode H).val.subgroupOf (omegaNode H).val := by
  ext b
  change E ((fixedSpace (omegaAction H) ⊤).mkQ (Additive.ofMul b)) = 0 ↔
    (b : H) ∈ omegaCenterIn (pCore 2 H) ⊓ center H
  rw [E.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hh : Additive.ofMul b ∈ fixedSpace (omegaAction H) ⊤ ↔ (b : H) ∈ center H := by
    let _ := omegaCenterIn_normal_of_normal (pCore 2 H)
    have hv := omegaAction_fixedSpace H ⊤ (Additive.ofMul b)
    rw [coe_top, centralizer_univ] at hv
    exact hv
  exact hh.trans (and_iff_right b.property).symm

/-- One-copy natural coordinates for the literal central omega chief quotient. -/
noncomputable def naturalChiefCoordinates :
    SectionCoordinates (centralOmegaNode H) (omegaNode H) (naturalRepresentation.comp q) 1 :=
  (naturalChiefMap q E hE).coordinates (naturalChiefMap_surjective q E hE)
    (naturalChiefMap_kernel q E hE)

/-- The original globally central omega quotient is an actual noncentral chief interval. -/
theorem omega_natural_chief (hq : Function.Surjective q) :
    centralOmegaNode H ⋖ omegaNode H ∧ ¬ IsCentral (centralOmegaNode H) (omegaNode H) := by
  let _ := natural_pullback_irreducible q hq
  have hn := natural_pullback_nontrivial q hq
  exact ⟨(naturalChiefCoordinates q E hE).covBy inf_le_left hn,
    (naturalChiefCoordinates q E hE).not_isCentral (by decide) hn⟩

/-- Direct coordinates on the original multiplicative quotient. -/
noncomputable def naturalChiefEquiv :
    Section (centralOmegaNode H) (omegaNode H) ≃* Multiplicative V :=
  (naturalChiefCoordinates q E hE).equiv.trans BinaryFlag.Map.oneCopy.symm

theorem naturalChiefEquiv_equivariant (h : H) (x : Section (centralOmegaNode H) (omegaNode H)) :
    (naturalChiefEquiv q E hE (sectionAction (centralOmegaNode H) (omegaNode H) h x)).toAdd =
      specialLinearNatural 2 (q h) (naturalChiefEquiv q E hE x).toAdd :=
  (naturalChiefCoordinates q E hE).equivariant h x 0

theorem naturalChief_card : Nat.card (Section (centralOmegaNode H) (omegaNode H)) = 16 := by
  rw [Nat.card_congr (naturalChiefEquiv q E hE).toEquiv]
  change Nat.card V = 16
  rw [Nat.card_eq_fintype_card, SL2FourNatural.card_vector]


/-- Every noncentral interval in a count-one series is equivariantly the actual
central omega chief interval, with the original natural action marking. -/
theorem unique_omega_natural_factor [Finite H] (hq : Function.Surjective q)
    (s : SeriesOn (pCore 2 H)) (hs : s.noncentralCount = 1)
    (i : Fin s.series.length) (hi : ¬ s.Central i) :
    Nonempty (SectionEquiv (s.lower i) (s.upper i) (centralOmegaNode H) (omegaNode H)) ∧
    Nonempty (SectionCoordinates (s.lower i) (s.upper i) (naturalRepresentation.comp q) 1) ∧
    ∃ f : s.Factor i ≃* Multiplicative V,
      ∀ h x, (f (s.action i h x)).toAdd = specialLinearNatural 2 (q h) (f x).toAdd := by
  have hc := omega_natural_chief q E hE hq
  obtain ⟨e⟩ := s.sectionEquiv_of_count_one hs (centralOmegaNode H) (omegaNode H) hc.1
    (fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).1) hc.2 i hi
  refine ⟨⟨e⟩, ⟨(naturalChiefCoordinates q E hE).transport e⟩,
    e.equiv.trans (naturalChiefEquiv q E hE), ?_⟩
  intro h x
  change (naturalChiefEquiv q E hE (e.equiv (sectionAction (s.lower i) (s.upper i) h x))).toAdd = _
  rw [e.equivariant]
  exact naturalChiefEquiv_equivariant q E hE h (e.equiv x)


omit q E hE in
/-- Niles Theorem B's natural-factor identification from the original source
hypotheses. The independent count-one conclusion identifies every noncentral
factor of any specified chief series, preserving the original H action. -/
theorem original_psl2_four_natural_chief_data [Finite H]
    {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H)) :
    ∃ q : H →* SL, Function.Surjective q ∧
      q.ker = centralizer (omegaCenterIn (pCore 2 H) : Set H) ∧
      centralOmegaNode H ⋖ omegaNode H ∧
      ¬ IsCentral (centralOmegaNode H) (omegaNode H) ∧
      Nat.card (Section (centralOmegaNode H) (omegaNode H)) = 16 ∧
      (∃ f : Section (centralOmegaNode H) (omegaNode H) ≃* Multiplicative V,
        ∀ h x, (f (sectionAction (centralOmegaNode H) (omegaNode H) h x)).toAdd =
          specialLinearNatural 2 (q h) (f x).toAdd) ∧
      ∀ (s : SeriesOn (pCore 2 H)), s.noncentralCount = 1 →
        ∀ i : Fin s.series.length, ¬ s.Central i →
          Nonempty (SectionEquiv (s.lower i) (s.upper i) (centralOmegaNode H) (omegaNode H)) ∧
          Nonempty (SectionCoordinates (s.lower i) (s.upper i) (naturalRepresentation.comp q) 1) ∧
          ∃ f : s.Factor i ≃* Multiplicative V,
            ∀ h x, (f (s.action i h x)).toAdd = specialLinearNatural 2 (q h) (f x).toAdd := by
  obtain ⟨q, hq, hk, _, _, _, E, hE⟩ :=
    original_psl2_four_omegaAction_recognition hF S hu K e hf hno
  have hc := omega_natural_chief q E hE hq
  exact ⟨q, hq, hk, hc.1, hc.2, naturalChief_card q E hE,
    ⟨naturalChiefEquiv q E hE, naturalChiefEquiv_equivariant q E hE⟩,
    fun s hs i hi => unique_omega_natural_factor q E hE hq s hs i hi⟩

end Glauberman
