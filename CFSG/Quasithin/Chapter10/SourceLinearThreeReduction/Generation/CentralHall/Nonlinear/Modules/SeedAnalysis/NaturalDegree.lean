module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.FullCubic
public import Theory.Representation.SL2.NaturalImageDegree

/-!
# Faithful natural actors bound the original moved module

The literal full component normalizer acts on W = [D.fullModule,L]. A natural
constituent identifies the component quotient with SL₂ and descends its
compatible automorphism action through the kernel on W. An elementary actor
faithful on that quotient, with codimension at most twice its rank, forces W
to have degree at most two natural copies. The previously proved two-copy
exclusion then reconstructs the original seed, including both orientations,
and applies to the literal central Hall exponent.

For the source Galois-field row this gives a contradiction. Consequently every
budget actor in the faithful image has a nontrivial kernel involution on the
marked component quotient. This identifies the unfaithful-actor branch; it
does not discharge it. Original source separation, constituent recognition
and the remaining D.3.9/D.3.21 branches stay with
qt-d-10-nona5-central-hall-orders, as does the final SeedAnalysisAt assembly.

Source: Aschbacher--Smith D.3.9(1), D.3.21(3), 3.2.6 and 10.2.3,
printed pp.199--207,581,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
private theorem component_le_stabilizer : L ≤ D.maximalLocal ⊓ normalizer (L : Set G) :=
  le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer
local instance : (movedStabilizerComponent D).Normal :=
  (normal_subgroupOf_iff_le_normalizer (component_le_stabilizer D)).mpr inf_le_right
variable {F : Type*} [Field F]

/-- Conjugation on the original component two-core quotient, in the fixed SL₂ marking. -/
@[expose] def movedNaturalQuotientAction (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    ↥(D.maximalLocal ⊓ normalizer (L : Set G)) →* MulAut (SL(2,F)) :=
  (MulAut.congr e).toMonoidHom.comp
    ((normalizerPCoreQuotientAction L).comp (inclusion inf_le_right))

/-- The fixed original quotient marking restricted to the stabilizer component. -/
@[expose] def movedNaturalComponentProjection (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    movedStabilizerComponent D →* SL(2,F) := e.toMonoidHom.comp
  ((QuotientGroup.mk' (pCore 2 L)).comp
    (subgroupOfEquivOfLe (by exact component_le_stabilizer D)).toMonoidHom)

/-- The component marking remains surjective after the subgroup-of transport. -/
theorem movedNaturalComponentProjection_surjective
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    Function.Surjective (movedNaturalComponentProjection D e) :=
  e.surjective.comp ((QuotientGroup.mk'_surjective _).comp
    (subgroupOfEquivOfLe (component_le_stabilizer D)).surjective)

/-- Normalizer conjugation respects the unchanged component quotient marking. -/
theorem movedNaturalComponentProjection_conj
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (n : ↥(D.maximalLocal ⊓ normalizer (L : Set G))) (l : movedStabilizerComponent D) :
    movedNaturalComponentProjection D e (MulAut.conjNormal n l) =
      movedNaturalQuotientAction D e n (movedNaturalComponentProjection D e l) := by
  change e (QuotientGroup.mk' (pCore 2 L) _) =
    e (normalizerPCoreQuotientAction L (inclusion inf_le_right n)
      (e.symm (e (QuotientGroup.mk' (pCore 2 L) _))))
  rw [e.symm_apply_apply]
  change _ = e (quotientAut (pCore 2 L) _ _)
  rw [quotientAut_apply_mk]
  rfl

variable [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

private theorem movedNaturalCoordinates
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (l : movedStabilizerComponent D) (v : Fin 2 → F) :
    E ((movedNaturalComponentProjection D e l).val.mulVec v) = I.toRepresentation l (E v) := by
  rw [←hE]
  congr 1
  exact (SL2AutomorphismNatural.action_conj _ _).symm

/-- The original component quotient action on the faithful image of W. -/
@[expose] def movedNaturalImageQuotientAction
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v)) :
    actionImage (movedStabilizerAction D) →* MulAut (SL(2,F)) :=
  SL2AutomorphismNatural.naturalImageQuotientAction (movedStabilizerAction D)
    (movedStabilizerComponent D) (movedNaturalComponentProjection D e)
    (movedNaturalComponentProjection_surjective D e) (movedNaturalQuotientAction D e)
    (movedNaturalComponentProjection_conj D e) I E (by exact movedNaturalCoordinates D e I E hE)

/-- The faithful-image action retains the original normalizer conjugation. -/
theorem movedNaturalImageQuotientAction_apply
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (g : ↥(D.maximalLocal ⊓ normalizer (L : Set G))) :
    movedNaturalImageQuotientAction D e I E hE (actionHom (movedStabilizerAction D) g) =
      movedNaturalQuotientAction D e g :=
  SL2AutomorphismNatural.naturalImageQuotientAction_apply (movedStabilizerAction D)
    (movedStabilizerComponent D) (movedNaturalComponentProjection D e)
    (movedNaturalComponentProjection_surjective D e) (movedNaturalQuotientAction D e)
    (movedNaturalComponentProjection_conj D e) I E (by exact movedNaturalCoordinates D e I E hE) g

/-- The actual elementary normalizer actor bounds the degree of the original W. -/
theorem moved_natural_degree_le_two_of_faithful_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (hF : 2 < Nat.card F)
    (A : Subgroup ↥(D.maximalLocal ⊓ normalizer (L : Set G)))
    (hA : IsElementaryTwo A)
    (hf : Function.Injective ((movedNaturalQuotientAction D e).comp A.subtype))
    (hb : fixedCodim (movedStabilizerAction D) A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) ≤
      2 * Module.finrank (ZMod 2) (Fin 2 → F) := by
  let := movedStabilizerAction_irreducible D c ht htn hsep
  exact SL2AutomorphismNatural.degree_le_two_of_faithful_actor (movedStabilizerAction D)
    (movedStabilizerComponent D) (movedNaturalComponentProjection D e)
    (movedNaturalComponentProjection_surjective D e) (movedNaturalQuotientAction D e)
    (movedNaturalComponentProjection_conj D e) I hI E (by exact movedNaturalCoordinates D e I E hE)
    hF A hA hf hb

/-- The faithful actor recovers all original seed clauses in either orientation. -/
theorem separatedSeed_of_natural_faithful_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (hF : 2 < Nat.card F)
    (A : Subgroup ↥(D.maximalLocal ⊓ normalizer (L : Set G)))
    (hA : IsElementaryTwo A)
    (hf : Function.Injective ((movedNaturalQuotientAction D e).comp A.subtype))
    (hb : fixedCodim (movedStabilizerAction D) A ≤ 2 * rank A) : SeparatedSeed D t :=
  separatedSeed_of_bounded_natural_constituent D c ht htn hsep e I hI E hE
    (moved_natural_degree_le_two_of_faithful_actor D c ht htn hsep e I hI E hE hF A hA hf hb)

/-- The reconstructed original seed feeds the literal Hall-exponent consumer. -/
theorem hall_exponent_of_natural_faithful_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (hF : 2 < Nat.card F)
    (A : Subgroup ↥(D.maximalLocal ⊓ normalizer (L : Set G)))
    (hA : IsElementaryTwo A)
    (hf : Function.Injective ((movedNaturalQuotientAction D e).comp A.subtype))
    (hb : fixedCodim (movedStabilizerAction D) A ≤ 2 * rank A)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1 :=
  hall_exponent_of_bounded_natural_constituent D c hnot ht htn hsep e I hI E hE
    (moved_natural_degree_le_two_of_faithful_actor D c ht htn hsep e I hI E hE hF A hA hf hb)

/-- The same degree bound applies directly to an actor in the faithful image. -/
theorem moved_natural_degree_le_two_of_faithful_image_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (hF : 2 < Nat.card F)
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : IsElementaryTwo A)
    (hf : Function.Injective ((movedNaturalImageQuotientAction D e I E hE).comp A.subtype))
    (hb : fixedCodim (imageRepresentation (movedStabilizerAction D)) A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) ≤
      2 * Module.finrank (ZMod 2) (Fin 2 → F) := by
  let := movedStabilizerAction_irreducible D c ht htn hsep
  exact SL2AutomorphismNatural.degree_le_two_of_faithful_image_actor (movedStabilizerAction D)
    (movedStabilizerComponent D) (movedNaturalComponentProjection D e)
    (movedNaturalComponentProjection_surjective D e) (movedNaturalQuotientAction D e)
    (movedNaturalComponentProjection_conj D e) I hI E (by exact movedNaturalCoordinates D e I E hE)
    hF A hA hf hb

/-- The faithful-image actor reconstructs the original seed without an elementary lift. -/
theorem separatedSeed_of_natural_faithful_image_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (hF : 2 < Nat.card F)
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : IsElementaryTwo A)
    (hf : Function.Injective ((movedNaturalImageQuotientAction D e I E hE).comp A.subtype))
    (hb : fixedCodim (imageRepresentation (movedStabilizerAction D)) A ≤ 2 * rank A) : SeparatedSeed D t :=
  separatedSeed_of_bounded_natural_constituent D c ht htn hsep e I hI E hE
    (moved_natural_degree_le_two_of_faithful_image_actor D c ht htn hsep e I hI E hE hF A hA hf hb)

/-- The image-actor degree bound supplies the literal central Hall exponent. -/
theorem hall_exponent_of_natural_faithful_image_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (hF : 2 < Nat.card F)
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : IsElementaryTwo A)
    (hf : Function.Injective ((movedNaturalImageQuotientAction D e I E hE).comp A.subtype))
    (hb : fixedCodim (imageRepresentation (movedStabilizerAction D)) A ≤ 2 * rank A)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1 :=
  hall_exponent_of_bounded_natural_constituent D c hnot ht htn hsep e I hI E hE
    (moved_natural_degree_le_two_of_faithful_image_actor D c ht htn hsep e I hI E hE hF A hA hf hb)

local instance naturalDegreeGaloisAlgebra (n : ℕ) :
    Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

omit [Field F] [Finite F] [CharP F 2] in
/-- A faithful budget actor is impossible in the source natural Galois-field row. -/
theorem no_natural_faithful_image_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : IsElementaryTwo A)
    (hf : Function.Injective ((movedNaturalImageQuotientAction D e I E hE).comp A.subtype))
    (hb : fixedCodim (imageRepresentation (movedStabilizerAction D)) A ≤ 2 * rank A) :
    False := by
  have hF : 2 < Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    simpa only [pow_one] using Nat.pow_lt_pow_right (by decide : 1 < 2) hn
  exact no_bounded_natural_constituent D c ht htn hsep n hn e I hI E hE
    (moved_natural_degree_le_two_of_faithful_image_actor D c ht htn hsep e I hI E hE hF A hA hf hb)

omit [Field F] [Finite F] [CharP F 2] in
/-- Every natural budget actor contains an involution centralizing the marked quotient. -/
theorem natural_budget_actor_has_quotient_kernel_involution
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : IsElementaryTwo A)
    (hb : fixedCodim (imageRepresentation (movedStabilizerAction D)) A ≤ 2 * rank A) :
    ∃ a : actionImage (movedStabilizerAction D), a ∈ A ∧ a ≠ 1 ∧ a ^ 2 = 1 ∧
      movedNaturalImageQuotientAction D e I E hE a = 1 := by
  classical
  by_contra! hnone
  apply no_natural_faithful_image_actor D c ht htn hsep n hn e I hI E hE A hA _ hb
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  apply Subtype.ext
  by_contra hne
  let : IsElementaryAbelian 2 A := hA.2
  exact hnone a.val a.property hne
    (elemPow_eq_one_of_isElementaryAbelian a.val a.property) ha

omit [Field F] [Finite F] [CharP F 2] in
/-- The genuine cubic bound supplies an actor with a nontrivial quotient-kernel involution. -/
theorem natural_cubic_actor_has_quotient_kernel_involution
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (hc : cubicRatio (imageRepresentation (movedStabilizerAction D)) ≤ 2) :
    ∃ A : Subgroup (actionImage (movedStabilizerAction D)), IsElementaryTwo A ∧
      IsCubic (imageRepresentation (movedStabilizerAction D)) A ∧
      fixedCodim (imageRepresentation (movedStabilizerAction D)) A ≤ 2 * rank A ∧
      ∃ a : actionImage (movedStabilizerAction D), a ∈ A ∧ a ≠ 1 ∧ a ^ 2 = 1 ∧
        movedNaturalImageQuotientAction D e I E hE a = 1 := by
  obtain ⟨A,hA,hcub,hb⟩ := (cubicRatio_le_nat_iff _ 2).mp hc
  exact ⟨A,hA,hcub,hb,natural_budget_actor_has_quotient_kernel_involution
    D c ht htn hsep n hn e I hI E hE A hA hb⟩

omit [Field F] [Finite F] [CharP F 2] in
/-- The original full-module cubic bound forces a nonfaithful actor in the
separated natural branch. No new cubic-bound premise is imposed. -/
theorem source_natural_actor_has_quotient_kernel_involution
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    :
    ∃ A : Subgroup (actionImage (movedStabilizerAction D)), IsElementaryTwo A ∧
      IsCubic (imageRepresentation (movedStabilizerAction D)) A ∧
      fixedCodim (imageRepresentation (movedStabilizerAction D)) A ≤ 2 * rank A ∧
      ∃ a : actionImage (movedStabilizerAction D), a ∈ A ∧ a ≠ 1 ∧ a ^ 2 = 1 ∧
        movedNaturalImageQuotientAction D e I E hE a = 1 := by
  obtain ⟨A,hA,hcub,hb⟩ := (cubicRatio_le_nat_iff _ 2).mp
    (movedStabilizerAction_cubic_bound D c ht htn hsep)
  exact ⟨A,hA,hcub,hb,natural_budget_actor_has_quotient_kernel_involution
    D c ht htn hsep n hn e I hI E hE A hA hb⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
