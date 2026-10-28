module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalDegree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.OriginalSuzuki
public import CFSG.Quasithin.ChapterD.Section03.HermitianMultiplicity

/-!
# Hermitian multiplicity and the original central Hall subgroup

The original component quotient marks a Hermitian constituent of the literal
moved subgroup W=[D.fullModule,L]. Its full component stabilizer acts
irreducibly, and conjugation on the marked quotient descends to the faithful
image. For fixed-field degree s>1, the Hermitian non-FF and two-section budget
force L-irreducibility whenever the specified image actor is faithful on that
quotient. This proves moved minimality and reconstructs all original seed
clauses in both separated orientations, then gives the literal Hall exponent.

The original cubic bound supplies an image actor: either it completes the
Hall branch or it has a nontrivial involution in the marked quotient-action
kernel. Source separation, constituent construction and exclusion of that
kernel branch remain with qt-d-10-nona5-central-hall-orders, together with the
ambient natural-tensor exclusion and final source assembly.

Source: Aschbacher--Smith D.3.9(1), D.3.21, 3.2.6 and 10.2.3,
printed pp.199--207,581,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 Representation.BinaryOffender
open Representation.OrthogonalFourMinus.FiniteModel
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
private theorem component_le_stabilizer : L ≤ D.maximalLocal ⊓ normalizer (L : Set G) :=
  le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer
local instance : (movedStabilizerComponent D).Normal :=
  (normal_subgroupOf_iff_le_normalizer (component_le_stabilizer D)).mpr inf_le_right
variable (s : ℕ) [NeZero s]
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- The original component quotient action descended through the literal moved image. -/
@[expose] def movedHermitianImageQuotientAction
    (e : (L ⧸ pCore 2 L) ≃* SL(2,Field s))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (SL2.BinarySmall.hermitian s (movedNaturalComponentProjection D e l) v) =
        I.toRepresentation l (E v)) :
    actionImage (movedStabilizerAction D) →* MulAut SL(2,Field s) :=
  SL2Hermitian.hermitianImageQuotientAction s (movedStabilizerAction D)
    (movedStabilizerComponent D) (movedNaturalComponentProjection D e)
    (movedNaturalComponentProjection_surjective D e) (movedNaturalQuotientAction D e)
    (movedNaturalComponentProjection_conj D e) I E hE

/-- The descended action retains the given original quotient marking. -/
theorem movedHermitianImageQuotientAction_apply
    (e : (L ⧸ pCore 2 L) ≃* SL(2,Field s))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (SL2.BinarySmall.hermitian s (movedNaturalComponentProjection D e l) v) =
        I.toRepresentation l (E v))
    (g : ↥(D.maximalLocal ⊓ normalizer (L : Set G))) :
    movedHermitianImageQuotientAction D s e I E hE (actionHom (movedStabilizerAction D) g) =
      movedNaturalQuotientAction D e g :=
  SL2Hermitian.hermitianImageQuotientAction_apply s (movedStabilizerAction D)
    (movedStabilizerComponent D) (movedNaturalComponentProjection D e)
    (movedNaturalComponentProjection_surjective D e) (movedNaturalQuotientAction D e)
    (movedNaturalComponentProjection_conj D e) I E hE g

/-- The full stabilizer and the original marked quotient give irreducibility on L. -/
theorem moved_hermitian_irreducible_of_faithful_image_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) (hs : 1 < s)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,Field s))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (SL2.BinarySmall.hermitian s (movedNaturalComponentProjection D e l) v) =
        I.toRepresentation l (E v))
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : IsElementaryTwo A)
    (hf : Function.Injective ((movedHermitianImageQuotientAction D s e I E hE).comp A.subtype))
    (hb : fixedCodim (imageRepresentation (movedStabilizerAction D)) A ≤ 2 * rank A) :
    IsIrreducible ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype) := by
  let : (movedStabilizerAction D).IsIrreducible :=
    movedStabilizerAction_irreducible D c ht htn hsep
  let := D.quasisimple
  let : IsQuasisimple SL(2,Field s) := IsQuasisimple.of_mulEquiv e
  exact ChapterD.hermitian_irreducible_of_faithful_image_actor s
    (IsSQTK.knownSimple_of_equiv e (original_component_quotient_sqtk D)) hs
    (movedStabilizerAction D) (movedStabilizerComponent D)
    (movedNaturalComponentProjection D e) (movedNaturalComponentProjection_surjective D e)
    (movedNaturalQuotientAction D e) (movedNaturalComponentProjection_conj D e)
    I hI E hE A hA hf hb

/-- Eliminate every proper noncentral L-submodule of the unchanged moved subgroup. -/
theorem movedMinimal_of_hermitian_faithful_image_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) (hs : 1 < s)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,Field s))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (SL2.BinarySmall.hermitian s (movedNaturalComponentProjection D e l) v) =
        I.toRepresentation l (E v))
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : IsElementaryTwo A)
    (hf : Function.Injective ((movedHermitianImageQuotientAction D s e I E hE).comp A.subtype))
    (hb : fixedCodim (imageRepresentation (movedStabilizerAction D)) A ≤ 2 * rank A) : MovedMinimal D := by
  let σ := (movedStabilizerAction D).comp (movedStabilizerComponent D).subtype
  let : IsIrreducible σ :=
    moved_hermitian_irreducible_of_faithful_image_actor D s c ht htn hsep hs e I hI E hE A hA hf hb
  intro J hJW hLJ
  let W := ⁅D.fullModule,L⁆
  let P : Subrepresentation σ := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 (J.subgroupOf W).toAddSubgroup
    apply_mem_toSubmodule l w hw := by
      exact (mem_normalizer_iff.mp (hLJ l.property) w.toMul.val).mp hw }
  rcases eq_bot_or_eq_top P with hbot | htop
  · right
    intro w hw
    have hp : Additive.ofMul (⟨w,hJW hw⟩ : W) ∈ P.toSubmodule := hw
    rw [hbot] at hp
    have hz : w = 1 := congrArg (fun v : Additive W => (v.toMul : G))
      (show Additive.ofMul (⟨w,hJW hw⟩ : W) = 0 from hp)
    exact hz ▸ (centralizer (L : Set G)).one_mem
  · left
    apply le_antisymm hJW
    intro w hw
    have hp : Additive.ofMul (⟨w,hw⟩ : W) ∈ P.toSubmodule := by rw [htop]; trivial
    exact hp

/-- Recover full/local equality and Sylow stability in either original orientation. -/
theorem separatedSeed_of_hermitian_faithful_image_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) (hs : 1 < s)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,Field s))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (SL2.BinarySmall.hermitian s (movedNaturalComponentProjection D e l) v) =
        I.toRepresentation l (E v))
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : IsElementaryTwo A)
    (hf : Function.Injective ((movedHermitianImageQuotientAction D s e I E hE).comp A.subtype))
    (hb : fixedCodim (imageRepresentation (movedStabilizerAction D)) A ≤ 2 * rank A) : SeparatedSeed D t :=
  separatedSeed_of_separated_and_movedMinimal D
    (movedMinimal_of_hermitian_faithful_image_actor D s c ht htn hsep hs e I hI E hE A hA hf hb)
    ht htn hsep

/-- Apply the constructed moved minimality to the literal original Hall subgroup. -/
theorem hall_exponent_of_hermitian_faithful_image_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) (hs : 1 < s)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,Field s))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (SL2.BinarySmall.hermitian s (movedNaturalComponentProjection D e l) v) =
        I.toRepresentation l (E v))
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : IsElementaryTwo A)
    (hf : Function.Injective ((movedHermitianImageQuotientAction D s e I E hE).comp A.subtype))
    (hb : fixedCodim (imageRepresentation (movedStabilizerAction D)) A ≤ 2 * rank A) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1 :=
  hall_exponent_of_moved_minimal_and_crossed T D c hnot ht htn
    (movedMinimal_of_hermitian_faithful_image_actor D s c ht htn hsep hs e I hI E hE A hA hf hb)
    (full_moved_centralizes_opposite_of_seed_separated D ht htn hsep)

/-- The original cubic bound either completes this Hermitian Hall branch or
supplies an actual involution in the marked component-action kernel. The
remaining kernel branch and source constituent construction stay with this owner. -/
theorem hall_exponent_or_hermitian_actor_kernel
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) (hs : 1 < s)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,Field s))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : Space s ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (SL2.BinarySmall.hermitian s (movedNaturalComponentProjection D e l) v) =
        I.toRepresentation l (E v))
    :
    (∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1) ∨
    ∃ A : Subgroup (actionImage (movedStabilizerAction D)), IsElementaryTwo A ∧
      IsCubic (imageRepresentation (movedStabilizerAction D)) A ∧
      fixedCodim (imageRepresentation (movedStabilizerAction D)) A ≤ 2 * rank A ∧
      ∃ a : actionImage (movedStabilizerAction D), a ∈ A ∧ a ≠ 1 ∧ a ^ 2 = 1 ∧
        movedHermitianImageQuotientAction D s e I E hE a = 1 := by
  classical
  obtain ⟨A,hA,hcub,hb⟩ := (cubicRatio_le_nat_iff _ 2).mp
    (movedStabilizerAction_cubic_bound D c ht htn hsep)
  by_cases hf : Function.Injective ((movedHermitianImageQuotientAction D s e I E hE).comp A.subtype)
  · exact Or.inl (hall_exponent_of_hermitian_faithful_image_actor
      D s c hnot ht htn hsep hs e I hI E hE A hA hf hb)
  · right
    refine ⟨A,hA,hcub,hb,?_⟩
    by_contra! hnone
    apply hf
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    apply Subtype.ext
    by_contra hne
    let : IsElementaryAbelian 2 A := hA.2
    exact hnone a.val a.property hne
      (elemPow_eq_one_of_isElementaryAbelian a.val a.property) ha
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
