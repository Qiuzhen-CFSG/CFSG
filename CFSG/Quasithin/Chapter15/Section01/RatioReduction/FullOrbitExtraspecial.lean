module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitSingletonCyclic
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ExtraspecialImage
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.ExtraspecialResidual

/-!
# The original extraspecial full-orbit residual

The extraspecial endpoint on the original normal actor Jhat gives a
characteristic odd kernel. Its image in the original action image is the
actual two-residual, by the faithful degree-six residual theorem and the
three-rank bound on the selected local group M.

The actual image-to-centralizer-quotient transport then consumes the source
Sylow irreducibility theorem. Thus the resulting residual has order27,
exponent three and irreducible Frattini quotient under the original Sylow
image, on the original binary six-space.

Source: Aschbacher--Smith 15.1.2, printed p.1086, case (4).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The literal extraspecial kernel supplied by the singleton cyclic endpoint
is the original local action image's two-residual. -/
theorem source_localAction_extraspecial_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ l : CyclicSource.LocalGeneration (ρ.comp (Jhat ρ).subtype),
      letI := BinaryGroupAction.action (ρ.comp (Jhat ρ).subtype)
      letI : Finite (Additive V) := Module.finite_of_finite (ZMod 2)
      letI : IsElementaryAbelian 2 (Multiplicative (Additive V)) := BinaryGroupAction.elementary
      letI := l.normal
      ChapterD.Section02.ExtraspecialEndpoint (V := Multiplicative (Additive V))
        l.kernel l.involution → l.kernel.map (Jhat ρ).subtype = pResidual 2 D := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let f : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro l h
  exact CyclicSource.LocalGeneration.extraspecial_ambient_residual (G := D) f
    (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
    ((Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1)).stronglyQuasithin
      3 (by decide) (by decide)) ρ (UniqueFactor.imageRepresentation_injective _ _ _) (Jhat ρ) l h


/-- The source extraspecial case, with the actual residual and original Sylow
Frattini irreducibility. The preceding endpoint supplies all model facts. -/
theorem source_localAction_extraspecial_full
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let f : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let P := pResidual 2 D
    ∀ l : CyclicSource.LocalGeneration (ρ.comp (Jhat ρ).subtype),
      letI := BinaryGroupAction.action (ρ.comp (Jhat ρ).subtype)
      letI : Finite (Additive V) := Module.finite_of_finite (ZMod 2)
      letI : IsElementaryAbelian 2 (Multiplicative (Additive V)) := BinaryGroupAction.elementary
      letI := l.normal
      ChapterD.Section02.ExtraspecialEndpoint (V := Multiplicative (Additive V))
        l.kernel l.involution →
      l.kernel.map (Jhat ρ).subtype = P ∧ IsExtraspecial 3 P ∧
        Nat.card P = 27 ∧ Monoid.exponent P = 3 ∧ Module.finrank (ZMod 2) (Additive V) = 6 ∧
        ChapterD.Section03.FrattiniIrreducible
          ((T.subtype hM.1.2 : Subgroup M).map f) P le_normalizer_of_normal := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let P := pResidual 2 D
  dsimp only
  intro l h
  let := BinaryGroupAction.action (ρ.comp (Jhat ρ).subtype)
  let : Finite (Additive V) := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative (Additive V)) := BinaryGroupAction.elementary
  let := l.normal
  have hres := source_localAction_extraspecial_residual hG T hM l h
  let e : l.kernel ≃* P :=
    (l.kernel.equivMapOfInjective (Jhat ρ).subtype (Jhat ρ).subtype_injective).trans
      (MulEquiv.subgroupCongr hres)
  let hp : IsExtraspecial 3 P := IsExtraspecial.of_mulEquiv e h.kernel_extraspecial
  have hP : Nat.card P = 27 := (Nat.card_congr e.symm.toEquiv).trans h.card_kernel
  have hexp : Monoid.exponent P = 3 := (Monoid.exponent_eq_of_mulEquiv e).symm.trans h.exponent_kernel
  have hd : Module.finrank (ZMod 2) (Additive V) = 6 := by
    have hc : Nat.card (Additive V) = 64 := (Nat.card_congr Multiplicative.toAdd).symm.trans h.card_module
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [hc,Nat.card_zmod] at hh
    exact Nat.pow_right_injective (by decide : 1 < 2) hh.symm
  refine ⟨hres,hp,hP,hexp,hd,?_⟩
  exact source_extraspecial_image_frattini_irreducible T hM hu hne V
    (localModule_le T hM.1.2) (le_normalizer_conjugateSpanBy _ _) P hP hexp hd rfl

end CFSG.Quasithin.Chapter15.Section01
