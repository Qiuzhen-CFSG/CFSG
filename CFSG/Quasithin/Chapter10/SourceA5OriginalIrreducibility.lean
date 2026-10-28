module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.Recognition
public import CFSG.Quasithin.Chapter3.Section02.ModuleConsequences
public import Theory.Representation.CliffordSubquotient

/-!
# Semisimple original A₅ quotient and minimal seed selection

The source 3.2.2 quotient is semisimple for the literal local action. We
transport it down the subnormal chain L < L₀ < M and across the original
quotient maps, obtaining semisimplicity of W/C_W(L) with its exact A₅
coordinates. Full commutator generation makes the quotient have no fixed
vectors, so every irreducible constituent is nontrivial; the proved binary
A₅ classifier therefore marks each constituent as natural or deleted and of
binary dimension four.

The source D.3.21(3) replacement is represented separately by
`MinimalModuleSelection`: Chapter 13 consumers may choose a setup with
minimal full-module order. The present theorem deliberately does not assert
irreducibility of an arbitrary fixed setup; the source removes the
two-constituent branch by a new seed choice before the A₅-specific assembly.
Source: Aschbacher–Smith,3.2.2(3),3.2.6,D.3.21 and10.1.1,
printed pp.579,581,204–207,741.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))

include D in
private theorem source_uniqueness :
    Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

local instance movedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

theorem source_a5_original_quotient_semisimple :
    IsSemisimpleRepresentation (originalMovedQuotientAction D e) := by
  let X := localOrbit T L
  let M := D.maximalLocal
  let V := D.fullModule
  let W := ⁅V,L⁆
  let Z := sourceMovedFixed D
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hLX : L ≤ X := le_componentOrbit L T
  have hXM : X ≤ M := X.le_normalizer
  have hLM : L ≤ M := hLX.trans hXM
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp
    (hLM.trans D.maximalLocal_normalizes_fullModule)
  let := D.fullModule_elementary (source_uniqueness D)
  obtain ⟨σ,hsemi,_,hσ⟩ := D.fullModule_quotient_consequences (source_uniqueness D)
  let σX := σ.comp (inclusion hXM)
  let σL := σ.comp (inclusion hLM)
  let : IsSemisimpleModule (ZMod 2)[X.subgroupOf M]
      (Representation.asModule (σ.comp (X.subgroupOf M).subtype)) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp hsemi
  let : IsSemisimpleModule (ZMod 2)[X] (Representation.asModule σX) :=
    comp_semisimple_of_surjective (σ.comp (X.subgroupOf M).subtype)
      (subgroupOfEquivOfLe hXM).symm.toMonoidHom (subgroupOfEquivOfLe hXM).symm.surjective
  have hsub : (L.subgroupOf X).IsSubnormal :=
    (D.maximal.1.1.subgroupOf_of_le hLX (componentOrbit_le_sup L T)).subnormal
  let : IsSemisimpleModule (ZMod 2)[L.subgroupOf X]
      (Representation.asModule (σX.comp (L.subgroupOf X).subtype)) :=
    subnormal_restriction_semisimple σX (L.subgroupOf X) hsub
  let : IsSemisimpleModule (ZMod 2)[L] (Representation.asModule σL) :=
    comp_semisimple_of_surjective (σX.comp (L.subgroupOf X).subtype)
      (subgroupOfEquivOfLe hLX).symm.toMonoidHom (subgroupOfEquivOfLe hLX).symm.surjective
  obtain ⟨ρ,_,hρ⟩ := source_a5_original_moved_action D e
  let τ := ρ.comp q
  let υ := (originalMovedQuotientAction D e).comp q
  let a : Additive W →ₗ[ZMod 2]
      Additive (V ⧸ (centralizer (X : Set G)).subgroupOf V) :=
    ((QuotientGroup.mk' ((centralizer (X : Set G)).subgroupOf V)).comp
      (inclusion hWV)).toAdditive.toZModLinearMap 2
  let b : Additive W →ₗ[ZMod 2] Additive (W ⧸ Z.subgroupOf W) :=
    (QuotientGroup.mk' (Z.subgroupOf W)).toAdditive.toZModLinearMap 2
  let f : Representation.IntertwiningMap τ σL := {
    toLinearMap := a
    isIntertwining' l := by
      ext w
      change Additive.ofMul (QuotientGroup.mk' _ (inclusion hWV (ρ (q l) w).toMul)) =
        σ ⟨l,hLM l.property⟩ (Additive.ofMul (QuotientGroup.mk' _ (inclusion hWV w.toMul)))
      rw [hσ]
      congr 2
      apply Subtype.ext
      exact hρ l w }
  let g : Representation.IntertwiningMap τ υ := {
    toLinearMap := b
    isIntertwining' l := by
      apply LinearMap.ext
      intro w
      have h := (originalMovedQuotientSection D e).equivariant l w.toMul
      rw [originalMovedQuotientSection_coordinates,
        originalMovedQuotientSection_coordinates] at h
      change Additive.ofMul (QuotientGroup.mk' ((sourceMovedFixed D).subgroupOf ⁅D.fullModule,L⁆)
        (ρ (q l) w).toMul) = (originalMovedQuotientAction D e) (q l)
          (Additive.ofMul (QuotientGroup.mk' ((sourceMovedFixed D).subgroupOf ⁅D.fullModule,L⁆) w.toMul))
      convert h using 1 <;> try rfl
      congr 2
      apply Subtype.ext
      exact hρ l w }
  have hker : f.toLinearMap.ker ≤ g.toLinearMap.ker := by
    intro w hw
    change QuotientGroup.mk' ((centralizer (X : Set G)).subgroupOf V)
      (inclusion hWV w.toMul) = 1 at hw
    change QuotientGroup.mk' (Z.subgroupOf W) w.toMul = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    have hc : inclusion hWV w.toMul ∈ (centralizer (X : Set G)).subgroupOf V :=
      (QuotientGroup.eq_one_iff _).mp hw
    exact ⟨w.toMul.property,centralizer_le hLX hc⟩
  have honto : Function.Surjective g := by
    intro w
    obtain ⟨v,hv⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) w.toMul
    exact ⟨Additive.ofMul v,hv⟩
  have hs : IsSemisimpleModule (ZMod 2)[L] (Representation.asModule υ) :=
    semisimple_of_shared_cover τ σL υ f g honto hker
  apply (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
  exact (semisimple_comp_iff_of_surjective (originalMovedQuotientAction D e) q
    (e.surjective.comp (QuotientGroup.mk'_surjective _))).mp hs

theorem source_a5_original_quotient_fixedSpace_eq_bot :
    BinaryOffender.fixedSpace (originalMovedQuotientAction D e) ⊤ = ⊥ := by
  let := source_a5_original_quotient_semisimple D e
  exact BinaryOffender.fixedSpace_eq_bot_of_semisimple_coinvariants
    (originalMovedQuotientAction D e)
    (source_original_moved_quotient_coinvariants D e
      (originalMovedQuotientAction D e) (originalMovedQuotientSection D e))

theorem source_a5_original_constituent_nontrivial
    (S : Subrepresentation (originalMovedQuotientAction D e))
    (hi : S.toRepresentation.IsIrreducible) :
    ∃ a, S.toRepresentation a ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hs : S = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    apply le_bot_iff.mp
    intro v hv
    apply (source_a5_original_quotient_fixedSpace_eq_bot D e).le
    intro a
    exact congrArg Subtype.val
      (congrArg (fun f : Module.End (ZMod 2) S.toSubmodule => f ⟨v,hv⟩) (h a))
  exact ((Subrepresentation.irreducible_iff_isAtom S).mp hi).ne_bot hs

local instance fieldFourAlgebra :
    Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

open scoped MatrixGroups in
theorem source_a5_original_constituent_alternatives
    (S : Subrepresentation (originalMovedQuotientAction D e))
    (hi : S.toRepresentation.IsIrreducible) :
    Module.finrank (ZMod 2) S.toSubmodule = 4 ∧
      ((∃ f : alternatingGroup (Fin 5) ≃*
          SL(2,Representation.OrthogonalFourMinus.FiniteModel.Field 1),
        Nonempty (S.toRepresentation.Equiv
          (Representation.SL2.BinarySmall.natural.comp f.toMonoidHom))) ∨
      ∃ f : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5),
        Nonempty (S.toRepresentation.Equiv
          (Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp
            f.toMonoidHom))) := by
  let := hi
  exact ChapterG.Section09.DefiningCharacteristic.alternating_five_irreducible_action_alternatives
    S.toRepresentation (MulEquiv.refl _) (source_a5_original_constituent_nontrivial D e S hi)

end CFSG.Quasithin.Chapter10
