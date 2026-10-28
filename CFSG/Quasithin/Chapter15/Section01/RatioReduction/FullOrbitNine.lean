module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitSingletonRatio
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitNineIrreducible
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NineAmbient
/-!
# The original full-orbit elementary-nine alternative

The singleton cyclic source has its marked kernel inside the original Jhat
and acts on the whole local module. Its E9 endpoint gives dimension four
and a normal nine-core. The original ratio and component irreducibility
theorems discharge the ambient extension hypotheses. The actual image of
T is cyclic of order four, the marked kernel is the two-residual, and
equivariant coordinates embed the original action into O₄⁺(2).

Source: Aschbacher–Smith 15.1.2(5), printed p.1086. The E9 endpoint is the
corresponding branch of source_localAction_singleton_cyclic_endpoints.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]
set_option synthInstance.maxSize 10000

theorem source_localAction_full_orbit_nine
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let q := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    ∀ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ (i : d.Index), (∀ j : d.Index,j=i) → U=⊤ →
      (∀ A ∈ QhatStar (d.factor i).action, IsCyclic A) →
    ∀ l : CyclicSource.LocalGeneration (ρ.comp (Jhat ρ).subtype),
      letI := BinaryGroupAction.action (ρ.comp (Jhat ρ).subtype)
      letI : Finite (Additive V) := Module.finite_of_finite (ZMod 2)
      letI : IsElementaryAbelian 2 (Multiplicative (Additive V)) := BinaryGroupAction.elementary
      letI := l.normal
      ChapterD.Section02.ElementaryNineEndpoint (V := Multiplicative (Additive V))
        l.kernel l.involution →
      Module.finrank (ZMod 2) (Additive V) = 4 ∧ Nat.card D = 36 ∧
        l.kernel.map (Jhat ρ).subtype = pResidual 2 D ∧
        (∀ S : Sylow 2 D, IsCyclic S ∧ Nat.card S = 4) ∧
        (IsCyclic ((T.subtype hM.1.2 : Subgroup M).map q) ∧
          Nat.card ((T.subtype hM.1.2 : Subgroup M).map q) = 4) ∧
        ∃ (b : Additive V ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
          (f : D →* OrthogonalFourBinary.TerminalLines.IsometryGroup),
          Function.Injective f ∧ ∀ g v, b (ρ g v) = (f g).val (b v) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let q := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let K := Jhat ρ
  let : K.Normal := Jhat_normal ρ
  dsimp only
  intro U c d hd i hi hU hc l
  let := BinaryGroupAction.action (ρ.comp K.subtype)
  let : Finite (Additive V) := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative (Additive V)) := BinaryGroupAction.elementary
  let := l.normal
  intro h9
  let := h9.kernel_elementary
  have hk := l.kernel_eq_threeCore_of_elementary_nine h9.kernel_elementary h9.card_kernel
  let P := l.kernel.map K.subtype
  let : P.Normal := by
    change (l.kernel.map K.subtype).Normal
    rw [hk]
    infer_instance
  let : IsElementaryAbelian 3 P := IsElementaryAbelian.map _
  have hcP : Nat.card P = 9 := (card_map_of_injective K.subtype_injective).trans h9.card_kernel
  have hdim : Module.finrank (ZMod 2) (Additive V) = 4 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have hv : Nat.card (Additive V) = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact hv.symm.trans ((Nat.card_congr (Multiplicative.toAdd (α := Additive V))).symm.trans h9.card_module)
  have hm : subspaceCommutator ρ ⊤ P = ⊤ := by
    rw [←subspaceCommutator_comp_map]
    exact l.moved
  have hq := source_localAction_singleton_cyclic_ratio_two hG T hempty hM hmany hJ
    U c d hd i hi hU hc (by rw [hdim]; decide)
  have hir := source_localAction_nine_irreducible hG T hempty hM hJ hu hne P hcP hdim hm
  have hf : Function.Injective ρ := imageRepresentation_injective _ _ _
  obtain ⟨hcD,hres,hS⟩ := l.nine_ambient_extension hf K hq hir h9
  have hactual := hS ((T.subtype hM.1.2).mapSurjective
    (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective)
  refine ⟨hdim,hcD,hres,hS,hactual,?_⟩
  obtain ⟨s⟩ := FittingConfigurations.supportFactors_of_nine_four_moved ρ hf P hcP hdim hm
  exact s.exists_isometry_embedding ρ hf (s.factor_conj_closed ρ hf)
end CFSG.Quasithin.Chapter15.Section01
