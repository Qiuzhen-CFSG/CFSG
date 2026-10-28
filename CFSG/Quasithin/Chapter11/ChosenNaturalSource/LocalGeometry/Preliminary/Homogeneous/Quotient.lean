module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Module
public import CFSG.Quasithin.Chapter3.Section02.ModuleConsequences
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity

/-!
# The seed inside the literal full central quotient

The internal FSU seed supplies the original normalizer action on
V_M/C_{V_M}(L), with its semisimplicity and transitive homogeneous components.
The map from V/C_V(L) is injective, intertwines the unchanged component action,
and generates the full quotient under the normalizer. All projections are the
literal group quotient maps; no central splitting is used.

Source: Aschbacher--Smith, 3.2.2(3) and 11.0.3(2), printed pp.579 and760.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
omit [Finite G] in
/-- The original projection intertwines the actual component conjugation. -/
theorem centralProjection_conjugation (l : L) (v : V) :
    (D.toCentralQuotient (V.normalizerMonoidHom (inclusion D.normalizes l) v)).toAdd =
      D.chosenCentralAction l (D.toCentralQuotient v).toAdd := by
  let w : D.space := (D.spaceEquiv.symm v).toAdd
  have hw : (w.val.toMul.val : G) = (v : G) :=
    (D.spaceEquiv_apply w).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
  have he : D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l w)) =
      V.normalizerMonoidHom (inclusion D.normalizes l) v := by
    apply Subtype.ext
    rw [D.spaceEquiv_apply]
    change (l : G) * (w.val.toMul.val : G) * (l : G)⁻¹ = _
    rw [hw]
    rfl
  change Submodule.Quotient.mk
    (D.spaceEquiv.symm (V.normalizerMonoidHom (inclusion D.normalizes l) v)).toAdd = _
  rw [← he, D.spaceEquiv.symm_apply_apply]
  rfl

/-- The literal full quotient, with its original normalizer action. -/
theorem fullModule_quotient_semisimple_transitive :
    let := fullModule_elementary D S
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    ∃ σ : Representation (ZMod 2) M
        (Additive (U ⧸ (centralizer (L : Set G)).subgroupOf U)),
      IsSemisimpleRepresentation (σ.comp (L.subgroupOf M).subtype) ∧
      (∀ A B : Subrepresentation (σ.comp (L.subgroupOf M).subtype),
        IsIrreducible A.toRepresentation → IsIrreducible B.toRepresentation →
        ∃ g : M, (homogeneousPart A ⊤).map (σ g) = homogeneousPart B ⊤) ∧
      (∀ (g : M) (v : U),
        σ g (Additive.ofMul (QuotientGroup.mk'
          ((centralizer (L : Set G)).subgroupOf U) v)) =
          Additive.ofMul (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U)
            ⟨(g : G) * (v : G) * (g : G)⁻¹,
              (mem_normalizer_iff.mp (le_normalizer_componentOrbit V M g.property) v).mp
                v.property⟩)) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.source.simpleQTKE T S.source.maximal_faithful.1
  let F := D.fundamentalSetup S.source.toHypothesis1221
  obtain ⟨J, hJ, hW, hi⟩ := F.exists_internal_seed hu
  have hh : ∃ I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup F.maximalLocal)),
      ReducedNormal.subspaceImage F.maximalLocal
        (orbitSpan (ReducedNormal.representation F.maximalLocal) ⊤ I) =
          F.fullModule ∧
      Representation.BinaryOffender.IsIrrPlus (ReducedNormal.representation F.maximalLocal)
        ((Chapter3.Section02.localOrbit T L).subgroupOf F.maximalLocal) I :=
    ⟨J, hW, hi.seed⟩
  change (∃ I : Submodule (ZMod 2) (Additive
      (ReducedNormal.ModuleGroup (normalizer (Chapter3.Section02.localOrbit T L : Set G)))),
    ReducedNormal.subspaceImage (normalizer (Chapter3.Section02.localOrbit T L : Set G))
      (BinaryOffender.Homogeneous.orbitSpan
        (ReducedNormal.representation (normalizer (Chapter3.Section02.localOrbit T L : Set G))) ⊤ I) =
          F.fullModule ∧
    BinaryOffender.IsIrrPlus
      (ReducedNormal.representation (normalizer (Chapter3.Section02.localOrbit T L : Set G)))
      ((Chapter3.Section02.localOrbit T L).subgroupOf
        (normalizer (Chapter3.Section02.localOrbit T L : Set G))) I) at hh
  rw [D.localOrbit_eq] at hh
  have hfull : F.fullModule = componentOrbit V (normalizer (L : Set G)) :=
    D.fundamentalSetup_fullModule _
  rw [hfull] at hh
  obtain ⟨I, hI, hi⟩ := hh
  let := fullModule_elementary D S
  let : (L.subgroupOf (normalizer (L : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer le_rfl
  exact ReducedNormal.exists_actual_quotient_consequences (normalizer (L : Set G))
    (orbitSpan (ReducedNormal.representation _) ⊤ I)
    (orbitSpan_invariant _ ⊤ I)
    L L.le_normalizer hi rfl _ hI (le_normalizer_componentOrbit V _)

variable (U : Subgroup G) [IsElementaryAbelian 2 U] (hVU : V ≤ U)

private def seedQuotientHom : Multiplicative D.chosenCentralQuotient →*
    U ⧸ (centralizer (L : Set G)).subgroupOf U :=
  D.toCentralQuotient.liftOfSurjective D.toCentralQuotient_surjective
    ⟨(QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U)).comp (inclusion hVU), by
      intro v hv
      exact (QuotientGroup.eq_one_iff (inclusion hVU v)).mpr
        ((quotient_eq_one_iff D v).mp hv)⟩

omit [Finite G] in
private theorem seedQuotientHom_projection (v : V) :
    seedQuotientHom D U hVU (D.toCentralQuotient v) =
      QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U) (inclusion hVU v) := by
  unfold seedQuotientHom
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

/-- The chosen central quotient embeds in the full quotient by the literal
inclusion of V. No splitting or choice of complement is used. -/
def seedQuotientMap : D.chosenCentralQuotient →ₗ[ZMod 2]
    Additive (U ⧸ (centralizer (L : Set G)).subgroupOf U) :=
  (show D.chosenCentralQuotient →+ Additive (U ⧸ (centralizer (L : Set G)).subgroupOf U) from
    { toFun := fun q => Additive.ofMul (seedQuotientHom D U hVU (Multiplicative.ofAdd q))
      map_zero' := (seedQuotientHom D U hVU).map_one
      map_add' := (seedQuotientHom D U hVU).map_mul }).toZModLinearMap 2

omit [Finite G] in
theorem seedQuotientMap_projection (v : V) :
    seedQuotientMap D U hVU (D.toCentralQuotient v).toAdd =
      Additive.ofMul (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U)
        (inclusion hVU v)) :=
  congrArg Additive.ofMul (seedQuotientHom_projection D U hVU v)

omit [Finite G] in
theorem seedQuotientMap_injective : Function.Injective (seedQuotientMap D U hVU) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro q hq
  obtain ⟨v, hv⟩ := D.toCentralQuotient_surjective (Multiplicative.ofAdd q)
  have hp : (D.toCentralQuotient v).toAdd = q := congrArg Multiplicative.toAdd hv
  rw [← hp, seedQuotientMap_projection] at hq
  have hc : (v : G) ∈ centralizer (L : Set G) :=
    (QuotientGroup.eq_one_iff (inclusion hVU v)).mp hq
  exact hp.symm.trans (congrArg Multiplicative.toAdd ((quotient_eq_one_iff D v).mpr hc))


omit [Finite G] in
/-- When V is the full orbit, its central quotient fills the literal full quotient. -/
theorem seedQuotientMap_surjective (hUV : U ≤ V) :
    Function.Surjective (seedQuotientMap D U hVU) := by
  intro q
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective ((centralizer (L : Set G)).subgroupOf U) q.toMul
  refine ⟨(D.toCentralQuotient ⟨u.val, hUV u.property⟩).toAdd, ?_⟩
  rw [seedQuotientMap_projection]
  exact congrArg Additive.ofMul hu

variable (hU : L ≤ normalizer (U : Set G))
    (σ : Representation (ZMod 2) L (Additive (U ⧸ (centralizer (L : Set G)).subgroupOf U)))
    (hσ : ∀ (l : L) (u : U),
      σ l (Additive.ofMul (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U) u)) =
        Additive.ofMul (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U)
          (U.normalizerMonoidHom (inclusion hU l) u)))


include hσ in
omit [Finite G] in
/-- The embedding uses the unchanged L-action on both quotients. -/
theorem seedQuotientMap_equivariant (l : L) (q : D.chosenCentralQuotient) :
    seedQuotientMap D U hVU (D.chosenCentralAction l q) =
      σ l (seedQuotientMap D U hVU q) := by
  obtain ⟨v, hv⟩ := D.toCentralQuotient_surjective (Multiplicative.ofAdd q)
  rw [← show (D.toCentralQuotient v).toAdd = q from congrArg Multiplicative.toAdd hv,
    ← centralProjection_conjugation, seedQuotientMap_projection,
    seedQuotientMap_projection, hσ]
  rfl


include D hVU hσ in
/-- An invariant original seed gives an irreducible actual full quotient. -/
theorem quotient_irreducible_of_eq_seed (hUV : U ≤ V) : IsIrreducible σ := by
  let e : D.chosenCentralQuotient ≃ₗ[ZMod 2]
      Additive (U ⧸ (centralizer (L : Set G)).subgroupOf U) :=
    LinearEquiv.ofBijective (seedQuotientMap D U hVU)
      ⟨seedQuotientMap_injective D U hVU, seedQuotientMap_surjective D U hVU hUV⟩
  let a : ActionEquiv D.chosenCentralAction σ :=
    ⟨MulEquiv.refl L, e, seedQuotientMap_equivariant D U hVU hU σ hσ⟩
  have hi : IsIrreducible D.chosenCentralAction :=
    (irreducible_comp_surjective_iff (QuotientGroup.mk' (pCore 2 L))
      (QuotientGroup.mk'_surjective _) D.centralQuotientAction).mpr D.centralQuotientAction_irreducible
  exact ExtensionConsequences.irreducible_of_equiv (ExtensionConsequences.actionSymm a) hi

section Generation
variable (σM : Representation (ZMod 2) (normalizer (L : Set G))
    (Additive (U ⧸ (centralizer (L : Set G)).subgroupOf U)))
    (hUM : normalizer (L : Set G) ≤ normalizer (U : Set G))
    (hσM : ∀ (g : normalizer (L : Set G)) (u : U),
      σM g (Additive.ofMul (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U) u)) =
        Additive.ofMul (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U)
          (U.normalizerMonoidHom (inclusion hUM g) u)))

include hUM hσM in
omit [Finite G] in
/-- The image of the original seed generates the entire quotient under M.
This is generation by the literal normalizer orbit, before any type comparison. -/
theorem fullQuotient_seed_generates (hgen : U = componentOrbit V (normalizer (L : Set G)))
    (W : Subrepresentation σM)
    (hW : (seedQuotientMap D U hVU).range ≤ W.toSubmodule) : W = ⊤ := by
  let q := QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U)
  let P : Subgroup G := (W.toSubmodule.toAddSubgroup.toSubgroup.comap q).map U.subtype
  have hVP : V ≤ P := by
    intro v hv
    refine ⟨inclusion hVU ⟨v, hv⟩, ?_, rfl⟩
    change Additive.ofMul (q (inclusion hVU ⟨v, hv⟩)) ∈ W
    rw [← seedQuotientMap_projection D U hVU ⟨v, hv⟩]
    exact hW ⟨_, rfl⟩
  have hNP : normalizer (L : Set G) ≤ normalizer (P : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg v hv
    obtain ⟨u, hu, rfl⟩ := hv
    refine ⟨U.normalizerMonoidHom (inclusion hUM ⟨g, hg⟩) u, ?_, rfl⟩
    change Additive.ofMul (q (U.normalizerMonoidHom (inclusion hUM ⟨g, hg⟩) u)) ∈ W
    rw [← hσM]
    exact W.apply_mem_toSubmodule ⟨g, hg⟩ hu
  have hUP : U ≤ P := hgen ▸ iSup_conjugates_le_of_le_normalizer V _ P hVP hNP
  apply top_unique
  intro z _
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective ((centralizer (L : Set G)).subgroupOf U) z.toMul
  obtain ⟨v, hv, he⟩ := hUP u.property
  have he' : v = u := Subtype.ext he
  subst v
  exact hv
end Generation


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
