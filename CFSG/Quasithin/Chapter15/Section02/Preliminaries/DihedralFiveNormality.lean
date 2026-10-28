module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralFiveSetup
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.ChosenResidualNormalizer
public import Theory.GroupTheory.PResidual.CyclicImageNormality
public import Theory.GroupTheory.PResidual.NormalityLift
public import Theory.Representation.SmallBinaryCyclicResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
/-!
# Normality of the original marked-five residual

The marked normal five-subgroup in the faithful four-dimensional action
makes the full action two-residual cyclic. In M/O₂(M), the intersection
core centralizes the action kernel by source15.2.3(5). Its full normal
closure therefore has faithful cyclic two-residual. The original relative
residual Y* lies inside this cyclic normal subgroup and is itself normal.
The already proved normalization of Y by C_M(V) supplies the kernel
normalization needed to lift normality of the two-perfect Y through O₂(M).

The final wrapper retains W=⟨YRc,K,S⟩ and M₁=W∩M exactly. It discharges the
Y-normality premise of C.1.2(4) and C.2.3 in the original15.2.4 argument.
No source15.1.14 or global factorization premise is used.
Source: Aschbacher--Smith15.2.3(2),15.2.4, printed pp.1105--1106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]
private theorem residual_notation {D : Type*} [Group D] [Finite D] (K : Subgroup D) :
    twoResidualAmbient K = (pResidual 2 K).map K.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN,n,hn⟩
    exact ⟨hN,IsPGroup.of_card hn⟩
  · rintro ⟨hN,hn⟩
    exact ⟨hN,IsPGroup.iff_card.mp hn⟩

/-- In the marked five row, the original chosen residual is normal in M. -/
theorem source_dihedral_five_residual_normal
    (T : Sylow 2 G) {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype))
    (hd : DihedralMarking l 5 2) :
    ((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).Normal := by
  let ρ := imageRepresentation M V hV.normalized
  let f : M →* internalActionImage M V hV.normalized := (actionHom M V hV.normalized).rangeRestrict
  let q := QuotientGroup.mk' (pCore 2 M)
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let A := Y.subgroupOf M
  let R := ((M ⊓ Mc).pCoreIn 2).subgroupOf M
  let B := (twoResidualAmbient (chosenStarredPreimage M V hV.normalized) ⊔
    (T : Subgroup G)).subgroupOf M
  have hfker : f.ker = (actionHom M V hV.normalized).ker := by
    ext x
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  have hcore : pCore 2 M ≤ f.ker := by
    rw [hfker]
    exact source_chosen_core_le_kernel T hTM hV
  let g := QuotientGroup.lift (pCore 2 M) f hcore
  have hker : g.ker = f.ker.map q := QuotientGroup.ker_lift _ _ _
  have hCeq : (M ⊓ centralizer (V : Set G)).subgroupOf M = f.ker := by
    rw [hfker,actionHom_ker]
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
  have hcentral : R.map q ≤ centralizer (g.ker : Set (M ⧸ pCore 2 M)) := by
    rw [hker,←hCeq]
    exact le_sup_left.trans (source_chosen_lemma_15_2_3_5 T hTM hu hV)
  let P := l.kernel.map (Jhat ρ).subtype
  let : (Jhat ρ).Normal := Jhat_normal ρ
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨_,_,hPc,hPn,_⟩ := hd.ambient_marks (Jhat ρ) hp
  let : P.Normal := hPn
  let : IsCyclic (pResidual 2 (internalActionImage M V hV.normalized)) :=
    Representation.SmallBinaryCyclicResidual.cyclic_twoResidual_of_normal_five
      ρ (imageRepresentation_injective _ _ _) (by simpa using hd.dimension) P hPc
  have hY : A.map q = (pResidual 2 (conjugateSpanBy (R.map q) (B.map q))).map
      (conjugateSpanBy (R.map q) (B.map q)).subtype := by
    rw [show A = Y.subgroupOf M from rfl,
      source_caseIIResidual_image T hTM (map_subtype_le _) q,residual_notation]
  have hn : (A.map q).Normal := by
    rw [hY]
    exact normal_twoResidual_conjugateSpan_of_cyclic_residual_image
      g (R.map q) (B.map q) ((isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype.map q) hcentral
  let := hn
  have hYM : Y ≤ M := source_caseIIResidual_le T hTM (map_subtype_le _)
  have hperfect : IsPPerfect 2 A := by
    have hYperfect : IsPPerfect 2 Y := by
      change IsPPerfect 2 (twoResidualAmbient
        (conjugateSpanBy ((M ⊓ Mc).pCoreIn 2)
          (twoResidualAmbient (chosenStarredPreimage M V hV.normalized) ⊔ (T : Subgroup G))))
      rw [residual_notation]
      exact isPPerfect_embedded_pResidual 2 _
    exact hYperfect.of_surjective (subgroupOfEquivOfLe hYM).symm.toMonoidHom
      (subgroupOfEquivOfLe hYM).symm.surjective
  apply normal_of_map_normal_of_pPerfect q A hperfect
  · rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  · have hC : M ⊓ centralizer (V : Set G) ≤ normalizer (Y : Set G) :=
      le_sup_left.trans (source_chosen_centralizer_sylow_normalizes_residual T hTM hu hV).1
    rw [QuotientGroup.ker_mk']
    rw [←subgroupOf_normalizer_eq hYM]
    exact hcore.trans (hCeq ▸ comap_mono hC)

/-- The exact generated marked-five configuration has Y normal in M₁=W∩M,
supplying the normality premise of source C.1.2(4) and C.2.3. -/
theorem source_dihedral_five_generated_intersection_residual_normal
    (T : Sylow 2 G) {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype))
    (hd : DihedralMarking l 5 2) (K : Subgroup G) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    let W := ChapterF.Source.generated ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K] S
    (Y.subgroupOf (W ⊓ M)).Normal := by
  intro Y S W
  have hn := source_dihedral_five_residual_normal T hTM hu hV l hd
  have hYM : Y ≤ M := source_caseIIResidual_le T hTM (map_subtype_le _)
  exact normal_subgroupOf_of_le_normalizer
    (inf_le_right.trans ((normal_subgroupOf_iff_le_normalizer hYM).mp hn))

end CFSG.Quasithin.Chapter15.Section02
