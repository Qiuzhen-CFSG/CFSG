module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerAlternatingGeometry
public import Theory.GroupTheory.SylowFixedNormalClosureSplitting
public import Theory.GroupTheory.NormalClosureCommutatorSupplement
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Conjugation

/-!
# Splitting the actual source omega module in a short-block configuration

Write H=LT, W=⟨Ω₁Z(T)^H⟩ and U=U(L). Normality of L in H and the
Sylow-fixed seed give [W,H]=[W,L]. Two-perfect commutator idempotence puts
this subgroup in U. In an escaping configuration U≤W, so [W,H]=U.
The Sylow-fixed normal-closure splitting then gives W=U C_W(H).

Since W is elementary and contained in T, C_W(H)≤Ω₁Z(T). Intersecting the
split with Ω₁Z(T) proves that C_L(Ω₁Z(T)) is exactly C_L(C_U(T)). The final
theorem applies this equality to the literal embedded residual defining
blockLocalResidual, preserving all subgroup inclusions and quotient maps.
Thus the remaining six-letter image calculation can use the intrinsic
block layer without identifying W or U with the chosen Chapter 12 module V.
The A₆ residual coordinates and the remaining block contradictions are
retained by the final assembly owner qt-d-12216-normalizer-block-centralizer.

Source: Aschbacher–Smith, B.2.13–14, C.1.7–13, the splitting clause of
3.3.7(4), 3.3.9, and 3.3.31, printed pp.78,123–125,587–588,602. The averaging and normal-supplement results
are reused through their existing general interfaces.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual orbit closure lies in the original Sylow two-subgroup. -/
theorem blockOmegaModule_le_sylow
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    blockOmegaModule T L ≤ (T : Subgroup G) := by
  apply (blockOmegaModule_le_core h).trans
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

/-- The intrinsic block layer is the exact L-commutator of the source module. -/
theorem blockOmegaModule_commutator_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L) :
    ⁅blockOmegaModule T L, L⁆ = (ChapterC.blockU L).map L.subtype := by
  let W := blockOmegaModule T L
  let U := (ChapterC.blockU L).map L.subtype
  have hLW : L ≤ normalizer (W : Set G) := le_sup_left.trans join_normalizes_blockOmegaModule
  have hp : IsPGroup 2 W := (isPGroup_pCoreIn 2 _).to_le (blockOmegaModule_le_core h)
  have hWL : W ≤ normalizer (L : Set G) :=
    (blockOmegaModule_le_sylow h).trans D.sylow_normalizes_component
  have hcore : ⁅W, L⁆ ≤ L.pCoreIn 2 := le_pCoreIn_of_normalizes
    (hp.to_le (le_normalizer_iff_commutator_le_left.mp hLW))
    (le_normalizer_iff_commutator_le_right.mp hWL) (normalizer_commutator_ge_right W L)
  have hid := commutator_isPPerfect_idempotent L W hb.twoPerfect hp hLW
  have hUL : ⁅U, L⁆ = U := by
    simpa only [map_commutator, ← MonoidHom.range_eq_map, range_subtype] using
      congrArg (Subgroup.map L.subtype) (ChapterC.ExceptionalRestrictions.short_commutator hb)
  apply le_antisymm
  · rw [show (ChapterC.blockU L).map L.subtype = ⁅L.pCoreIn 2, L⁆ from
      block_module_eq_commutator]
    exact hid.symm.le.trans (commutator_mono hcore le_rfl)
  · exact hUL.symm.le.trans (commutator_mono (blockU_le_blockOmegaModule h D hescape hb) le_rfl)

omit [Finite G] in
/-- The Sylow-fixed seed makes the full local commutator equal to the L-commutator. -/
theorem blockOmegaModule_commutator_join (D : ChosenModule T L V) :
    ⁅blockOmegaModule T L, L ⊔ (T : Subgroup G)⁆ = ⁅blockOmegaModule T L, L⁆ := by
  let H := L ⊔ (T : Subgroup G)
  let P : Sylow 2 H := T.subtype le_sup_right
  let Z := Stellmacher.omegaOneCenterAmbient (P : Subgroup H)
  let W := normalClosure (Z : Set H)
  let E := L.subgroupOf H
  let : E.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hc : Z ≤ centralizer (P : Set H) := by
    intro z hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
  have hs : E ⊔ (P : Subgroup H) = ⊤ := by
    change L.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hh := congrArg (Subgroup.map H.subtype)
    (commutator_normalClosure_eq_of_normal_supplement Z W E P
      subset_normalClosure rfl hc hs)
  have hEL : E.map H.subtype = L := map_subgroupOf_eq_of_le le_sup_left
  rw [map_commutator, map_commutator, ← MonoidHom.range_eq_map, range_subtype, hEL] at hh
  exact hh

/-- Split the literal omega-generated module into the block layer and the H-fixed subgroup. -/
theorem blockOmegaModule_split
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L) :
    blockOmegaModule T L = (ChapterC.blockU L).map L.subtype ⊔
      (blockOmegaModule T L ⊓ centralizer (L ⊔ (T : Subgroup G) : Subgroup G)) := by
  let H := L ⊔ (T : Subgroup G)
  let P : Sylow 2 H := T.subtype le_sup_right
  let Z := Stellmacher.omegaOneCenterAmbient (P : Subgroup H)
  let W := normalClosure (Z : Set H)
  have hc : (center H).map H.subtype = H ⊓ centralizer (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, fun a ha => congrArg Subtype.val (mem_center_iff.mp hy ⟨a, ha⟩)⟩
    · rintro ⟨hx, hc⟩
      exact ⟨⟨x, hx⟩, mem_center_iff.mpr (fun a => Subtype.ext (hc a a.property)), rfl⟩
  have hh := congrArg (Subgroup.map H.subtype)
    (omegaCenter_subgroup_normalClosure_split P (join_characteristicTwo h) Z le_rfl)
  rw [Subgroup.map_sup, map_commutator, ← MonoidHom.range_eq_map, range_subtype,
    Subgroup.map_inf _ _ _ H.subtype_injective, hc] at hh
  have hWH : W.map H.subtype ≤ H := map_subtype_le _
  rw [← inf_assoc, inf_eq_left.mpr hWH] at hh
  change blockOmegaModule T L = ⁅blockOmegaModule T L, L ⊔ (T : Subgroup G)⁆ ⊔ _ at hh
  rw [blockOmegaModule_commutator_join D, blockOmegaModule_commutator_component h D hescape hb] at hh
  exact hh

/-- Split the original central omega using the intrinsic block layer. -/
theorem omegaCenter_split_blockU
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L) :
    omegaCenterIn (T : Subgroup G) =
      ((ChapterC.blockU L).map L.subtype ⊓ omegaCenterIn (T : Subgroup G)) ⊔
      (blockOmegaModule T L ⊓ centralizer (L ⊔ (T : Subgroup G) : Subgroup G)) := by
  let W := blockOmegaModule T L
  let U := (ChapterC.blockU L).map L.subtype
  let F := W ⊓ centralizer (L ⊔ (T : Subgroup G) : Subgroup G)
  let Z := omegaCenterIn (T : Subgroup G)
  let : IsElementaryAbelian 2 W := blockOmegaModule_elementary h
  have hUW : U ≤ W := blockU_le_blockOmegaModule h D hescape hb
  have hFZ : F ≤ Z := by
    intro f hf
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨blockOmegaModule_le_sylow h hf.1,
      centralizer_le (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right) hf.2,
      elemPow_eq_one_of_isElementaryAbelian f hf.1⟩
  have hUF : U ≤ normalizer (F : Set G) := by
    apply (le_centralizer_iff.mp (show F ≤ centralizer (U : Set G) from ?_)).trans
      (Subgroup.centralizer_le_normalizer _)
    exact inf_le_right.trans (centralizer_le (hUW.trans
      ((blockOmegaModule_le_sylow h).trans le_sup_right)))
  apply le_antisymm ?_ (sup_le inf_le_right hFZ)
  intro z hz
  have hzW : z ∈ U ⊔ F := by
    rw [← blockOmegaModule_split h D hescape hb]
    exact omegaCenter_le_blockOmegaModule hz
  have hzprod : z ∈ (U : Set G) * (F : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right U F hUF]
    exact hzW
  obtain ⟨u, hu, f, hf, rfl⟩ := hzprod
  have huZ : u ∈ Z := by
    have hx := Z.mul_mem hz (Z.inv_mem (hFZ hf))
    simpa only [mul_inv_cancel_right] using hx
  exact mul_mem_sup (show u ∈ U ⊓ Z from ⟨hu, huZ⟩) hf

/-- The extra fixed summand does not affect the centralizer inside L. -/
theorem omega_local_centralizer_eq_blockU
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L) :
    L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G) =
      L ⊓ centralizer ((ChapterC.blockU L).map L.subtype ⊓
        omegaCenterIn (T : Subgroup G) : Subgroup G) := by
  apply le_antisymm (inf_le_inf_left _ (centralizer_le inf_le_right))
  apply le_inf inf_le_left
  apply le_centralizer_iff.mpr
  apply (omegaCenter_split_blockU h D hescape hb).le.trans
  exact sup_le (le_centralizer_iff.mp inf_le_right)
    (inf_le_right.trans (centralizer_le (fun x hx => mem_sup_left hx.1)))

/-- On the elementary block layer, central omega membership is Sylow fixedness. -/
theorem blockU_inf_omegaCenter_eq_sylow_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L) :
    (ChapterC.blockU L).map L.subtype ⊓ omegaCenterIn (T : Subgroup G) =
      (ChapterC.blockU L).map L.subtype ⊓ centralizer (T : Set G) := by
  let U := (ChapterC.blockU L).map L.subtype
  let : IsElementaryAbelian 2 U := hb.elementary.map L.subtype
  have hUT : U ≤ (T : Subgroup G) :=
    (blockU_le_blockOmegaModule h D hescape hb).trans (blockOmegaModule_le_sylow h)
  apply le_antisymm
  · exact inf_le_inf_left _ (fun z hz => ((mem_omegaCenterIn_iff _ _).mp hz).2.1)
  · intro u hu
    exact ⟨hu.1, (mem_omegaCenterIn_iff _ _).mpr
      ⟨hUT hu.1, hu.2, elemPow_eq_one_of_isElementaryAbelian u hu.1⟩⟩

/-- Apply the source-module split to the actual local residual used by the terminal argument. -/
theorem blockLocalResidual_eq_sylow_fixed_blockU
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L) :
    blockLocalResidual T L =
      let C := L ⊓ centralizer ((ChapterC.blockU L).map L.subtype ⊓
        centralizer (T : Set G) : Subgroup G)
      (pResidual 2 C).map C.subtype := by
  dsimp only [blockLocalResidual]
  rw [omega_local_centralizer_eq_blockU h D hescape hb,
    blockU_inf_omegaCenter_eq_sylow_fixed h D hescape hb]

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
