module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalF11
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.G2
public import Theory.AtlasPort.LinearGroups.G2.ShortLocalCoreCenter

/-!
# Excluding a native G₂ pair from two original A₅ contexts

The original chosen module is nontrivial, lies in the center of its
component's whole two-core, and has no component-fixed points. The short
native G₂ local factor centralizes the center of its whole two-core.
Consequently an original component cannot be that native factor.

An actual reduced G₂ comparison identifies the short original factor with
the native parabolic residual. This uses preservation of the full core and
residual, with no normalized-Borel premise and no bound on any core order.
The binary field is excluded by solvability of the short parabolic; no
field-size classification is needed.

Source: Aschbacher--Smith 13.2.8(1), p.880, F.1.12(I)(3), pp.262--264,
and the native short-core centrality used in 10.2.9, pp.750--751.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source ChapterF.Source
open ChapterF.Source.DGS85.OriginalExtension
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ K W W₁ W₂ W₃ : Subgroup G}

private theorem original_core_center_not_central
    (d : Context T L V V₁ V₂ V₃) :
    ¬ (center (pCore 2 L)).map (pCore 2 L).subtype ≤ center L := by
  intro hc
  have hVC : V ≤ centralizer (L.pCoreIn 2 : Set G) :=
    le_centralizer_iff.mp
      ((pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer d.normalizes_L)).trans
        d.chosen.core_centralizes)
  apply d.chosen.ne_bot
  apply bot_unique
  intro v hv
  apply d.flag.module.fixed_eq_bot.le
  refine ⟨hv,?_⟩
  obtain ⟨x,hx,rfl⟩ := d.chosen.le_componentCore hv
  have hz : (⟨x,hx⟩ : pCore 2 L) ∈ center (pCore 2 L) := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact hVC hv y.val.val (mem_map_of_mem L.subtype y.property)
  have hxc : x ∈ center L := hc (mem_map_of_mem (pCore 2 L).subtype hz)
  intro l hl
  exact congrArg L.subtype (mem_center_iff.mp hxc ⟨l,hl⟩)

private theorem core_center_central_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B)
    (hc : (center (pCore 2 B)).map (pCore 2 B).subtype ≤ center B) :
    (center (pCore 2 A)).map (pCore 2 A).subtype ≤ center A := by
  let q : pCore 2 A ≃* pCore 2 B :=
    (e.subgroupMap (pCore 2 A)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  rintro _ ⟨z,hz,rfl⟩
  have hqz : q z ∈ center (pCore 2 B) := (centerCongr q ⟨z,hz⟩).property
  have hez : e (z : A) ∈ center B := hc ⟨q z,hqz,rfl⟩
  have hz' : e.symm (e (z : A)) ∈ center A :=
    (centerCongr e.symm ⟨e (z : A),hez⟩).property
  simpa only [MulEquiv.symm_apply_apply,Subgroup.subtype_apply] using hz'

/-- The original moved central module excludes the short native local
factor over every finite field of characteristic two. -/
theorem original_context_not_g2_short_local_equiv
    (d : Context T L V V₁ V₂ V₃)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : L ≃* local₁ (F := F)) : False :=
  original_core_center_not_central d
    (core_center_central_of_equiv e local₁_core_center_le_center)

private theorem not_g2_short_endpoint
    {A : Fin 2 → Subgroup G} (j : Fin 2)
    (d : Context T (A j) V V₁ V₂ V₃)
    (h : HypothesisF11 A (T : Subgroup G))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F)
    (e : parabolic A (SuzukiContainment.reducedSylow A (T : Subgroup G)) j ≃*
      parabolic₁ (F := F)) : False := by
  let P := parabolic A (SuzukiContainment.reducedSylow A (T : Subgroup G)) j
  have hAP : A j ≤ P := le_sup_left.trans le_sup_left
  have hcore : pCore 2 (parabolic₁ (F := F)) ≤
      solvableResidual (parabolic₁ (F := F)) := by
    apply (map_le_map_iff_of_injective (parabolic₁ (F := F)).subtype_injective).mp
    rw [HigherFieldResiduals.parabolic₁_residual hq]
    change (parabolic₁ (F := F)).pCoreIn 2 ≤ local₁
    rw [parabolic₁_pCore,←local₁_pCore]
    exact map_subtype_le _
  have hm := A5PairCatalogue.local_marking_of_reduced_equiv h j d.quotient e hcore
  let a : A j ≃* solvableResidual (parabolic₁ (F := F)) :=
    (subgroupOfEquivOfLe hAP).symm.trans
      ((e.subgroupMap ((A j).subgroupOf P)).trans (MulEquiv.subgroupCongr hm))
  let b : solvableResidual (parabolic₁ (F := F)) ≃* local₁ (F := F) :=
    ((solvableResidual (parabolic₁ (F := F))).equivMapOfInjective
      (parabolic₁ (F := F)).subtype (parabolic₁ (F := F)).subtype_injective).trans
        (MulEquiv.subgroupCongr (HigherFieldResiduals.parabolic₁_residual hq))
  exact original_context_not_g2_short_local_equiv d F (a.trans b)

/-- An actual native reduced G₂ comparison is incompatible with the two
original Contexts, in either orientation. -/
theorem original_pair_not_reduced_g2
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (h : HypothesisF11 ![L,K] (T : Subgroup G))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (short : Bool)
    (c : Iso (reducedAmalgam ![L,K] (T : Subgroup G)) (G2Native.amalgam F short)) :
    False := by
  have hq : 2 < Nat.card F := by
    by_contra hgt
    have htwo : Nat.card F = 2 := by
      have := Finite.one_lt_card (α := F)
      omega
    let := Chapter6.Source.RankOneGeneric.Global.G2Short.parabolic_solvable_of_card_two htwo
    cases short
    · let f : _ ≃* parabolic₁ (F := F) := c.right
      exact A5PairCatalogue.overgroup_not_solvable (L := ![L,K]) 1 e.quotient
        (le_sup_left.trans le_sup_left)
        (Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective)
    · let f : _ ≃* parabolic₁ (F := F) := c.left
      exact A5PairCatalogue.overgroup_not_solvable (L := ![L,K]) 0 d.quotient
        (le_sup_left.trans le_sup_left)
        (Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective)
  cases short
  · exact not_g2_short_endpoint 1 e h F hq c.right
  · exact not_g2_short_endpoint 0 d h F hq c.left

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
