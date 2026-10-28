module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.RootGeometry
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.NaturalThompson
public import Stellmacher.ElementaryAbelianMaxOrder

/-!
# The Thompson subgroup and weak closure in the prepared linear row

The affine natural-module offender theorem puts every maximum elementary
subgroup of T inside S. The UT₃ coordinates then identify that family as the
two source cores. Their join is S = J(T). Burnside fusion for the normal pair
proves each plane weakly closed in T with respect to the original ambient G.
Both orientations and q=4 are retained, and no full-normalizer realization is
assumed in this argument.

Source: Aschbacher–Smith 5.3.6(1) and the preceding Thompson calculation,
printed p.660, using B.4.2(1), printed p.86 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem maxFamily_subgroupOf (E T N : Subgroup G)
    (hE : E ∈ elementaryAbelianMaxSubgroups T) (hEN : E ≤ N) :
    E.subgroupOf N ∈ elementaryAbelianMaxSubgroups (T.subgroupOf N) := by
  let := hE.2.1
  refine ⟨fun x hx => hE.1 hx,IsElementaryAbelian.subgroupOf hEN,?_⟩
  intro B hB he
  have hBT : B.map N.subtype ≤ T := by rintro _ ⟨b,hb,rfl⟩; exact hB hb
  have hh := hE.2.2 (B.map N.subtype) hBT (he.map N.subtype)
  rw [card_map_of_injective N.subtype_injective] at hh
  exact hh.trans_eq (Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv).symm

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax

/-- Natural-module offenders force every maximum elementary subgroup of the
original Sylow T into the original common factor Sylow S. -/
theorem Preparation.linear_maxElementary_le_sourceS
    (E : Subgroup G) (hE : E ∈ elementaryAbelianMaxSubgroups (T : Subgroup G)) :
    E ≤ sourceS L H := by
  have ha : Nonempty (L ≃* Matrix.SL2.Affine F) := by
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 0 true e.left).2.1
      exact ⟨a.trans (Matrix.PSL3.LinearThree.pointLocalEquivAffine F)⟩
    · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 0 false e.left).2.1
      exact ⟨a.trans (Matrix.PSL3.LinearThree.lineLocalEquivAffine F)⟩
  obtain ⟨a⟩ := ha
  have hc := d.linear_core_structure h hH hp F hm hF he
  have hC := (d.linear_root_centralizers h hH hp F hm hF he hmax).1
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  let M := normalizer (L : Set G)
  let X := L.subgroupOf M
  let : X.Normal := normal_subgroupOf_of_le_normalizer (show M ≤ normalizer (L : Set G) from le_rfl)
  let e : X ≃* Matrix.SL2.Affine F := (subgroupOfEquivOfLe L.le_normalizer).trans a
  have hV : (X.pCoreIn 2).map M.subtype = L.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 X M.subtype M.subtype_injective]
    change (L.subgroupOf M |>.map M.subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le L.le_normalizer]
  have hCX : centralizer (X.pCoreIn 2 : Set M) = X.pCoreIn 2 := by
    apply le_antisymm
    · intro x hx
      have hh : (x : G) ∈ centralizer (L.pCoreIn 2 : Set G) := by
        rw [← hV]
        rintro _ ⟨y,hy,rfl⟩
        exact congrArg M.subtype (hx y hy)
      have hxV := hC.le hh
      rw [← hV] at hxV
      exact (mem_map_iff_mem M.subtype_injective).mp hxV
    · intro x hx y hy
      apply Subtype.ext
      exact hC.ge (hV ▸ mem_map_of_mem M.subtype hx) y (hV ▸ mem_map_of_mem M.subtype hy)
  have hq : 2 < Nat.card F := by
    rw [hF,hc.1]
    exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) h.exponent
  have hVS : X.pCoreIn 2 ≤ (T : Subgroup G).subgroupOf M := by
    intro x hx
    exact hST ((hc.2.2 0).2.2 (hV ▸ mem_map_of_mem M.subtype hx))
  have hEM : E ≤ M := hE.1.trans h.sylow_normalizes
  have hle := Matrix.PSL3.LinearAmbientGeometry.maxElementary_le_affine X e hq hCX
    ((T : Subgroup G).subgroupOf M) (E.subgroupOf M) hVS
    (maxFamily_subgroupOf E T M hE hEM)
  have hEL : E ≤ L := fun x hx => hle (show (⟨x,hEM hx⟩ : M) ∈ E.subgroupOf M from hx)
  have hs := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he
  have hS : sourceS L H = (T : Subgroup G) ⊓ L := by
    rw [← d.left_intersection,inf_eq_left.mpr (show sourceS L H ≤ L from hs 0)]
  exact (le_inf hE.1 hEL).trans_eq hS.symm

/-- The original ambient Sylow has exactly the two source planes as its
maximum elementary abelian subgroups, including field four. -/
theorem Preparation.linear_maxElementary_pair :
    elementaryAbelianMaxSubgroups (T : Subgroup G) =
      {L.pCoreIn 2,(residual H).pCoreIn 2} := by
  have hc := (d.linear_core_structure h hH hp F hm hF he).2.2
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have hVT (i : Fin 2) : (![L,residual H] i).pCoreIn 2 ≤ (T : Subgroup G) :=
    (hc i).2.2.trans hST
  have hmaxOnly (E : Subgroup G) (hE : E ∈ elementaryAbelianMaxSubgroups (T : Subgroup G)) :
      E = L.pCoreIn 2 ∨ E = (residual H).pCoreIn 2 := by
    apply d.linear_large_elementary_in_sourceS h hH hp F hm hF he hmax E hE.2.1
      (d.linear_maxElementary_le_sourceS h hH hp F hm hF he hmax E hE)
    rw [← (hc 0).2.1]
    exact hE.2.2 _ (hVT 0) (hc 0).1
  obtain ⟨D,hD⟩ := elementaryAbelianMaxSubgroups_nonempty (T : Subgroup G)
  have hDc : Nat.card D = Nat.card F ^ 2 := by
    rcases hmaxOnly D hD with rfl | rfl
    · exact (hc 0).2.1
    · exact (hc 1).2.1
  have hmem (i : Fin 2) : (![L,residual H] i).pCoreIn 2 ∈
      elementaryAbelianMaxSubgroups (T : Subgroup G) := by
    refine ⟨hVT i,(hc i).1,?_⟩
    intro E hET helem
    exact (hD.2.2 E hET helem).trans_eq (hDc.trans (hc i).2.1.symm)
  ext E
  change E ∈ elementaryAbelianMaxSubgroups (T : Subgroup G) ↔
    E = L.pCoreIn 2 ∨ E = (residual H).pCoreIn 2
  constructor
  · exact hmaxOnly E
  · rintro (rfl | rfl)
    · exact hmem 0
    · exact hmem 1

/-- Source §5.3.6(1): both original root planes are weakly closed in T with
respect to G. The pair action uses the two-residual through the proved fusion lemma. -/
theorem Preparation.linear_root_planes_weakly_closed :
    ∀ V ∈ ({L.pCoreIn 2,(residual H).pCoreIn 2} : Set (Subgroup G)), ∀ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      V.map (MulAut.conj g).toMonoidHom = V := by
  have hc := (d.linear_core_structure h hH hp F hm hF he).2.2
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have hpair := d.linear_maxElementary_pair h hH hp F hm hF he hmax
  have hA : ∀ V ∈ ({L.pCoreIn 2,(residual H).pCoreIn 2} : Set (Subgroup G)), ∀ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      V.map (MulAut.conj g).toMonoidHom ∈ ({L.pCoreIn 2,(residual H).pCoreIn 2} : Set (Subgroup G)) := by
    intro V hV g hg
    have hVm : V ∈ elementaryAbelianMaxSubgroups (T : Subgroup G) := hpair ▸ hV
    let := hVm.2.1
    rw [← hpair]
    refine ⟨hg,IsElementaryAbelian.map _,?_⟩
    intro E hET hEl
    exact (hVm.2.2 E hET hEl).trans_eq (card_map_of_injective (MulAut.conj g).injective).symm
  exact Chapter5.Section03.weakly_closed_normal_pair T _ _
    (d.linear_root_normalizers h hH hp F hm hF he hmax).2.2
    ((hc 0).2.2.trans hST) ((hc 1).2.2.trans hST)
    (h.sylow_normalizes.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    ((hH.1.1.2.trans (le_normalizer_residual H)).trans
      (normalizer_le_normalizer_characteristic_image (residual H) (pCore 2 (residual H)))) hA

/-- The original S is the elementary Thompson subgroup of the ambient Sylow. -/
theorem Preparation.linear_sourceS_eq_thompson :
    sourceS L H = elementaryAbelianMaxJ (T : Subgroup G) := by
  change sourceS L H = sSup (elementaryAbelianMaxSubgroups (T : Subgroup G))
  rw [d.linear_maxElementary_pair h hH hp F hm hF he hmax,sSup_pair]
  exact d.linear_sourceS_eq_sup_cores h hH hp F hm hF he hmax

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
