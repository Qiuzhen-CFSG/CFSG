module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.RootGeometry
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.NaturalThompson
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import Theory.GroupTheory.CharacteristicTwoCentralLayerSylow
public import Theory.GroupTheory.NormalSylowQuotientAction

/-!
# The central line of the prepared maximal linear row

The faithful quotient action on an affine root plane identifies the Sylow
centralizer of Z(S) with S itself: pointwise fixation of the natural fixed
line kills the field coefficient, and a linear two-element lies in SL₂.
Even characteristic passes from N_G(Z(S)) to C_G(Z(S)). Since S/Z(S) is
abelian, the central-layer core theorem gives O₂(C_G(Z(S))) = S. Normalizer
functoriality then identifies N_G(Z(S)) with N_G(S), the full intersection
of the source factor normalizers.

This proves source §5.3.5 for the original prepared row in either orientation,
including q=4. The individual involution-centralizer bound in §5.3.7 and
the full-normalizer realization and ambient recognition remain separate.
Source: Aschbacher–Smith 5.3.1 and 5.3.5, printed pp.658–660
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

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

/-- In the original ambient Sylow, the centralizer of Z(S) is exactly S. -/
theorem Preparation.linear_sylow_center_centralizer :
    (T : Subgroup G) ⊓ centralizer (centerIn (sourceS L H) : Set G) = sourceS L H := by
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
  have hs := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he
  have hS : sourceS L H = (T : Subgroup G) ⊓ L := by
    rw [← d.left_intersection,inf_eq_left.mpr (show sourceS L H ≤ L from hs 0)]
  let P := T.subtype h.sylow_normalizes
  have hfix := Matrix.PSL3.LinearAmbientGeometry.sylow_center_centralizer_eq X e hq hCX P
  refine le_antisymm ?_ (le_inf hST (le_centralizer_iff.mp inf_le_right))
  intro x hx
  have hxM : x ∈ M := h.sylow_normalizes hx.1
  have hx' : (⟨x,hxM⟩ : M) ∈ (P : Subgroup M) ⊓
      centralizer (centerIn ((P : Subgroup M) ⊓ X) : Set M) := by
    refine ⟨hx.1,?_⟩
    intro z hz
    apply Subtype.ext
    apply hx.2
    refine ⟨hS.symm ▸ hz.1,?_⟩
    intro s hsS
    have hsTL := hS ▸ hsS
    exact congrArg M.subtype (hz.2 ⟨s,h.sylow_normalizes hsTL.1⟩ hsTL)
  have hxL : x ∈ L := (hfix ▸ hx').2
  exact hS.symm ▸ ⟨hx.1,hxL⟩

/-- The actual center centralizer has two-core S, the key core calculation
in source §5.3.5. -/
theorem Preparation.linear_center_centralizer_core :
    (centralizer (centerIn (sourceS L H) : Set G)).pCoreIn 2 = sourceS L H := by
  let S := sourceS L H
  let Z := centerIn S
  let C := centralizer (Z : Set G)
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have hgeo := d.linear_involution_geometry h hH hp F hm hF he hmax
  have hs := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he
  have hS : S = (T : Subgroup G) ⊓ L := by
    rw [← d.left_intersection,inf_eq_left.mpr (show S ≤ L from hs 0)]
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) := by
    rw [hS]
    exact (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
      inf_normalizer_le_normalizer_inf
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) := by
    change (T : Subgroup G) ≤ normalizer (centerIn S : Set G)
    rw [centerIn_eq_map_center]
    exact hTS.trans (normalizer_le_normalizer_characteristic_image S (center S))
  have hZS : Z ≤ S := inf_le_left
  have hZp : IsPGroup 2 Z := T.isPGroup'.to_le (hZS.trans hST)
  have hZne : Z ≠ ⊥ := by
    apply Z.one_lt_card_iff_ne_bot.mp
    change 1 < Nat.card (centerIn S)
    rw [centerIn_eq_map_center,card_map_of_injective S.subtype_injective,hgeo.2.1]
    exact Finite.one_lt_card
  have hcharN : normalizer (Z : Set G) ∈ Chapter1.He G :=
    Chapter1.twoLocal_mem_He_of_sylow_le T (h.qtke.evenCharacteristic T)
      ⟨Z,hZne,hZp,rfl⟩ hTZ
  have hcharC : C ∈ Chapter1.He G := by
    change C ⊓ centralizer (C.pCoreIn 2 : Set G) ≤ C.pCoreIn 2
    have hh := pCoreIn_selfCentralizing_centralizer hcharN hZp Z.le_normalizer
    simpa only [C,inf_eq_right.mpr (centralizer_le_normalizer (Z : Set G))] using hh
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T C
    (hTZ.trans (normalizer_le_normalizer_centralizer Z))
  have hTC : (T : Subgroup G) ⊓ C = S :=
    d.linear_sylow_center_centralizer h hH hp F hm hF he hmax
  have hPS : (P : Subgroup C).map C.subtype = S := by
    rw [hP,subgroupOf_map_subtype,hTC]
  have hSC : S ≤ C := hTC ▸ inf_le_right
  have hZC : Z ≤ C := hZS.trans hSC
  have hZcentral : Z.subgroupOf C ≤ center C := by
    intro z hz
    exact mem_center_iff.mpr fun c => Subtype.ext (c.property z hz).symm
  let : (Z.subgroupOf C).Normal :=
    normal_subgroupOf_of_le_normalizer (centralizer_le_normalizer (Z : Set G))
  have hZcore : Z.subgroupOf C ≤ pCore 2 C :=
    le_sSup ⟨inferInstance,hZp.comap_subtype⟩
  have hcommS : ⁅S,S⁆ ≤ Z := by
    have hh : _root_.commutator S ≤ center S :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hgeo.2.2.1
    have hm := map_mono (f := S.subtype) hh
    change ⁅S,S⁆ ≤ centerIn S
    rw [centerIn_eq_map_center]
    simpa only [_root_.commutator_def,map_commutator,← MonoidHom.range_eq_map,range_subtype] using hm
  have hcomm : ⁅(P : Subgroup C),(P : Subgroup C)⁆ ≤ Z.subgroupOf C := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,hPS]
    exact hcommS
  have hPc := sylow_two_eq_pCore_of_commutator_le_central_layer P (Z.subgroupOf C)
    hZcore hZcentral (Chapter1.mem_He_iff.mp hcharC) hcomm
  exact (congrArg (fun U : Subgroup C => U.map C.subtype) hPc).symm.trans hPS

/-- Source §5.3.5: the original central line and S have the same ambient
normalizer, namely the whole intersection of the two factor normalizers. -/
theorem Preparation.linear_center_normalizer :
    normalizer (centerIn (sourceS L H) : Set G) =
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  have hcore := d.linear_center_centralizer_core h hH hp F hm hF he hmax
  have hcomp : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) := .linear F m hm hF he
  have hl := d.normalizer_local_conditions h hH hmax rfl
    (d.common_sylow_of_comparison h hH.1.1.2 hp hcomp)
    (d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp hcomp)
  have hs := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he
  have hS : sourceS L H = (T : Subgroup G) ⊓ L := by
    rw [← d.left_intersection,inf_eq_left.mpr (show sourceS L H ≤ L from hs 0)]
  have hnS : normalizer (sourceS L H : Set G) =
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
    rw [hS]
    exact hl.normalizer_eq_middle
  rw [← hnS]
  apply le_antisymm
  · have hn := (normalizer_le_normalizer_centralizer (centerIn (sourceS L H))).trans
      (normalizer_le_normalizer_characteristic_image
        (centralizer (centerIn (sourceS L H) : Set G))
        (pCore 2 (centralizer (centerIn (sourceS L H) : Set G))))
    change normalizer (centerIn (sourceS L H) : Set G) ≤
      normalizer ((centralizer (centerIn (sourceS L H) : Set G)).pCoreIn 2 : Set G) at hn
    rwa [hcore] at hn
  · rw [centerIn_eq_map_center]
    exact normalizer_le_normalizer_characteristic_image (sourceS L H) (center (sourceS L H))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
