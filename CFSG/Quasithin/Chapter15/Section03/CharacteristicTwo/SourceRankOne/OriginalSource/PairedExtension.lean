module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.PairedMaps
public import Theory.SpecificGroups.SymmetricEight.FourBlockQuotientExtension

/-!
The larger Sylow-image alternative in the actual quotient XT/O₂(XT).
The normal image of XS has index dividing two and is identified with the
four-block stabilizer modulo its two-core. Its characteristic elementary
three-core then gives the faithful GL₂(3) Sylow action, by the concrete
four-block extension theorem. No abstract Sylow-extension premise remains.

Source: [AS, 15.3.25], printed pp.1133–1134.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterB.Offenders.Eight
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open RankOneConfiguration EightGeometry PairedQuotient PairedOffenders
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}
namespace EndNodeData
variable (e : EndNodeData d I c)
  (hn : ∀ i : I, e.marking.equiv (d.starMap I i) = e.action.actor i)
  (hL : c.L = RankOne.threeResidualIn
    (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)))
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (htS : t ∉ d.S)
local notation "b" => e.pairedConfiguration hL t ht htS
include hn
local notation "Q" => PairedOffenders.Configuration.q b inf_le_left

theorem paired_extension
    (first : SylowCoordinates (b).S (b).f Q)
    (hne : (b).S.map Q ≠ PairedOffenders.Configuration.Timage b) :
    ∃ P : Sylow 2 (GL (Fin 2) (ZMod 3)),
      Nonempty (PairedOffenders.Configuration.Timage b ≃* P) := by
  let Y := XT d (RankOne.threeResidualIn (centralizer (d.ZS : Set G)))
  let π := PairedOffenders.quotientMap d (RankOne.threeResidualIn (centralizer (d.ZS : Set G)))
  let J := (b).J.subgroupOf Y
  have hST : d.S ≤ (d.T : Subgroup G) := inf_le_left
  have hJY : (b).J ≤ Y := sup_le le_sup_left (hST.trans le_sup_right)
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hTJ := residual_join_normalized_by_sylow d hi
  have hnJ : Y ≤ normalizer ((b).J : Set G) :=
    sup_le (le_sup_left.trans le_normalizer) hTJ
  let : J.Normal := normal_subgroupOf_of_le_normalizer hnJ
  let N := J.map π
  let : N.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have hN : N = (Q).range := by
    change J.map π = (π.comp (inclusion hJY)).range
    rw [MonoidHom.range_comp,inclusion_range]
  have hJi : J.index ∣ 2 := by
    let T₀ := (d.T : Subgroup G).subgroupOf Y
    have hsup : J ⊔ T₀ = ⊤ := by
      apply map_injective Y.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hJY,
        map_subgroupOf_eq_of_le (show (d.T : Subgroup G) ≤ Y from le_sup_right),
        ←MonoidHom.range_eq_map,range_subtype]
      change (_ ⊔ d.S) ⊔ (d.T : Subgroup G) = _ ⊔ (d.T : Subgroup G)
      rw [sup_assoc,sup_eq_right.mpr hST]
    have hd : J.relIndex T₀ ∣ (d.S.subgroupOf Y).relIndex T₀ :=
      relIndex_dvd_of_le_left T₀ (comap_mono (show d.S ≤ (b).J from le_sup_right))
    have he : (d.S.subgroupOf Y).relIndex T₀ = d.S.relIndex (d.T : Subgroup G) :=
      relIndex_subgroupOf (show (d.T : Subgroup G) ≤ Y from le_sup_right)
    rw [he] at hd
    change J.relIndex T₀ ∣ (d.S.subgroupOf (d.T : Subgroup G)).index at hd
    rw [hi] at hd
    rwa [←relIndex_sup_left,hsup,relIndex_top_right] at hd
  have hNi : N.index ∣ 2 := (J.index_map_dvd (QuotientGroup.mk'_surjective _)).trans hJi
  let f := (b).f
  have hfr : f.range = parabolic := e.paired_first_range hn hL t ht htS
  let r : (b).J →* parabolic := f.codRestrict parabolic (fun x => hfr.le ⟨x,rfl⟩)
  have hr : Function.Surjective r := by
    intro y
    have hy : (y : Perm) ∈ f.range := hfr.symm ▸ y.property
    obtain ⟨x,hx⟩ := hy
    exact ⟨x,Subtype.ext hx⟩
  have hkr : IsPGroup 2 r.ker := by
    rw [show r.ker = f.ker from MonoidHom.ker_codRestrict _ _ _]
    exact e.paired_first_kernel_isTwo hL t ht htS
  let a := (QuotientGroup.mk' (pCore 2 parabolic)).comp r
  have ha : a.ker = (b).P := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact r.comap_pCore_of_ker_isPGroup hr hkr
  let v : (Q).range ≃* (parabolic ⧸ pCore 2 parabolic) :=
    (QuotientGroup.quotientKerEquivRange Q).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq
        ((e.paired_core_kernel hL t ht htS).trans ha.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective a ((QuotientGroup.mk'_surjective _).comp hr)))
  let vN : N ≃* (parabolic ⧸ pCore 2 parabolic) := (MulEquiv.subgroupCongr hN).trans v
  let P := (d.T.subtype (show (d.T : Subgroup G) ≤ Y from le_sup_right)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 Y))
  have hP : (P : Subgroup (Y ⧸ pCore 2 Y)) = PairedOffenders.Configuration.Timage b := by
    rw [Sylow.coe_mapSurjective,Sylow.coe_subtype]
  have h8 : Nat.card ((b).S.map Q) = 8 :=
    (Nat.card_congr first.quotientEquiv.toEquiv).trans card_quotient
  have hPlt : 8 < Nat.card P := by
    have hle := PairedOffenders.Configuration.Simage_le_Timage b hST
    have hc := Subgroup.card_le_of_le hle
    have hncard : Nat.card ((b).S.map Q) ≠ Nat.card (PairedOffenders.Configuration.Timage b) := by
      intro hc
      exact hne (eq_of_le_of_card_ge hle hc.ge)
    have hpc : Nat.card P = Nat.card (PairedOffenders.Configuration.Timage b) :=
      Nat.card_congr (MulEquiv.subgroupCongr hP).toEquiv
    omega
  obtain ⟨R,⟨vR⟩⟩ := Theory.SpecificGroups.SymmetricEight.FourBlockQuotient.sylow_equiv_GL2_three
    N hNi (pCore_quotient_pCore_eq_bot 2) vN P hPlt
  exact ⟨R,⟨(MulEquiv.subgroupCongr hP).symm.trans vR⟩⟩
end EndNodeData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
