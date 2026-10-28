module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinarySolvableBorel
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalBender
public import CFSG.Quasithin.MainConverse.RankOneLocal
public import CFSG.Quasithin.MainConverse.SuzukiEven

/-!
# The actual original marked Borel for a Bender component

Native model rank-one geometry makes every proper full-Sylow overgroup
solvable. Native even characteristic gives characteristic two of the full
Borel. The original local characteristic-normalizer and residual-normalizer
controls therefore identify the same marked intersection with that Borel.
No ambient generation or global residual-centralization premise is used.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]

private theorem raw_bender_simple {X : Type*} [Group X]
    (hm : ClassificationModels.IsBenderModel X) : IsSimpleGroup X := by
  have hfour {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2^n :=
    (by norm_num : 4 = 2^2) ▸ Nat.pow_le_pow_right (by decide) hn
  cases hm with
  | linear n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F) (hF ▸ hfour hn)
    exact e.isSimpleGroup
  | unitary n hn hm =>
    obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    have hf := ChapterF.Source.Unitary.fixed_card J n (by omega) hF hc
    let := BenderSuzuki.External.huppert_II_10_13 J (2^n)
      (by have := hfour hn; omega) hF hf
    exact e.isSimpleGroup
  | suzuki m hm he =>
    obtain ⟨e⟩ := he
    let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
    exact e.isSimpleGroup

private theorem raw_bender_evenCharacteristic {X : Type*} [Group X] [Finite X]
    [IsSimpleGroup X] (hna : ¬ IsMulCommutative X)
    (hm : ClassificationModels.IsBenderModel X) : IsEvenCharacteristic X := by
  cases hm with
  | linear n hn hm => exact MainConverse.psl2_evenCharacteristic hna hn hm
  | unitary n hn hm => exact MainConverse.psu3_evenCharacteristic hna hn hm
  | suzuki m hm he =>
    obtain ⟨e⟩ := he
    exact MainConverse.suzuki_evenCharacteristic_of_iso hm e

private theorem raw_bender_borel_characteristicTwo
    (S L : Subgroup G) [IsQuasisimple L] [IsSimpleGroup L]
    (hSyl : Chapter1.IsSylowIn 2 (S ⊓ L) L)
    (hm : ClassificationModels.IsBenderModel L) :
    HasCharacteristicTwo ((normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype) := by
  obtain ⟨P,hP⟩ := hSyl
  have hP' : (P : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  let B0 := normalizer (P : Set L)
  have hf := ChapterE.Structure.bender_sylow_facts hm P
  have hPne : (P : Subgroup L) ≠ ⊥ := by
    intro he
    have hh := hf.proper.ne
    change normalizer ((P : Subgroup L) : Set L) ≠ ⊤ at hh
    rw [he] at hh
    exact hh (normalizer_eq_top (⊥ : Subgroup L))
  obtain ⟨K,hBK,hK⟩ := Finite.exists_le_maximal
    (show IsTwoLocal B0 from ⟨P,hPne,P.isPGroup',rfl⟩)
  have hKB : K ≤ B0 := hf.unique_maximal K ((P : Subgroup L).le_normalizer.trans hBK)
    (lt_top_iff_ne_top.mpr (twoLocal_ne_top_of_nonabelian_simple
      (Group.IsPerfect.not_isMulCommutative L) hK.1))
  have hb : HasCharacteristicTwo B0 := by
    have he := le_antisymm hKB hBK
    rw [←he]
    exact raw_bender_evenCharacteristic (Group.IsPerfect.not_isMulCommutative L) hm
      P K hK ((P : Subgroup L).le_normalizer.trans hBK)
  have hh := hb.of_equiv (B0.equivMapOfInjective L.subtype L.subtype_injective)
  change HasCharacteristicTwo ((normalizer ((P : Subgroup L) : Set L)).map L.subtype) at hh
  rwa [hP'] at hh

/-- The original marked intersection in an actual Bender component is its
full Borel, using the literal local controls and component escape. -/
theorem PreparedChosenModule.raw_ordinary_bender_borel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G)) (L.subgroupOf (centralizer (Z1 : Set G))))
    (hSylG : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hSylL : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hcontrol : ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 (centralizer (Z1 : Set G) ⊓ Mc : Subgroup G)).map
      (centralizer (Z1 : Set G) ⊓ Mc).subtype : Set G) ≤ Mc)
    (hout : ¬ L ≤ centralizer (Z1 : Set G) ⊓ Mc)
    (hm : ClassificationModels.IsBenderModel L) :
    ((centralizer (Z1 : Set G) ⊓ Mc) ⊓ L) =
      (normalizer ((((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L).subgroupOf L : Set L)).map
        L.subtype := by
  let := h.elementary
  let : IsQuasisimple (L.subgroupOf (centralizer (Z1 : Set G))) := hL.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLG)
  let : IsSimpleGroup L := raw_bender_simple hm
  let H := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ H
  let A := (H ⊓ Mc) ⊓ L
  let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
  have hSM : S ≤ H ⊓ Mc := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact ⟨hx.2,hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz x hx.1).symm)⟩
  obtain ⟨P,hP⟩ := hSylL
  have hP' : (P : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  have hf := ChapterE.Structure.bender_sylow_facts hm P
  have hproper : A.subgroupOf L < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    apply hout
    intro x hx
    have hh : (⟨x,hx⟩ : L) ∈ A.subgroupOf L := he ▸ mem_top _
    exact hh.1
  have hPA : (P : Subgroup L) ≤ A.subgroupOf L := by
    intro x hx
    have hh := hP ▸ mem_map_of_mem L.subtype hx
    exact ⟨hSM hh.1,hh.2⟩
  have hsol : Group.IsSolvable A := by
    let : Group.IsSolvable (normalizer (P : Set L)) := hf.solvable
    let : Group.IsSolvable (A.subgroupOf L) := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (hf.unique_maximal _ hPA hproper))
    exact Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe (show A ≤ L from inf_le_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show A ≤ L from inf_le_right)).surjective
  have hc : SolvableSylowControl 2 L := by
    intro Q D hD hQD
    let := hD
    have hnot : ¬ Group.IsSolvable L := Group.IsPerfect.not_isSolvable L
    have hDproper : D < ⊤ := by
      apply lt_top_iff_ne_top.mpr
      intro he
      subst D
      exact hnot (Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := L)).toMonoidHom)
        (Subgroup.topEquiv (G := L)).surjective)
    exact (ChapterE.Structure.bender_sylow_facts hm Q).unique_maximal
      D hQD hDproper
  exact raw_ordinary_solvable_borel_eq H Mc S L
    (caseI_centralizer_sqtk hG Z1 hZne ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left)))
    hSM (T.isPGroup'.to_le inf_le_left) hSylG hLG hL ⟨P,hP⟩ hcontrol hbound hsol hc
    (raw_bender_borel_characteristicTwo S L ⟨P,hP⟩ hm)

end CFSG.Quasithin.Chapter15.Section01
