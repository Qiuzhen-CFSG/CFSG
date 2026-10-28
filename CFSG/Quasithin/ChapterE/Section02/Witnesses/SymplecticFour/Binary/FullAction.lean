module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.NormalElementaryPlacement
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.Binary.NaturalExtension
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.MarkedCentralFour

/-!
# Full binary component action from the original normal elementary subgroup

Faithful conjugation embeds the core-free source into Aut(A6). Its Sylow
image contains the inner D8 and escapes natural S6 by minimal parabolicity.
The native normal-elementary calculation then identifies the full Sylow
and the actual central four; order divisibility proves surjectivity.
Source: E.2.7, printed p.219. No full automorphism-image premise is assumed.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
open AlternatingSix.ShadowLocal
open AlternatingSix.ShadowLocal.Identification
local notation "Inn" => AlternatingSix.ShadowLocal.inner

variable {G : Type*} [Group G] [Finite G]

theorem full_action_of_normal_elementary
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup G) [K.Normal] (hK : Nat.card K = 360)
    (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (a : G →* AutA6) (ha : Function.Injective a) (hKa : K.map a = Inn)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hn : (T : Subgroup G) ≤ normalizer (V : Set G)) (hV : 2 < Nat.card V) :
    Function.Surjective a ∧ ∃ P : Sylow 2 AutA6,
      (T : Subgroup G).map a = (P : Subgroup AutA6) ∧
      V.map a = ((Holomorph.centralTwo ⊔ Holomorph.transpositionSubgroup).map
        (sylowEquiv P).toMonoidHom).map (P : Subgroup AutA6).subtype := by
  let S := (T : Subgroup G).map a
  let E := V.map a
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map a
  have hES : E ≤ S := map_mono hVT
  have hnE : S ≤ normalizer (E : Set AutA6) :=
    (map_mono hn).trans (le_normalizer_map a)
  have hE : Nat.card E = Nat.card V := card_map_of_injective ha
  have hgena : Inn ⊔ S = a.range := by
    rw [←hKa,←Subgroup.map_sup,hgen,←MonoidHom.range_eq_map]
  have hout : ¬ S ≤ natural := by
    intro hS
    apply not_minimal_of_natural_extension T a ha
      (hgena ▸ (show Inn ≤ Inn ⊔ S from le_sup_left))
      (hgena ▸ sup_le inner_le_natural hS) hP
  obtain ⟨P,hSP⟩ := (T.isPGroup'.map a).exists_le_sylow
  let e := sylowEquiv P
  let S₀ := (S.subgroupOf (P : Subgroup AutA6)).map e.symm.toMonoidHom
  let E₀ := (E.subgroupOf (P : Subgroup AutA6)).map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 (E.subgroupOf (P : Subgroup AutA6)) :=
    IsElementaryAbelian.subgroupOf (hES.trans hSP)
  let : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.map _
  have hSmap : (S₀.map e.toMonoidHom).map (P : Subgroup AutA6).subtype = S := by
    rw [show S₀.map e.toMonoidHom = S.subgroupOf (P : Subgroup AutA6) from
      e.mapSubgroup.apply_symm_apply _,map_subgroupOf_eq_of_le hSP]
  have hEmap : (E₀.map e.toMonoidHom).map (P : Subgroup AutA6).subtype = E := by
    rw [show E₀.map e.toMonoidHom = E.subgroupOf (P : Subgroup AutA6) from
      e.mapSubgroup.apply_symm_apply _,map_subgroupOf_eq_of_le (hES.trans hSP)]
  have hE₀ : 2 < Nat.card E₀ := by
    rw [show Nat.card E₀ = Nat.card (E.subgroupOf (P : Subgroup AutA6)) from
      card_map_of_injective e.symm.injective,
      Nat.card_congr (subgroupOfEquivOfLe (hES.trans hSP)).toEquiv,hE]
    exact hV
  have hn₀ : S₀ ≤ normalizer (E₀ : Set Holomorph.Model) := by
    have hh : S.subgroupOf (P : Subgroup AutA6) ≤
        normalizer (E.subgroupOf (P : Subgroup AutA6) : Set P) := by
      rw [←subgroupOf_normalizer_eq (hES.trans hSP)]
      exact fun x hx => hnE hx
    exact (map_mono hh).trans (le_normalizer_map _)
  have hout₀ : ¬ S₀ ≤ Holomorph.natural := by
    intro hh
    apply hout
    rw [←hSmap]
    have hm := map_mono (f := (P : Subgroup AutA6).subtype)
      (map_mono (f := e.toMonoidHom) hh)
    rw [sylowEquiv_natural] at hm
    exact hm.trans (map_comap_le _ _)
  obtain ⟨R,hR⟩ := T.exists_subgroupOf_eq_of_normal K
  have hRc : Nat.card R = 8 := by
    rw [R.card_eq_multiplicity,hK]
    decide +kernel
  let F := ((R : Subgroup K).map K.subtype).map a
  have hFc : Nat.card F = 8 := by
    rw [show Nat.card F = Nat.card ((R : Subgroup K).map K.subtype) from card_map_of_injective ha,
      card_map_of_injective K.subtype_injective,hRc]
  have hFS : F ≤ S := by
    apply map_mono
    rw [hR,subgroupOf_map_subtype]
    exact inf_le_left
  have hFI : F ≤ Inn := by
    rw [←hKa]
    exact map_mono (map_subtype_le _)
  have hFEq : F = (sylowInner P).map (P : Subgroup AutA6).subtype := by
    apply eq_of_le_of_card_ge
    · intro x hx
      exact ⟨⟨x,hSP (hFS hx)⟩,hFI hx,rfl⟩
    · rw [card_map_of_injective (P : Subgroup AutA6).subtype_injective,sylowInner_card,hFc]
  have hinnerS : sylowInner P ≤ S.subgroupOf (P : Subgroup AutA6) := by
    intro x hx
    exact hFS (hFEq.symm ▸ mem_map_of_mem (P : Subgroup AutA6).subtype hx)
  have hD₀ : Holomorph.innerD ≤ S₀ := by
    have hh := map_mono (f := e.symm.toMonoidHom) hinnerS
    rw [←sylowEquiv_innerD P] at hh
    change e.mapSubgroup.symm (e.mapSubgroup Holomorph.innerD) ≤ S₀ at hh
    simpa only [e.mapSubgroup.symm_apply_apply] using hh
  have hES₀ : E₀ ≤ S₀ := map_mono (subgroupOf_mono _ hES)
  have hs₀ := Holomorph.normal_elementary_forces_full_sylow S₀ E₀ hD₀ hout₀ hn₀ hES₀ hE₀
  have he₀ := Holomorph.normal_elementary_eq_central_four S₀ E₀ hD₀ hout₀ hn₀ hE₀
  have hS : S = (P : Subgroup AutA6) := by
    rw [←hSmap,hs₀,map_top_of_surjective _ e.surjective,←MonoidHom.range_eq_map,range_subtype]
  have hd1 : 360 ∣ Nat.card a.range := by
    rw [←card_inner]
    exact card_dvd_of_le (hgena ▸ (show Inn ≤ Inn ⊔ S from le_sup_left))
  have hd2 : 32 ∣ Nat.card a.range := by
    rw [←sylow_card P,←hS]
    exact card_dvd_of_le (hgena ▸ (show S ≤ Inn ⊔ S from le_sup_right))
  have hd : 1440 ∣ Nat.card a.range := by
    have hh := Nat.lcm_dvd hd1 hd2
    norm_num [Nat.lcm] at hh
    exact hh
  have ht : a.range = ⊤ := eq_of_le_of_card_ge (show a.range ≤ ⊤ from le_top) (by
    rw [card_top,card_aut]
    exact Nat.le_of_dvd Nat.card_pos hd)
  refine ⟨MonoidHom.range_eq_top.mp ht,P,hS,?_⟩
  change E = _
  rw [←hEmap,he₀]
end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary

namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
open Subgroup Theory.GroupTheory AlternatingSix.ShadowLocal
open AlternatingSix.ShadowLocal.BinaryWitness
variable {G : Type*} [Group G] [Finite G]

theorem coreFree_full_action
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hcore : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup G) [K.Normal] [IsSimpleGroup K] (hKa : ¬ IsMulCommutative K)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (eK : K ≃* alternatingGroup (Fin 6))
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hn : (T : Subgroup G) ≤ normalizer (V : Set G)) (hV : 2 < Nat.card V) :
    ∃ e : G ≃* AutA6, ∃ P : Sylow 2 AutA6,
      (T : Subgroup G).map e.toMonoidHom = (P : Subgroup AutA6) ∧
      V.map e.toMonoidHom = markedFour P ∧
      K.map e.toMonoidHom = AlternatingSix.ShadowLocal.inner := by
  have hc := (Structure.Sporadic.faithful_normal_structure T hP hcore K hKa hgen).2
  let a : G →* AutA6 := (MulAut.congr eK).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have ha : Function.Injective a := (MulAut.congr eK).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot K hc)
  have hact (k : K) : a k = MulAut.conj (eK k) := by
    change MulAut.congr eK (MulAut.conjNormal (k : G)) = _
    rw [MulAut.conjNormal_val,MulAut.congr_conj]
  have hi : K.map a = AlternatingSix.ShadowLocal.inner := by
    ext x
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨eK ⟨k,hk⟩,(hact ⟨k,hk⟩).symm⟩
    · rintro ⟨k,rfl⟩
      exact ⟨eK.symm k,(eK.symm k).property,(hact (eK.symm k)).trans
        (congrArg MulAut.conj (eK.apply_symm_apply k))⟩
  have hK : Nat.card K = 360 := (Nat.card_congr eK.toEquiv).trans card_A6
  obtain ⟨hs,P,hT,hE⟩ := full_action_of_normal_elementary T hP K hK hgen a ha hi V hVT hn hV
  refine ⟨MulEquiv.ofBijective a ⟨ha,hs⟩,P,hT,?_,hi⟩
  rw [markedFour_def]
  exact hE
end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
