module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductBaumannSylow
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductNormalized
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootPairEnvelope
public import Theory.SpecificGroups.SymplecticFour.Sylow.RootSylowGeneration
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.GroupTheory.SylowCharacteristicKernelLifting

/-!
# Characteristic-normal exclusion for the original Baumann-Sylow group

Retain the constructed F₀ and its original Baumann Sylow. Its Sylow is
nonnormal because its quotient is SL₂. In full-Sylow normalized coordinates,
its Sylow image lies in the central long root, so F₀ and the full Sylow
preimage generate the original vertex stabilizer. The latter normalizes
the edge and every characteristic subgroup of its Baumann subgroup.
A characteristic Sylow subgroup normal in F₀ is thus normal at both ends
of the edge; the replacement characteristic condition makes it trivial.

This discharges the characteristic-normal premise before the Niles
application in MS93 (5.1), printed p.913, for the same F₀, envelope,
residual and original field degree. Arbitrary-degree Niles, the subsequent
selected-path and terminal arguments, and the distance-two witness remain
unproved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same Baumann-Sylow witness satisfies the characteristic-normal
exclusion, retaining its envelope, whole residual and original field degree. -/
theorem Input.replacement_root_product_F0_noCharacteristicNormal
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (E₁ E₂ : Subgroup (FreeAmalgam d.radical))
    (hE₁ : E₁ ≤ Q d.radical t) (hE₂ : E₂ ≤ Q d.radical t)
    (hc₁ : (Q d.radical a).relIndex E₁ = Nat.card F)
    (hc₂ : (Q d.radical a).relIndex E₂ = Nat.card F)
    (hi₁ : (centralizer (E₁ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hi₂ : (centralizer (E₂ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hprod : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)) ⊆
      (E₁ : Set (FreeAmalgam d.radical)) * (E₂ : Set (FreeAmalgam d.radical))) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ I : Subgroup (FreeAmalgam d.radical), I ≤ stabilizer d.radical a ∧
      ∃ C : Subgroup (FreeAmalgam d.radical), C ≤ I ∧ (C.subgroupOf I).Normal ∧
        C ⊔ (pCore 2 I).map I.subtype = I ∧
        Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) ∧
        generalizedFitting C = pCore 2 C ∧
        (pResidual 2 C).map C.subtype = (pResidual 2 I).map I.subtype ∧
        ∃ P : Sylow 2 C,
          (P : Subgroup C).map C.subtype = Glauberman.baumannSubgroup (Q d.radical t) ∧
          Order.HasUniqueMaximalOver (P : Subgroup C) ⊤ ∧
          NoCharacteristicNormal (P : Subgroup C) := by
  obtain ⟨E,hE,f,hf,hfQ,hTn,hE₁f,hE₂f,hJf,hJE⟩ :=
    h.replacement_normalized_root_product d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  obtain ⟨E',hE',I,hI,C,hCI,hCn,hgen,hiso,hfit,hres,P,hP,hunique⟩ :=
    h.replacement_root_product_F0 d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let V := stabilizer d.radical a
  let T := (Q d.radical t).subgroupOf V
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F ^ 2)
  have hCa : C ≤ V := hCI.trans hI
  let := finite_stabilizer d.radical a
  let : Finite C := Finite.of_injective (inclusion hCa) (inclusion_injective hCa)
  obtain ⟨j,hj,hjr,hjR,hjQ,_⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hTS : Q d.radical t ≤ V := by
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjR,←hjr]
    exact map_le_range j _
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hkerT : f.ker ≤ T := by
    intro x hx
    exact hQT (hfQ ▸ mem_map_of_mem V.subtype hx)
  have hk : IsPGroup 2 f.ker := by
    have hq : IsPGroup 2 (Q d.radical a) := hjQ ▸ pCore_isPGroup.map j
    exact (hfQ.symm ▸ hq).of_injective
      (f.ker.equivMapOfInjective V.subtype V.subtype_injective).toMonoidHom
      (f.ker.equivMapOfInjective V.subtype V.subtype_injective).injective
  let q := f.comp (inclusion hCa)
  have hqk : IsPGroup 2 q.ker := hk.comap_of_injective
    (inclusion hCa) (inclusion_injective hCa)
  obtain ⟨M,hM,hJM,hTh,hBa,_⟩ := h.replacement_root_product_baumann_control
    d geometry hb ha hat E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  have hBJ : Glauberman.baumannSubgroup (Q d.radical t) ≤ J := by
    change _ ≤ Subgroup.SmallMover.join _ _ _ _
    rw [hJM]
    exact hBa
  have hPq : (P : Subgroup C).map q ≤ RootSubgroup.group 0 := by
    rintro _ ⟨x,hx,rfl⟩
    have hxB : x.val ∈ Glauberman.baumannSubgroup (Q d.radical t) :=
      hP ▸ mem_map_of_mem C.subtype hx
    have hxJ : inclusion hCa x ∈ J.subgroupOf V := hBJ hxB
    have hxroot : q x ∈ (rootFamily (none : Option E.Carrier)).map unipotent.subtype :=
      hJf ▸ mem_map_of_mem f hxJ
    obtain ⟨z,hz⟩ := (RootEnvelope.first_root_mem_iff (q x)).mp hxroot
    exact (RootSubgroup.mem_group_iff 0 (q x)).mpr ⟨z,hz⟩
  have hPn : ¬ (P : Subgroup C).Normal := by
    intro hn
    let := hn
    obtain ⟨eC⟩ := hiso
    let r := eC.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
    have hr : Function.Surjective r := eC.surjective.comp (QuotientGroup.mk'_surjective _)
    exact Matrix.SpecialLinearGroup.sylow_normalizer_ne_top_of_surjective r hr P
      (normalizer_eq_top (H := (P : Subgroup C)))
  have hmodel := unipotent_sup_range_eq_top_of_root_sylow q hqk P hPq hPn
  let S := unipotent.comap f
  have hSn : S ≤ normalizer (T : Set V) := by
    have hh := (comap_mono hTn).trans ((T.map f).le_normalizer_comap f)
    rwa [comap_map_eq_self hkerT] at hh
  have hkS : f.ker ≤ S := by
    intro x hx
    change f x ∈ unipotent
    rw [MonoidHom.mem_ker.mp hx]
    exact one_mem _
  have hSgen : S ⊔ C.subgroupOf V = ⊤ := by
    have hm : (S ⊔ C.subgroupOf V).map f = ⊤ := by
      rw [Subgroup.map_sup,map_comap_eq_self_of_surjective hf]
      have hc : (C.subgroupOf V).map f = q.range := by
        rw [MonoidHom.range_comp]
        congr 1
        ext x
        constructor
        · intro hx
          exact ⟨⟨x.val,hx⟩,rfl⟩
        · rintro ⟨x,rfl⟩
          exact x.property
      rw [hc,hmodel]
    have hh := congrArg (Subgroup.comap f) hm
    rwa [comap_map_eq_self (hkS.trans le_sup_left),comap_top] at hh
  let N := S.map V.subtype
  have hNgen : N ⊔ C = V := by
    have hh := congrArg (Subgroup.map V.subtype) hSgen
    rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hCa,
      ←MonoidHom.range_eq_map,range_subtype] at hh
  have hNT : N ≤ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    have hh := (map_mono (f := V.subtype) hSn).trans (T.le_normalizer_map V.subtype)
    rwa [map_subgroupOf_eq_of_le hTS] at hh
  refine ⟨E',hE',I,hI,C,hCI,hCn,hgen,hiso,hfit,hres,P,hP,hunique,?_⟩
  intro A hAc hAn
  let := hAc
  let D := (A.map (P : Subgroup C).subtype).map C.subtype
  have hDC : D ≤ C := map_subtype_le _
  have hDa : D ≤ V := hDC.trans hCa
  have hDB : D ≤ Glauberman.baumannSubgroup (Q d.radical t) := by
    rw [←hP]
    exact map_mono (map_subtype_le _)
  have hDt : D ≤ stabilizer d.radical t := hDB.trans (inf_le_left.trans (fun _ hx => hx.1))
  have hBN : normalizer (Glauberman.baumannSubgroup (Q d.radical t) : Set (FreeAmalgam d.radical)) ≤
      normalizer (D : Set (FreeAmalgam d.radical)) := by
    have hh := normalizer_le_normalizer_characteristic_map C.subtype C.subtype_injective
      (P : Subgroup C) A
    rwa [hP] at hh
  have hNn : N ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    (hNT.trans (Glauberman.normalizer_le_normalizer_baumannSubgroup _)).trans hBN
  have hCn' : C ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    let := hAn
    have hh := (A.map (P : Subgroup C).subtype).le_normalizer_map C.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hAn' : V ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    rw [←hNgen]
    exact sup_le hNn hCn'
  have hTn' : stabilizer d.radical t ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    ((Q_normalized d.radical t).trans
      (Glauberman.normalizer_le_normalizer_baumannSubgroup _)).trans hBN
  have hD : D = ⊥ := no_common_normal_at_edge d.radical
    (h.replacement_characteristic d) a t ha hat D (le_inf hDa hDt)
    ((normal_subgroupOf_iff_le_normalizer hDa).mpr hAn')
    ((normal_subgroupOf_iff_le_normalizer hDt).mpr hTn')
  have hbot : A.map (P : Subgroup C).subtype = ⊥ :=
    ((A.map (P : Subgroup C).subtype).map_eq_bot_iff_of_injective C.subtype_injective).mp hD
  exact (A.map_eq_bot_iff_of_injective (P : Subgroup C).subtype_injective).mp hbot

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
