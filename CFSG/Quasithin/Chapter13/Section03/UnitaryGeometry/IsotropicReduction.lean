module

public import Theory.LinearAlgebra.AlternatingPlane
public import CFSG.Quasithin.ChapterE.Section06.Basic
public import CFSG.Quasithin.ChapterE.Section06.Obstructions

/-!
# From nondegenerate-plane centralizers to the genuine parameter r

A nonisotropic subgroup contains a nondegenerate plane, whose centralizer
contains its centralizer. Once the source C.2/chief-factor argument controls
those planes, every escaping subgroup is isotropic and has dimension at most
three. The original E.6 TI hypothesis identifies escape from M with escape
from N_G(V), which is required by the actual definition of r(G,V).
If r=3, its attained minimum yields an actual escaping isotropic three-space.

Source: Aschbacher–Smith, Lemma 13.3.12(2–3), printed p.890. The nondegenerate
plane centralizer premise is the preceding C.2/chief-factor step, not proved
by these linear and parameter reductions.
-/

@[expose] public noncomputable section
open Module Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
variable {G : Type*} [Group G] [Finite G] {V M : Subgroup G} [IsElementaryAbelian 2 V]

abbrev subgroupSpace : Subgroup V ≃o Submodule (ZMod 2) (Additive V) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)
def ambientSpace (U : Subgroup G) : Submodule (ZMod 2) (Additive V) :=
  subgroupSpace (U.subgroupOf V)
def ambientGroup (P : Submodule (ZMod 2) (Additive V)) : Subgroup G :=
  (subgroupSpace.symm P).map V.subtype

omit [Finite G] in
theorem ambientSpace_ambientGroup (P : Submodule (ZMod 2) (Additive V)) :
    ambientSpace (ambientGroup P)=P := by
  unfold ambientSpace ambientGroup
  rw [Subgroup.subgroupOf,Subgroup.comap_map_eq_self_of_injective V.subtype_injective]
  exact subgroupSpace.apply_symm_apply P

omit [Finite G] in
theorem ambientGroup_le {P : Submodule (ZMod 2) (Additive V)} {U : Subgroup G}
    (hP : P≤ambientSpace U) : ambientGroup P≤U := by
  rintro x ⟨v,hv,rfl⟩
  exact hP hv

theorem ambientSpace_finrank_add_corank (U : Subgroup G) :
    finrank (ZMod 2) (ambientSpace (V:=V) U)+ChapterE.subgroupCorank V U=
      finrank (ZMod 2) (Additive V) := by
  have hc := (U.subgroupOf V).card_mul_index
  have hU : Nat.card (U.subgroupOf V)=2^finrank (ZMod 2) (ambientSpace (V:=V) U) := by
    have he : Nat.card (U.subgroupOf V)=Nat.card (ambientSpace (V:=V) U) := rfl
    rw [he,Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod]
  have hV : Nat.card V=2^finrank (ZMod 2) (Additive V) := by
    have h := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive V)
    change Nat.card V=_ at h
    simpa only [Nat.card_zmod] using h
  have hi : (U.subgroupOf V).index=2^ChapterE.subgroupCorank V U := by
    rw [ChapterE.subgroupCorank_eq_quotient_finrank]
    exact V.relIndex_eq_two_pow_quotient_finrank U
  rw [hU,hi,hV,←pow_add] at hc
  exact Nat.pow_right_injective (by decide : 2≤2) hc

omit [Finite G] in
theorem escaping_isotropic_of_plane_centralizers
    (B : LinearMap.BilinForm (ZMod 2) (Additive V)) (ha : B.IsAlt)
    (hplanes : ∀ P : Submodule (ZMod 2) (Additive V),finrank (ZMod 2) P=2 →
      (B.restrict P).Nondegenerate → centralizer (ambientGroup P : Set G)≤M)
    (U : Subgroup G) (he : ¬centralizer (U : Set G)≤M) :
    ∀ x∈ambientSpace (V:=V) U,∀ y∈ambientSpace (V:=V) U,B x y=0 := by
  by_contra hn
  obtain ⟨P,hPU,hd,hP⟩ := B.exists_nondegenerate_plane_of_not_isotropic ha _ hn
  exact he ((Subgroup.centralizer_le (ambientGroup_le hPU)).trans (hplanes P hd hP))

theorem three_le_globalR_of_plane_centralizers
    {K : GroupClass} {T : Sylow 2 G}
    (h : ChapterE.Section06.HypothesisE61 K T M V)
    (B : LinearMap.BilinForm (ZMod 2) (Additive V)) (ha : B.IsAlt)
    (hn : B.Nondegenerate) (hd : finrank (ZMod 2) (Additive V)=6)
    (hplanes : ∀ P : Submodule (ZMod 2) (Additive V),finrank (ZMod 2) P=2 →
      (B.restrict P).Nondegenerate → centralizer (ambientGroup P : Set G)≤M) :
    3≤ChapterE.globalR V := by
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hUV,he⟩
  by_cases hU : U=⊥
  · subst U
    rw [ChapterE.Section06.corank_bot,hd]
    norm_num
  have heM : ¬centralizer (U : Set G)≤M :=
    fun hc => he ((h.centralizer_le_iff hU hUV).mp hc)
  have hi := escaping_isotropic_of_plane_centralizers B ha hplanes U heM
  have hb := B.twice_finrank_le_of_isotropic hn _ hi
  have hc := ambientSpace_finrank_add_corank (V:=V) U
  rw [hd] at hb hc
  exact_mod_cast (show 3≤ChapterE.subgroupCorank V U by omega)

theorem exists_escaping_isotropic_three_space
    {K : GroupClass} {T : Sylow 2 G}
    (h : ChapterE.Section06.HypothesisE61 K T M V)
    (B : LinearMap.BilinForm (ZMod 2) (Additive V)) (ha : B.IsAlt)
    (hd : finrank (ZMod 2) (Additive V)=6)
    (hplanes : ∀ P : Submodule (ZMod 2) (Additive V),finrank (ZMod 2) P=2 →
      (B.restrict P).Nondegenerate → centralizer (ambientGroup P : Set G)≤M)
    (hr : ChapterE.globalR V=3) :
    ∃ U : Subgroup G,U≤V ∧ finrank (ZMod 2) (ambientSpace (V:=V) U)=3 ∧
      (∀x∈ambientSpace (V:=V) U,∀y∈ambientSpace (V:=V) U,B x y=0) ∧
      ¬centralizer (U : Set G)≤M := by
  obtain ⟨U,hUV,he,hc⟩ := ChapterE.Section06.globalR_attained (V:=V) (by simp [hr])
  rw [hr] at hc
  have hc3 : ChapterE.subgroupCorank V U=3 := by exact_mod_cast hc
  have hdim := ambientSpace_finrank_add_corank (V:=V) U
  rw [hd,hc3] at hdim
  have hU : U≠⊥ := by
    intro hz
    subst U
    rw [ChapterE.Section06.corank_bot,hd] at hc3
    omega
  have heM : ¬centralizer (U : Set G)≤M := fun hh => he ((h.centralizer_le_iff hU hUV).mp hh)
  exact ⟨U,hUV,by omega,escaping_isotropic_of_plane_centralizers B ha hplanes U heM,heM⟩
end CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
