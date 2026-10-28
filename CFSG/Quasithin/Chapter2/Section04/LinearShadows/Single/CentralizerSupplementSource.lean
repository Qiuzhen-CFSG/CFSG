module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CyclicSource
public import Theory.GroupTheory.CyclicSectionInvolutionOrbit

/-!
# The original involution-centralizer supplement

The selected Sylow image has index two in T. Its cyclic quotient by the
Thompson subgroup therefore has an ambient-invariant involution. The actual
core-transitivity conclusion of 2.4.12(2) corrects each conjugator into the
involution centralizer, proving T = R C_T(s). All embeddings and quotient
maps are those of the original torus setup.

The transitivity premise belongs to the original field-involution fixed-row
producer. This module removes the separate supplement premise in 2.4.23(4).
Source: Aschbacher–Smith, printed p.537.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The original normal cyclic section makes the marked field involution
central modulo the Thompson subgroup. Its actual core orbit then supplies
the first conclusion of source 2.4.23(4). -/
theorem CyclicTorusSetup.sylow_centralizer_supplement
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {n : ℕ} (c : CyclicTorusSetup d T n)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex (T : Subgroup G) = 2)
    (s : T) (hs : orderOf s = 2)
    (hsS : (s : G) ∈ (d.S : Subgroup d.H).map d.H.subtype)
    (hsR : (s : G) ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (horbit : ∀ v : T, orderOf v = 2 →
      (v : G) * (s : G)⁻¹ ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      ∃ r ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype),
        r * (s : G) * r⁻¹ = (v : G)) :
    (T : Subgroup G) = Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊔
      ((T : Subgroup G) ⊓ centralizer ({(s : G)} : Set G)) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let ST := S.subgroupOf (T : Subgroup G)
  let RT := R.subgroupOf (T : Subgroup G)
  have hRS : R ≤ S := sSup_le fun _ hA => hA.1
  have hRT : R ≤ (T : Subgroup G) := hRS.trans hST
  let : RT.Normal := c.normal_in_sylow
  let : ST.Normal := normal_of_index_eq_two hindex
  let : (R.subgroupOf S).Normal :=
    (normal_subgroupOf_iff_le_normalizer hRS).mpr
      (S.le_normalizer.trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ S))
  let : IsCyclic (S ⊓ normalizer (c.hall : Set G) : Subgroup G) := c.field_cyclic
  let : IsCyclic ((S ⊓ normalizer (c.hall : Set G)).subgroupOf S) :=
    (subgroupOfEquivOfLe (show S ⊓ normalizer (c.hall : Set G) ≤ S from inf_le_left)).isCyclic.mpr inferInstance
  let : IsCyclic (S ⧸ R.subgroupOf S) := c.split_sylow.symm.QuotientMulEquiv.isCyclic.mpr inferInstance
  let e : ST ≃* S := subgroupOfEquivOfLe hST
  have he : (RT.subgroupOf ST).map e.toMonoidHom = R.subgroupOf S := by
    ext a
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact hv
    · intro ha
      exact ⟨⟨⟨a,hST a.property⟩,a.property⟩,ha,rfl⟩
  let : IsCyclic (ST ⧸ RT.subgroupOf ST) :=
    (QuotientGroup.congr _ _ e he).isCyclic.mpr inferInstance
  have hsup := sup_centralizer_eq_top_of_normal_cyclic_section RT ST s hsS hs hsR (by
    intro v hv hcos
    obtain ⟨r,hr,heq⟩ := horbit v hv hcos
    exact ⟨⟨r,hRT hr⟩,hr,Subtype.ext heq⟩)
  have hm := congrArg (Subgroup.map (T : Subgroup G).subtype) hsup
  rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hRT,
    ←MonoidHom.range_eq_map,Subgroup.range_subtype] at hm
  have hc : (centralizer ({s} : Set T)).map (T : Subgroup G).subtype =
      (T : Subgroup G) ⊓ centralizer ({(s : G)} : Set G) := by
    ext a
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact ⟨v.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hv))⟩
    · intro ha
      exact ⟨⟨a,ha.1⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp ha.2)),rfl⟩
  rw [hc] at hm
  exact hm.symm
end CFSG.Quasithin.Chapter2.LinearShadows.Single
