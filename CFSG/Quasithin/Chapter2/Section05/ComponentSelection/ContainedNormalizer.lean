module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSource
public import Theory.GroupTheory.ComponentRadicalOvergroup
public import Theory.SpecificGroups.GL2.ThreeCoreOvergroups

/-!
# The first contained-normalizer reduction in the original component

Under the opposite branch guard N_D(D∩O2(H_U))≤M, the actual core of M∩D
lies in D∩O2(H_U). Saturation constructs radicality inside D, and C.2.1
applies to the full normalizer there. Both subgroup restrictions and all
ambient embeddings are literal. This is the first reduction on printed
p.553 in Aschbacher--Smith 2.5.3(4).

For an actual GL2(3) intersection, this identifies the radical with its
quaternion core or the original component Sylow subgroup. Conjugacy control
and the component-removal induction remain separate.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- The source contained-normalizer guard forces the original intersection
core into the original saturated component radical. -/
theorem intersection_core_le_saturated_component_of_normalizer_le
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (hinside : (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    ((M.subgroupOf H).subgroupOf D).pCoreIn 2 ≤ ((twoCore HU).subgroupOf H).subgroupOf D := by
  let Q := (twoCore HU).subgroupOf H
  have hsatH : ∀ P : Subgroup H, IsPGroup 2 P →
      HU.subgroupOf H ≤ normalizer (P : Set H) → P ≤ Q := by
    intro P hp hn x hx
    have hna : HU ≤ normalizer (P.map H.subtype : Set G) := by
      intro a ha
      exact P.le_normalizer_map H.subtype ⟨⟨a, hpair.2 ha⟩, hn ha, rfl⟩
    exact hsat _ (map_subtype_le P) (hp.map H.subtype) hna
      (mem_map_of_mem H.subtype hx)
  have hAQ : HU.subgroupOf H ≤ normalizer (Q : Set H) := by
    intro a ha x
    exact le_normalizer_twoCore HU ha (x : G)
  apply hD.local_overgroup_core_le_intersection_of_saturation
    (isPGroup_pCoreIn 2 HU).comap_subtype hAQ hsatH
  let R := D ⊓ Q
  have he : R.subgroupOf D = Q.subgroupOf D := by ext x; simp [R]
  intro x hx
  change x ∈ normalizer (Q.subgroupOf D : Set D) at hx
  rw [← he, ← subgroupOf_normalizer_eq (show R ≤ D from inf_le_left)] at hx
  exact hinside (mem_map_of_mem H.subtype ⟨x.property, hx⟩)


/-- In the actual GL2(3) intersection, the saturated component radical is
its quaternion core or the original component Sylow subgroup. -/
theorem contained_component_radical_eq_core_or_sylow
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (hinside : (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M)
    (P : Sylow 2 D) (hPM : (P : Subgroup D) ≤ (M.subgroupOf H).subgroupOf D)
    (hQP : ((twoCore HU).subgroupOf H).subgroupOf D ≤ (P : Subgroup D))
    (e : ((M.subgroupOf H).subgroupOf D) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ((twoCore HU).subgroupOf H).subgroupOf D = ((M.subgroupOf H).subgroupOf D).pCoreIn 2 ∨
      ((twoCore HU).subgroupOf H).subgroupOf D = (P : Subgroup D) := by
  let I := (M.subgroupOf H).subgroupOf D
  let R := ((twoCore HU).subgroupOf H).subgroupOf D
  have hRI : R ≤ I := hQP.trans hPM
  have hcore : pCore 2 I ≤ R.subgroupOf I := by
    intro x hx
    exact intersection_core_le_saturated_component_of_normalizer_le hpair hsat D hD hinside
      (mem_map_of_mem I.subtype hx)
  have hRP : R.subgroupOf I ≤ (P.subtype hPM : Subgroup I) := fun x hx => hQP hx
  rcases Matrix.GeneralLinearGroup.subgroup_eq_core_or_sylow_of_equiv_three e
      (P.subtype hPM) (R.subgroupOf I) hcore hRP with he | he
  · left
    have hh := congrArg (Subgroup.map I.subtype) he
    rwa [map_subgroupOf_eq_of_le hRI] at hh
  · right
    have hh := congrArg (Subgroup.map I.subtype) he
    rwa [map_subgroupOf_eq_of_le hRI, Sylow.coe_subtype, map_subgroupOf_eq_of_le hPM] at hh

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
