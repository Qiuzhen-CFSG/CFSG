module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.Geometry
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ModuleGeometry
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.NormalFourCentralizer

/-!
# Constructing the local four-plane in the L₃(2) branch

The original indecomposable module has sixteen elements, with one orbit of
fourteen outside its fixed line. Orbit–stabilizer gives the exact index of
each local point centralizer. A normal subgroup of order four in V supplies
a T-invariant plane. Its centralizer has index at most two, and the orbit
calculation excludes index one and proves the literal local Sylow property.

No ambient Sylow-centralizer, escaping-normalizer or fusion conclusion is
used. The fixed-space and larger reduced-module calculations are separate.

Source: Aschbacher–Smith, Section 12.4, printed pp.813–814, especially
the choice of E preceding 12.4.5 and the opening of 12.4.6.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The nonsplit chosen module has order sixteen. -/
theorem module_card_sixteen (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥) : Nat.card V = 16 := by
  let _ := D.elementary
  change Nat.card (Additive V) = 16
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    SLThreeCommutatorSource.module_finrank_four ext hne]
  rfl

/-- Every nonfixed point has orbit length fourteen under the actual N_G(L). -/
theorem point_centralizer_index (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hMV : normalizer (L : Set G) ≤ normalizer (V : Set G))
    (v : G) (hvV : v ∈ V) (hv : v ∉ fixedSubgroup L V) :
    (centralizer ({v} : Set G)).relIndex (normalizer (L : Set G)) = 14 := by
  let M := normalizer (L : Set G)
  let : MulAction M G := {
    smul := fun g v => MulAut.conj (g : G) v
    one_smul := by intro v; change (1 : G) * v * 1⁻¹ = v; group
    mul_smul := by
      intro g k v
      change ((g : G) * (k : G)) * v * ((g : G) * (k : G))⁻¹ =
        (g : G) * ((k : G) * v * (k : G)⁻¹) * (g : G)⁻¹
      group }
  have ho : MulAction.orbit M v = (V : Set G) \ (fixedSubgroup L V : Set G) := by
    ext w
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨(mem_normalizer_iff.mp (hMV g.property) v).mp hvV, ?_⟩
      have hMF : M ≤ normalizer (fixedSubgroup L V : Set G) :=
        (le_inf hMV (normalizer_le_normalizer_centralizer L)).trans
          inf_normalizer_le_normalizer_inf
      exact fun hw => hv ((mem_normalizer_iff.mp (hMF g.property) v).mpr hw)
    · intro hw
      obtain ⟨l, hl, he⟩ := ext.transitive_nonfixed hne v w hvV hw.1 hv hw.2
      exact ⟨⟨l, L.le_normalizer hl⟩, he⟩
  have hs : MulAction.stabilizer M v = (centralizer ({v} : Set G)).subgroupOf M := by
    ext g
    change MulAut.conj (g : G) v = v ↔ (g : G) ∈ centralizer ({v} : Set G)
    rw [mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul
  change ((centralizer ({v} : Set G)).subgroupOf M).index = 14
  rw [← hs, MulAction.index_stabilizer, ho, Set.ncard_sdiff (show
    (fixedSubgroup L V : Set G) ⊆ V from inf_le_left)]
  change Nat.card V - Nat.card (fixedSubgroup L V) = 14
  rw [module_card_sixteen ext hne, ext.fixed_card_eq_two hne]

/-- A point of V centralized by T lies in the original fixed line. -/
theorem fixed_by_sylow (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hMV : normalizer (L : Set G) ≤ normalizer (V : Set G)) :
    V ⊓ centralizer (T : Set G) ≤ fixedSubgroup L V := by
  intro v hv
  by_contra hvF
  let M := normalizer (L : Set G)
  have hTC : (T : Subgroup G) ≤ centralizer ({v} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hv.2 t ht)
  have hd : (centralizer ({v} : Set G)).relIndex M ∣
      ((T : Subgroup G).subgroupOf M).index :=
    index_dvd_of_le (by intro t ht; exact hTC ht)
  apply (T.subtype hTM).not_dvd_index
  change 2 ∣ ((T : Subgroup G).subgroupOf M).index
  exact (show 2 ∣ (centralizer ({v} : Set G)).relIndex M by
    rw [point_centralizer_index ext hne hMV v hv.1 hvF]; decide).trans hd

/-- The fourteen-vector orbit makes every index-two centralizer in T Sylow
in the literal local point centralizer. -/
theorem local_sylow_of_index_two (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hMV : normalizer (L : Set G) ≤ normalizer (V : Set G))
    (v : G) (hvV : v ∈ V) (hv : v ∉ fixedSubgroup L V)
    (R : Subgroup G) (hRT : R ≤ T) (hRv : R ≤ centralizer ({v} : Set G))
    (hi : R.relIndex (T : Subgroup G) = 2) :
    Chapter1.IsSylowIn 2 R (normalizer (L : Set G) ⊓ centralizer ({v} : Set G)) := by
  let M := normalizer (L : Set G)
  let C := M ⊓ centralizer ({v} : Set G)
  have hRC : R ≤ C := le_inf (hRT.trans hTM) hRv
  have hc : C.relIndex M = 14 := by
    rw [inf_relIndex_left]
    exact point_centralizer_index ext hne hMV v hvV hv
  have ht := relIndex_mul_relIndex R (T : Subgroup G) M hRT hTM
  have hr := relIndex_mul_relIndex R C M hRC inf_le_left
  rw [hi] at ht
  rw [hc] at hr
  have he : R.relIndex C * 7 = (T : Subgroup G).relIndex M := by omega
  have hn : ¬ 2 ∣ (R.subgroupOf C).index := by
    intro hd
    apply (T.subtype hTM).not_dvd_index
    change 2 ∣ (T : Subgroup G).relIndex M
    rw [← he]
    exact dvd_mul_of_dvd_left hd 7
  have hp : IsPGroup 2 (R.subgroupOf C) :=
    (T.isPGroup'.of_injective (inclusion hRT) (inclusion_injective hRT)).comap_subtype
  exact ⟨hp.toSylow hn, map_subgroupOf_eq_of_le hRC⟩

/-- A normal four-plane exists in the original elementary module. -/
theorem exists_invariant_plane (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    ∃ E : Subgroup G, E ≤ V ∧ Nat.card E = 4 ∧
      (T : Subgroup G) ≤ normalizer (E : Set G) := by
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  let A := V.subgroupOf (T : Subgroup G)
  have hA : A.Normal := normal_subgroupOf_of_le_normalizer hTV
  have hAc : Nat.card A = 2 ^ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe D.le_sylow).toEquiv,
      module_card_sixteen ext hne]
    rfl
  obtain ⟨U, hUn, hUA, hUc⟩ :=
    exists_normal_subgroup_card_pow_of_normal (p := 2) A hA hAc 2 (by decide)
  let E := U.map (T : Subgroup G).subtype
  have hEV : E ≤ V := by
    rw [← map_subgroupOf_eq_of_le D.le_sylow]
    exact map_mono hUA
  have hET : E ≤ (T : Subgroup G) := map_subtype_le _
  have hEU : E.subgroupOf (T : Subgroup G) = U := by
    ext t
    constructor
    · rintro ⟨x, hx, he⟩
      exact (Subtype.ext he : x = t) ▸ hx
    · intro ht
      exact ⟨t, ht, rfl⟩
  have : (E.subgroupOf (T : Subgroup G)).Normal := hEU.symm ▸ hUn
  refine ⟨E, hEV, ?_, le_normalizer_of_normal_subgroupOf hET⟩
  rw [card_map_of_injective (T : Subgroup G).subtype_injective, hUc]
  rfl

/-- An invariant four-plane contains a nonfixed point, and its centralizer
has the exact source index and local Sylow property. -/
theorem invariant_plane_local_sylow (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hMV : normalizer (L : Set G) ≤ normalizer (V : Set G))
    (E : Subgroup G) (hEV : E ≤ V) (hEc : Nat.card E = 4)
    (hTE : (T : Subgroup G) ≤ normalizer (E : Set G)) :
    ∃ v ∈ E, v ∉ fixedSubgroup L V ∧
      ((T : Subgroup G) ⊓ centralizer (E : Set G)).relIndex T = 2 ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (E : Set G))
        (normalizer (L : Set G) ⊓ centralizer ({v} : Set G)) := by
  let _ := D.elementary
  have hEF : ¬ E ≤ fixedSubgroup L V := by
    intro he
    have hc := card_le_of_le he
    rw [hEc, ext.fixed_card_eq_two hne] at hc
    omega
  obtain ⟨v, hvE, hvF⟩ := SetLike.not_le_iff_exists.mp hEF
  let U := E.subgroupOf (T : Subgroup G)
  have hET : E ≤ (T : Subgroup G) := hEV.trans D.le_sylow
  let : U.Normal := normal_subgroupOf_of_le_normalizer hTE
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le hEV
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hET
  have hUc : Nat.card U = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hET).toEquiv).trans hEc
  have hb := centralizer_index_le_two_of_normal_four T.isPGroup' U hUc
  let R := (T : Subgroup G) ⊓ centralizer (E : Set G)
  have hRC : R.subgroupOf (T : Subgroup G) = centralizer (U : Set T) := by
    ext t
    constructor
    · intro ht u hu
      exact Subtype.ext (ht.2 u hu)
    · intro ht
      refine ⟨t.property, ?_⟩
      intro e he
      exact congrArg Subtype.val (ht ⟨e, hET he⟩ he)
  have hRi : R.relIndex (T : Subgroup G) ≤ 2 := by
    change (R.subgroupOf (T : Subgroup G)).index ≤ 2
    rwa [hRC]
  have hRv : R ≤ centralizer ({v} : Set G) :=
    inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr hvE))
  have hRne : R.relIndex (T : Subgroup G) ≠ 1 := by
    intro hi
    have hTR := relIndex_eq_one.mp hi
    apply hvF
    apply fixed_by_sylow ext hne hTM hMV
    refine ⟨hEV hvE, ?_⟩
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hRv (hTR ht))
  have hRpos : 0 < R.relIndex (T : Subgroup G) :=
    Nat.pos_of_ne_zero (R.subgroupOf (T : Subgroup G)).index_ne_zero_of_finite
  have hi : R.relIndex (T : Subgroup G) = 2 := by omega
  exact ⟨v, hvE, hvF, hi,
    local_sylow_of_index_two ext hne hTM hMV v (hEV hvE) hvF R inf_le_left hRv hi⟩
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
