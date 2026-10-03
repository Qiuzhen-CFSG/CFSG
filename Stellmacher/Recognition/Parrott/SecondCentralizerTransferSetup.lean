module

public import Stellmacher.Recognition.Parrott.SecondCentralizerLocalStructure

/-!
# Local inputs to the two transfers

A core square root of the supplied Q-fixed involution v belongs to Ω₁(K):
it centralizes both Z(K) and v, which together generate Z(Ω₁(K)). Also,
the supplied group Q of order three lies in every normal subgroup of index
two of C_G(v). Thus it normalizes the intersection of Ω₁(K) with any
normal subgroup of such an index-two subgroup.

These elementary local facts keep the compatible root and odd-order action
available to the separate normalizer-character and Sylow-geometry arguments.
Source: Parrott, *A characterization of the Tits' simple group* (1972),
§4, pp.682–683.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Any core root of the supplied fixed involution lies in the actual omega image. -/
public theorem normalizer_fixed_root_mem_omega
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∀ b ∈ K.map N.subtype, b ^ 2 = v →
      b ∈ (omega₁ K (p := 2)).map (N.subtype.comp K.subtype) := by
  intro N K b hb hbsq
  let i := N.subtype.comp K.subtype
  let U := omega₁ K (p := 2)
  let ZK := (center K).map i
  let ZW := (center U).map (i.comp U.subtype)
  have hZK : ZK ≤ centralizer ({b} : Set G) := by
    obtain ⟨bN, hbK, heb⟩ := hb
    rintro t ⟨tK, htK, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg i (mem_center_iff.mp htK (⟨bN, hbK⟩ : K))
    change (bN : G) * i tK = i tK * (bN : G) at he
    change (bN : G) = b at heb
    rw [heb] at he
    exact he.symm
  have hZW : ZW ≤ centralizer ({b} : Set G) := by
    have hjoin : ZW = ZK ⊔ zpowers v :=
      (d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix).2.2.1
    rw [hjoin]
    refine sup_le hZK (zpowers_le.mpr ?_)
    apply mem_centralizer_singleton_iff.mpr
    rw [← hbsq]
    exact ((Commute.refl b).pow_right 2).symm.eq
  rw [(d.normalizer_core_omega_structure h hN hproper).2.2.2]
  exact ⟨hb, fun t ht => mem_centralizer_singleton_iff.mp (hZW ht)⟩

/-- Both transfer kernels still contain the supplied odd-order group as a
normalizing group of their Sylow intersection. -/
public theorem second_transfer_intersection_three_normalized
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let W := U.map (N.subtype.comp K.subtype)
    let A := (Q : Subgroup N).map N.subtype
    let C := centralizer ({v} : Set G)
    ∀ M : Subgroup C, M.Normal → M.index = 2 →
    ∀ L : Subgroup M, L.Normal →
      A ≤ normalizer ((W ⊓ L.map (C.subtype.comp M.subtype) : Subgroup G) : Set G) := by
  intro N K U W A C M hMn hMi L hLn
  let := hMn
  let := hLn
  have hAC : A ≤ C := by
    have hvC : v ∈ centralizer (A : Set G) := (hfix.symm ▸ mem_zpowers v).2
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hvC a ha)
  have hAcard : Nat.card (A.subgroupOf C) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv]
    exact (card_map_of_injective N.subtype_injective).trans
      (d.normalizer_three_card h hN hproper Q)
  have hACM : A.subgroupOf C ≤ M := by
    apply relIndex_eq_one.mp
    apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 2 3 by decide)
    · simpa only [hMi] using relIndex_dvd_index_of_normal (H := M) (K := A.subgroupOf C)
    · simpa only [hAcard] using relIndex_dvd_card M (A.subgroupOf C)
  have hAM : A ≤ M.map C.subtype := by
    intro a ha
    exact ⟨⟨a, hAC ha⟩, hACM ha, rfl⟩
  have hNW : N ≤ normalizer (W : Set G) := by
    let B := U.map K.subtype
    let : U.Characteristic := omega₁_characteristic K
    let : B.Normal := ConjAct.normal_of_characteristic_of_normal
    have hh := le_normalizer_map (H := B) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, B, W, map_map] using hh
  have hML : M.map C.subtype ≤
      normalizer (L.map (C.subtype.comp M.subtype) : Set G) := by
    have hh := L.le_normalizer_map (C.subtype.comp M.subtype)
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, MonoidHom.range_comp, range_subtype] at hh
    exact hh
  intro a ha
  apply mem_normalizer_iff.mpr
  intro x
  exact and_congr (mem_normalizer_iff.mp (hNW (map_subtype_le _ ha)) x)
    (mem_normalizer_iff.mp (hML (hAM ha)) x)

end Stellmacher.Recognition.ParrottSecondElementaryData
