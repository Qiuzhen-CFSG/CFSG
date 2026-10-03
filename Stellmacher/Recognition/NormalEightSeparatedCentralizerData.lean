module

public import Stellmacher.Recognition.NormalEightSeparatedFusion

/-!
# Local data for the separated involution-centralizer argument

In the separated case, a normalizer of the four inside the centralizer of
a noncentral involution fixes two distinct nonidentity elements of the four,
and hence centralizes it. Thus a normalizer supplement to the odd core gives
the desired centralizer supplement.

`CentralizerSetup` records the Sylow subgroup and odd-core supplement used
for the normal-closure analysis. Existence of this data is not asserted here.
If the closure has order four, its equality with the original four gives
the normalizer supplement. The larger closure cases remain separate.

Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, pp.387–388;
refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedCentralizers
open Subgroup
open NormalEightSeparatedFusion
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

private theorem centralizes_four_of_commute_pair
    {P : Type*} [Group P] [Finite P]
    (W : Subgroup P) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (i z : W) (hi : i ≠ 1) (hz : z ≠ 1) (hiz : i ≠ z)
    (g : P) (hgi : Commute g (i : P)) (hgz : Commute g (z : P)) :
    g ∈ centralizer (W : Set P) := by
  let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour W := ⟨hW, IsElementaryAbelian.exponent_eq_prime⟩
  intro x hx
  let w : W := ⟨x, hx⟩
  by_cases h1 : w = 1
  · have : x = 1 := congrArg Subtype.val h1
    simp [this]
  by_cases hiw : w = i
  · have he : x = i := congrArg Subtype.val hiw
    rw [he]
    exact hgi.eq.symm
  by_cases hzw : w = z
  · have he : x = z := congrArg Subtype.val hzw
    rw [he]
    exact hgz.eq.symm
  have he : w = i * z := IsKleinFour.eq_mul_of_ne_all hi hz hiz h1 hiw hzw
  have he' : x = (i : P) * z := congrArg Subtype.val he
  rw [he']
  exact (hgi.mul_right hgz).eq.symm

/-- Separation makes the four normalizer inside an involution centralizer
equal to the four centralizer. -/
public theorem normalizer_eq_centralizer
    (S : Sylow 2 G) (W : Subgroup S) [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W)
    (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hsep : Separated S W z)
    (i : S) (hiW : i ∈ W) (hi : orderOf i = 2) (hiC : i ∉ center S) :
    let C := centralizer ({(i : G)} : Set G)
    let U := (W.map (S : Subgroup G).subtype).subgroupOf C
    normalizer (U : Set C) = centralizer (U : Set C) := by
  intro C U
  let W₀ := W.map (S : Subgroup G).subtype
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.map_subtype
  have hWC : W₀ ≤ C := by
    intro w hw
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨w, hw⟩ : W₀)
      (⟨(i : G), mem_map_of_mem _ hiW⟩ : W₀))
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hWC
  have hU : Nat.card U = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv,
      card_map_of_injective (S : Subgroup G).subtype_injective, hW]
  let iC : C := ⟨i, hWC (mem_map_of_mem _ hiW)⟩
  let zC : C := ⟨z, hWC (mem_map_of_mem _ hzW)⟩
  let iU : U := ⟨iC, mem_map_of_mem _ hiW⟩
  let zU : U := ⟨zC, mem_map_of_mem _ hzW⟩
  have hi1 : iU ≠ 1 := by
    intro h
    have he : i = 1 := Subtype.ext (congrArg (fun x : U => ((x : C) : G)) h)
    simp [he] at hi
  have hz1 : zU ≠ 1 := by
    intro h
    have he : z = 1 := Subtype.ext (congrArg (fun x : U => ((x : C) : G)) h)
    simp [he] at hz
  have hiz : iU ≠ zU := by
    intro h
    have he : i = z := Subtype.ext (congrArg (fun x : U => ((x : C) : G)) h)
    exact hiC (he ▸ hzC)
  apply le_antisymm ?_ (centralizer_le_normalizer _)
  intro g hg
  have hgz : g * zC * g⁻¹ = zC := by
    have hm : g * zC * g⁻¹ ∈ U := (mem_normalizer_iff.mp hg zC).mp zU.property
    obtain ⟨t, ht, he⟩ := hm
    have htconj : IsConj (z : G) (t : G) :=
      isConj_iff.mpr ⟨g, he.symm⟩
    have htEq := hsep t ht htconj
    apply Subtype.ext
    exact he.symm.trans (congrArg Subtype.val htEq)
  apply centralizes_four_of_commute_pair U hU iU zU hi1 hz1 hiz g
  · exact Subtype.ext (mem_centralizer_singleton_iff.mp g.property)
  · exact mul_inv_eq_iff_eq_mul.mp hgz
end Stellmacher.Recognition.NormalEightSeparatedCentralizers

namespace Stellmacher.Recognition.NormalEightSeparatedCentralizers
open Subgroup NormalEightSeparatedFusion
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- A normalizer supplement is sufficient for the required factorization. -/
public theorem factorization_of_normalizer_supplement
    (S : Sylow 2 G) (W : Subgroup S) [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W)
    (hzC : z ∈ center S) (hz : orderOf z = 2) (hsep : Separated S W z)
    (hsupp : ∀ i : S, i ∈ W → orderOf i = 2 → i ∉ center S →
      let C := centralizer ({(i : G)} : Set G)
      normalizer ((W.map (S : Subgroup G).subtype).subgroupOf C : Set C) ⊔
        pPrimeCore 2 C = ⊤) : CentralizerFactorization S W := by
  intro i hiW hi hiC
  dsimp only
  rw [← normalizer_eq_centralizer S W hW z hzW hzC hz hsep i hiW hi hiC]
  exact hsupp i hiW hi hiC

/-- The intrinsic local configuration for the normal-closure analysis. -/
public structure CentralizerSetup (S : Sylow 2 G) (W : Subgroup S) (i : S) where
  T : Sylow 2 (centralizer ({(i : G)} : Set G))
  sylow_eq : (T : Subgroup (centralizer ({(i : G)} : Set G))) =
    (S : Subgroup G).subgroupOf (centralizer ({(i : G)} : Set G))
  omega_center_eq :
    ((omega₁ (center T) (p := 2)).map (center T).subtype).map
      (T : Subgroup (centralizer ({(i : G)} : Set G))).subtype =
    (W.map (S : Subgroup G).subtype).subgroupOf (centralizer ({(i : G)} : Set G))
  H : Subgroup (centralizer ({(i : G)} : Set G))
  sylow_le : (T : Subgroup (centralizer ({(i : G)} : Set G))) ≤ H
  four_le : (W.map (S : Subgroup G).subtype).subgroupOf
    (centralizer ({(i : G)} : Set G)) ≤ H
  supplement : H ⊔ pPrimeCore 2 (centralizer ({(i : G)} : Set G)) = ⊤
  elementary : IsElementaryAbelian 2 (normalClosure
    (((W.map (S : Subgroup G).subtype).subgroupOf
      (centralizer ({(i : G)} : Set G))).subgroupOf H : Set H))
  closure_le : (normalClosure
    (((W.map (S : Subgroup G).subtype).subgroupOf
      (centralizer ({(i : G)} : Set G))).subgroupOf H : Set H)).map H.subtype ≤ T

/-- The normal closure of the four in the selected supplement. -/
public abbrev CentralizerSetup.closure
    {S : Sylow 2 G} {W : Subgroup S} {i : S} (d : CentralizerSetup S W i) : Subgroup d.H :=
  normalClosure (((W.map (S : Subgroup G).subtype).subgroupOf
    (centralizer ({(i : G)} : Set G))).subgroupOf d.H : Set d.H)

/-- An order-four normal closure gives a normalizer supplement to the odd core. -/
public theorem CentralizerSetup.normalizer_supplement_of_card_four
    {S : Sylow 2 G} {W : Subgroup S} [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) {i : S} (hiW : i ∈ W)
    (d : CentralizerSetup S W i) (hc : Nat.card d.closure = 4) :
    let C := centralizer ({(i : G)} : Set G)
    normalizer ((W.map (S : Subgroup G).subtype).subgroupOf C : Set C) ⊔
      pPrimeCore 2 C = ⊤ := by
  intro C
  let U := (W.map (S : Subgroup G).subtype).subgroupOf C
  have hWC : W.map (S : Subgroup G).subtype ≤ C := by
    let : IsElementaryAbelian 2 (W.map (S : Subgroup G).subtype) :=
      IsElementaryAbelian.map_subtype
    intro w hw
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm
      (⟨w, hw⟩ : W.map (S : Subgroup G).subtype)
      (⟨(i : G), mem_map_of_mem _ hiW⟩ : W.map (S : Subgroup G).subtype))
  have hcard : Nat.card (U.subgroupOf d.H) = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe d.four_le).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv,
      card_map_of_injective (S : Subgroup G).subtype_injective, hW]
  have heq : U.subgroupOf d.H = d.closure :=
    eq_of_le_of_card_ge le_normalClosure (le_of_eq (hc.trans hcard.symm))
  let : (U.subgroupOf d.H).Normal := heq ▸ inferInstance
  have hH : d.H ≤ normalizer (U : Set C) := by
    have hn := (U.subgroupOf d.H).le_normalizer_map d.H.subtype
    rw [(U.subgroupOf d.H).normalizer_eq_top, ← MonoidHom.range_eq_map,
      range_subtype, map_subgroupOf_eq_of_le d.four_le] at hn
    exact hn
  exact top_unique (d.supplement ▸ sup_le_sup_right hH _)
/-- An elementary-order bound leaves only the three closure orders in Lemma 3.1. -/
public theorem CentralizerSetup.closure_card_cases
    {S : Sylow 2 G} {W : Subgroup S} [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) {i : S} (hiW : i ∈ W)
    (d : CentralizerSetup S W i)
    (hbound : ∀ E : Subgroup S, IsElementaryAbelian 2 E → Nat.card E ≤ 16) :
    Nat.card d.closure = 4 ∨ Nat.card d.closure = 8 ∨ Nat.card d.closure = 16 := by
  let C := centralizer ({(i : G)} : Set G)
  let V := d.closure.map d.H.subtype
  let E₀ := V.map C.subtype
  let E := E₀.subgroupOf (S : Subgroup G)
  let : IsElementaryAbelian 2 d.closure := d.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.map_subtype
  have hES : E₀ ≤ S := by
    rintro x ⟨v, hv, rfl⟩
    have ht := d.closure_le hv
    rw [d.sylow_eq] at ht
    exact ht
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hES
  have hcard : Nat.card E = Nat.card d.closure := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv,
      card_map_of_injective C.subtype_injective,
      card_map_of_injective d.H.subtype_injective]
  have hupper : Nat.card d.closure ≤ 16 := by
    rw [← hcard]
    exact hbound E inferInstance
  let U := (W.map (S : Subgroup G).subtype).subgroupOf C
  have hWC : W.map (S : Subgroup G).subtype ≤ C := by
    let : IsElementaryAbelian 2 (W.map (S : Subgroup G).subtype) :=
      IsElementaryAbelian.map_subtype
    intro w hw
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm
      (⟨w, hw⟩ : W.map (S : Subgroup G).subtype)
      (⟨(i : G), mem_map_of_mem _ hiW⟩ : W.map (S : Subgroup G).subtype))
  have hfour : Nat.card (U.subgroupOf d.H) = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe d.four_le).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv,
      card_map_of_injective (S : Subgroup G).subtype_injective, hW]
  have hlower : 4 ≤ Nat.card d.closure := by
    rw [← hfour]
    exact card_le_of_le le_normalClosure
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 d.closure).exists_card_eq
  change Nat.card d.closure = 2 ^ n at hn
  have hn4 : n ≤ 4 := by
    by_contra! h
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) h
    norm_num at hp
    omega
  rw [hn] at hlower ⊢
  interval_cases n
  all_goals norm_num at hlower
  all_goals norm_num

end Stellmacher.Recognition.NormalEightSeparatedCentralizers
