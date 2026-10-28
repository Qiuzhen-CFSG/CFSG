module
public import Theory.GroupTheory.NormalNonabelianSixteenCenter
public import Theory.GroupTheory.EmbeddedCenterMap
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.OneAbelian.CoreModels

/-!
# The original order-thirty-two pair has an abelian core

A nonabelian local core of order sixteen forces the actual Sylow center to
lie in the vertex center. If both cores are nonabelian, both vertices
centralize that same nontrivial subgroup, contradicting source faithfulness.
Consequently the remaining both-nonabelian F.6.5 source branch has common
Sylow order at least sixty-four. The common Sylow and every subgroup map
are the original ones; no finite-group list or upper depth bound is assumed.

Source: Aschbacher–Smith F.1.12 and F.6.5, printed pp.262–264 and 305.
The order-thirty-two marking and the larger depth cases remain separate steps.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.SourceAssembly.BothNonabelian
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

/-- This keeps the actual Sylow center and its embedding in the first vertex. -/
theorem sylow_center_le_left_center
    (h : IsGoldschmidtTriple A B) (hA : generalizedFitting A=pCore 2 A)
    (hcard : Nat.card (pCore 2 A)=16) (hn : ¬ IsMulCommutative (pCore 2 A))
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) :
    (center (S : Subgroup G)).map (S : Subgroup G).subtype≤(center A).map A.subtype := by
  have hSA : (S : Subgroup G)≤A := hS.symm.le.trans inf_le_left
  let T := S.subtype hSA
  have hh := map_mono (f:=A.subtype) (NormalNonabelianSixteen.sylow_center_le_center
    (pCore 2 A) hcard hn (h.local_core_selfCentralizing hA) T)
  rw [map_embeddedCenter _ A.subtype A.subtype_injective] at hh
  have he : (T : Subgroup A).map A.subtype=(S : Subgroup G) := map_subgroupOf_eq_of_le hSA
  rw [he] at hh
  exact hh

omit [Finite G] in
private theorem embedded_center_centralizes (H : Subgroup G) :
    (center H).map H.subtype≤centralizer (H : Set G) := by
  rintro _ ⟨z,hz,rfl⟩
  rw [mem_centralizer_iff]
  intro x hx
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x,hx⟩)

/-- A faithful original pair with overlap order32 has an abelian core. -/
theorem one_core_abelian_of_card_thirty_two
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    (hc : Nat.card (A⊓B : Subgroup G)=32) :
    IsMulCommutative (pCore 2 A) ∨ IsMulCommutative (pCore 2 B) := by
  by_contra! hn
  obtain ⟨S,hS⟩ := h.intersection_sylow
  have hs : Nat.card S=32 := hS ▸ hc
  have hqA : Nat.card (pCore 2 A)=16 := by
    have h1 := h.local_card_eq_three_mul_intersection
    have h2 := SymmetricThreeTwoCore.card_eq h.quotient_left.some
    omega
  have hqB : Nat.card (pCore 2 B)=16 := by
    have h1 := h.symm.local_card_eq_three_mul_intersection
    have h2 := SymmetricThreeTwoCore.card_eq h.quotient_right.some
    rw [inf_comm B A] at h1
    omega
  let Z := (center (S : Subgroup G)).map (S : Subgroup G).subtype
  have hZA : Z≤centralizer (A : Set G) :=
    (sylow_center_le_left_center h hA hqA hn.1 S hS).trans (embedded_center_centralizes A)
  have hZB : Z≤centralizer (B : Set G) :=
    (sylow_center_le_left_center h.symm hB hqB hn.2 S ((inf_comm _ _).trans hS)).trans
      (embedded_center_centralizes B)
  have hZS : Z≤A⊓B := hS.symm ▸ map_subtype_le (center (S : Subgroup G))
  have hz := h.common_normal_eq_bot hcore Z hZS
    ((normal_subgroupOf_iff_le_normalizer (hZS.trans inf_le_left)).mpr
      ((le_centralizer_iff.mp hZA).trans (Subgroup.centralizer_le_normalizer _)))
    ((normal_subgroupOf_iff_le_normalizer (hZS.trans inf_le_right)).mpr
      ((le_centralizer_iff.mp hZB).trans (Subgroup.centralizer_le_normalizer _)))
  have hzc : Nat.card Z=1 := hz ▸ card_bot
  rw [card_map_of_injective (S : Subgroup G).subtype_injective] at hzc
  let : Nontrivial (S : Subgroup G) := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
  let := S.isPGroup'.center_nontrivial
  have hpos := Finite.one_lt_card (α:=center (S : Subgroup G))
  omega

/-- The genuine remaining branch with both cores nonabelian starts at order64. -/
theorem common_sylow_card_ge_sixty_four
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) (hlarge : 8<Nat.card S)
    (hns : ¬ Nonempty (S≃*Multiplicative (ZMod 2)×DihedralGroup 4))
    (hna : ¬ IsMulCommutative (pCore 2 A)) (hnb : ¬ IsMulCommutative (pCore 2 B)) :
    64≤Nat.card S := by
  have h16 := BothSixteen.common_sylow_card_ne_sixteen h hcore hA hB S hS hns
  have h32 : Nat.card S≠32 := by
    intro hc
    exact (one_core_abelian_of_card_thirty_two h hcore hA hB (hS ▸ hc)).elim hna hnb
  obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
  rw [hn] at hlarge h16 h32 ⊢
  by_cases h6 : 6≤n
  · exact Nat.pow_le_pow_right (by decide : 0<2) h6
  · interval_cases n <;> norm_num at *
end CFSG.Quasithin.ChapterF.SourceAssembly.BothNonabelian
