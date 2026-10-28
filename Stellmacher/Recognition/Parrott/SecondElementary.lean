module

public import Stellmacher.Recognition.Parrott.CoreInvolution
public import Stellmacher.Recognition.Parrott.CosetSelection
public import Stellmacher.Recognition.Parrott.FixedJoinCentralizer

/-!
# Parrott's second elementary subgroup

Put H=C_G(z), J=O₂(H), and let E be the actual image of J′ in G.
Lemma 3 supplies an involution outside E in (J). Lemma 4 places its
nonzero coset in the orbit of length five. The stabilizer of this coset
is the local normalizer of the literal fixed join
F=⟨a⟩ ∨ (E ∩ C_G(a)), and is a Sylow two-subgroup of (H).

We retain the involution, the fixed join, and compatible local and ambient
Sylow subgroups in one witness package. The fixed-join geometry gives
|F|=32 and |E∩F|=16; the centralizer theorem gives C_G(F)=F.
The existence theorem uses only the original simple N₂-group hypotheses.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–675, especially Lemma 4 and the opening of §2 on p.675.
-/

open Subgroup

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] (z : G)

set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
local notation "J" => pCore 2 H
set_option quotPrecheck false in
local notation "DH" => (commutator J).map (J).subtype
set_option quotPrecheck false in
local notation "E" => (commutator J).map ((H).subtype.comp (J).subtype)

/-- Actual witnesses for the opening of Parrott's normalizer and fusion
argument. The subgroup `F` is specified as the fixed join, and the two
Sylow subgroups agree under the centralizer's inclusion in the ambient group. -/
public structure ParrottSecondElementaryData where
  a : H
  a_mem_core : a ∈ J
  a_order : orderOf a = 2
  a_not_mem_derived : a ∉ DH
  coset_index : (centralizer ({QuotientGroup.mk' DH a} : Set (H ⧸ DH))).index = 5
  localSylow : Sylow 2 H
  sylow : Sylow 2 G
  sylow_map : (sylow : Subgroup G) = (localSylow : Subgroup H).map (H).subtype
  F : Subgroup G
  fixed_join : F = zpowers (a : G) ⊔ (E ⊓ centralizer ({(a : G)} : Set G))
  elementary : IsElementaryAbelian 2 F
  card : Nat.card F = 32
  inf_eq : E ⊓ F = E ⊓ centralizer ({(a : G)} : Set G)
  inf_card : Nat.card (E ⊓ F : Subgroup G) = 16
  ne_derived : F ≠ E
  z_mem_inf : z ∈ E ⊓ F
  le_core : F ≤ (J).map (H).subtype
  le_sylow : F ≤ sylow
  sylow_le_normalizer : (sylow : Subgroup G) ≤ normalizer (F : Set G)
  centralizer_eq : centralizer (F : Set G) = F

/-- Every involution in the two-core outside its derived subgroup gives
the second elementary subgroup, with a compatible Sylow normalizing it. -/
public theorem parrott_second_elementary_of_core_involution [Finite G]
    (h : ParrottCentralizerHypotheses z)
    (a : H) (haJ : a ∈ J) (ha2 : orderOf a = 2) (haD : a ∉ DH) :
    ∃ d : ParrottSecondElementaryData z, d.a = a := by
  have haE : (a : G) ∉ E := by
    intro haE
    have hmap : (DH).map (H).subtype = E := map_map _ _ _
    obtain ⟨b, hb, hba⟩ := hmap.symm ▸ haE
    exact haD ((H).subtype_injective hba ▸ hb)
  have haG : (a : G) ∈ (J).map (H).subtype := mem_map_of_mem (H).subtype haJ
  have haG2 : orderOf (a : G) = 2 := (Subgroup.orderOf_coe a).trans ha2
  have hindex := parrott_core_involution_coset_centralizer_index z h a haJ ha2 haD
  obtain ⟨T, S, hS, hFS, hSN⟩ :=
    parrott_fixed_join_sylow_of_coset_index_five z h a ha2 haD hindex
  obtain ⟨hElem, hcard, hinf, hfixedcard, hne, hz, _, _, hFJ, _⟩ :=
    parrott_core_involution_fixed_join z h (a : G) haG haG2 haE
  refine ⟨{
    a := a
    a_mem_core := haJ
    a_order := ha2
    a_not_mem_derived := haD
    coset_index := hindex
    localSylow := T
    sylow := S
    sylow_map := hS
    F := zpowers (a : G) ⊔ (E ⊓ centralizer ({(a : G)} : Set G))
    fixed_join := rfl
    elementary := hElem
    card := hcard
    inf_eq := hinf
    inf_card := ?_
    ne_derived := hne
    z_mem_inf := hinf.symm ▸ hz
    le_core := hFJ
    le_sylow := hFS
    sylow_le_normalizer := hSN
    centralizer_eq := parrott_core_involution_fixed_join_centralizer z h
      (a : G) haG haG2 haE }, rfl⟩
  rw [hinf]
  exact hfixedcard

/-- From the original hypotheses, construct Parrott's second elementary
subgroup and all witnesses needed for the subsequent normalizer argument. -/
public theorem parrott_second_elementary_exists [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    Nonempty (ParrottSecondElementaryData z) := by
  obtain ⟨a, haJ, ha2, haE⟩ := parrott_core_involution_outside_derived hns hN z h
  obtain ⟨aH, haH, rfl⟩ := haJ
  have haD : aH ∉ DH := by
    intro haD
    have hmap : (DH).map (H).subtype = E := map_map _ _ _
    exact haE (hmap ▸ mem_map_of_mem (H).subtype haD)
  obtain ⟨d, _⟩ := parrott_second_elementary_of_core_involution z h aH haH
    ((Subgroup.orderOf_coe aH).symm.trans ha2) haD
  exact ⟨d⟩

end Stellmacher.Recognition
