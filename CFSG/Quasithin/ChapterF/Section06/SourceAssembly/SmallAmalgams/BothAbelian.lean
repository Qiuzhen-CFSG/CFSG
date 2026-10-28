module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.BothEight
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.BothSixteen.Rigidity
public import Theory.GroupTheory.IndexThreeCenterBound
public import Theory.GroupTheory.IndexTwoIntersection

/-!
# Faithful binary amalgams with two abelian local cores

The distinct local two-cores generate the common Sylow subgroup. Their
intersection therefore centralizes that subgroup and has half the order of
either core. Two conjugate Sylow subgroups generate each vertex, so the
index-three center bound controls each core by its vertex center. Both vertex
centers lie in the core intersection, and faithfulness makes their own
intersection trivial. The product formula forces common Sylow order at most
sixteen. The checked small-branch rigidity theorems then give the original
PSL₃(2) or Sp₄(2) amalgam, retaining both overlap maps.

Source: the abelian-core branch of Aschbacher–Smith F.1.12 and F.6.5,
printed pp.262–263 and 305. No universal amalgam bound is assumed here.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.SourceAssembly.BothAbelian
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
private abbrev Q (A : Subgroup G) := (pCore 2 A).map A.subtype
private abbrev Z (A : Subgroup G) := (center A).map A.subtype

private theorem two_mul_core_card (h : IsGoldschmidtTriple A B) :
    2 * Nat.card (Q A) = Nat.card (A ⊓ B : Subgroup G) := by
  let K := (Q A).subgroupOf (A ⊓ B)
  have hh := K.index_mul_card
  have hK : Nat.card K = Nat.card (Q A) := by
    exact Nat.card_congr (subgroupOfEquivOfLe h.local_twoCore_le_intersection).toEquiv
  have hiK : K.index = 2 := h.left_core_index
  rw [hiK, hK] at hh
  exact hh

private theorem center_le_core (h : IsGoldschmidtTriple A B)
    (hA : generalizedFitting A=pCore 2 A) : Z A ≤ Q A :=
  map_mono ((center_le_centralizer _).trans (h.local_core_selfCentralizing hA))

omit [Finite G] in
private theorem center_centralizes (A : Subgroup G) : Z A ≤ centralizer (A : Set G) := by
  rintro _ ⟨a,ha,rfl⟩
  rw [mem_centralizer_iff]
  intro b hb
  exact congrArg Subtype.val ((mem_center_iff.mp ha) ⟨b,hb⟩)

private theorem center_le_other_core (h : IsGoldschmidtTriple A B)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B) :
    Z A ≤ Q B := by
  intro x hx
  have hxB : x ∈ B := (h.local_twoCore_le_intersection (center_le_core h hA hx)).2
  have hxc : (⟨x,hxB⟩ : B) ∈ centralizer (pCore 2 B : Set B) := by
    rw [mem_centralizer_iff]
    intro b hb
    apply Subtype.ext
    exact mem_centralizer_iff.mp (center_centralizes A hx) b
      ((h.symm.local_twoCore_le_intersection (mem_map_of_mem B.subtype hb)).2)
  exact mem_map_of_mem B.subtype (h.symm.local_core_selfCentralizing hB hxc)

private theorem center_intersection (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥) (hA : generalizedFitting A=pCore 2 A) :
    Z A ⊓ Z B = ⊥ := by
  have hle : Z A ⊓ Z B ≤ A ⊓ B :=
    inf_le_left.trans ((center_le_core h hA).trans h.local_twoCore_le_intersection)
  apply h.common_normal_eq_bot hcore _ hle
  · apply (normal_subgroupOf_iff_le_normalizer (hle.trans inf_le_left)).mpr
    exact ((le_centralizer_iff.mp (inf_le_left.trans (center_centralizes A))).trans
      (Subgroup.centralizer_le_normalizer _))
  · apply (normal_subgroupOf_iff_le_normalizer (hle.trans inf_le_right)).mpr
    exact ((le_centralizer_iff.mp (inf_le_right.trans (center_centralizes B))).trans
      (Subgroup.centralizer_le_normalizer _))

private theorem cores_generate_of_large (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥) (hbig : 16 < Nat.card (A⊓B : Subgroup G)) :
    Q A ⊔ Q B = A⊓B := by
  have hqa := two_mul_core_card h
  have hqb := two_mul_core_card h.symm
  rw [inf_comm B A] at hqb
  have hout : ¬ Q B ≤ Q A := by
    intro hle
    have he : Q B=Q A := eq_of_le_of_card_ge hle (by omega)
    have hnA : ((Q A).subgroupOf A).Normal :=
      (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mpr h.left_core_normalized
    have hnB : ((Q A).subgroupOf B).Normal := by
      rw [←he]
      exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mpr h.symm.left_core_normalized
    have hh := h.common_normal_eq_bot hcore (Q A) h.local_twoCore_le_intersection hnA hnB
    rw [hh,card_bot] at hqa
    omega
  have hQT : Q A ≤ A⊓B := h.local_twoCore_le_intersection
  have hRT : Q B ≤ A⊓B := by simpa only [inf_comm B A] using h.symm.local_twoCore_le_intersection
  have hidx := relIndex_mul_relIndex (Q A) (Q A⊔Q B) (A⊓B) le_sup_left (sup_le hQT hRT)
  rw [h.left_core_index] at hidx
  have hdiv : (Q A).relIndex (Q A⊔Q B) ∣ 2 := ⟨_,hidx.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
  · exact (hout (le_sup_right.trans (relIndex_eq_one.mp h1))).elim
  · rw [h2] at hidx
    exact le_antisymm (sup_le hQT hRT) (relIndex_eq_one.mp (by omega))

private theorem core_intersection_centralizes (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥) (hbig : 16 < Nat.card (A⊓B : Subgroup G))
    [IsMulCommutative (pCore 2 A)] [IsMulCommutative (pCore 2 B)] :
    Q A⊓Q B ≤ centralizer ((A⊓B : Subgroup G) : Set G) := by
  rw [le_centralizer_iff]
  rw [← cores_generate_of_large h hcore hbig]
  exact sup_le ((Q A).le_centralizer.trans (centralizer_le inf_le_left))
    ((Q B).le_centralizer.trans (centralizer_le inf_le_right))

private theorem core_intersection_card (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥) (hbig : 16 < Nat.card (A⊓B : Subgroup G)) :
    2 * Nat.card (Q A⊓Q B : Subgroup G) = Nat.card (Q A) := by
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes (Q A) (Q B)
    ((h.symm.local_twoCore_le_intersection.trans inf_le_right).trans h.left_core_normalized)
  rw [cores_generate_of_large h hcore hbig] at hh
  have hqa := two_mul_core_card h
  have hqb := two_mul_core_card h.symm
  rw [inf_comm B A] at hqb
  have hp := Nat.card_pos (α := Q A)
  nlinarith

private theorem center_card_lower (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥) (hbig : 16 < Nat.card (A⊓B : Subgroup G))
    [IsMulCommutative (pCore 2 A)] [IsMulCommutative (pCore 2 B)] :
    Nat.card (Q A) ≤ 4 * Nat.card (Z A) := by
  let T := (A⊓B).subgroupOf A
  let W := (Q A⊓Q B).subgroupOf A
  have hTc : Nat.card T = Nat.card (A⊓B : Subgroup G) :=
    Nat.card_congr (subgroupOfEquivOfLe (show A⊓B≤A from inf_le_left)).toEquiv
  have hWc : Nat.card W = Nat.card (Q A⊓Q B : Subgroup G) :=
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans (map_subtype_le _))).toEquiv
  have hQc : Nat.card (Q A) = Nat.card (pCore 2 A) := card_map_of_injective A.subtype_injective
  have hZc : Nat.card (Z A) = Nat.card (center A) := card_map_of_injective A.subtype_injective
  have hi : T.index=3 := by
    have hh := T.index_mul_card
    rw [hTc,h.local_card_eq_three_mul_intersection] at hh
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := (A⊓B : Subgroup G))) hh
  have hn : ¬ T.Normal := by
    intro hn
    let := hn
    obtain ⟨S,hS⟩ := h.intersection_sylow
    let eT : T ≃* (A⊓B : Subgroup G) := subgroupOfEquivOfLe inf_le_left
    have hp : IsPGroup 2 T := IsPGroup.of_injective
      (S.isPGroup'.to_le (show A⊓B≤(S : Subgroup G) from hS.le))
      eT.toMonoidHom eT.injective
    have hle : T≤pCore 2 A := le_sSup ⟨hn,hp⟩
    have hc := card_le_of_le hle
    have hh := two_mul_core_card h
    rw [hTc,←hQc] at hc
    omega
  have hWQ : W≤pCore 2 A := by
    rintro x hx
    obtain ⟨a,ha,he⟩ := hx.1
    exact (Subtype.ext he : a=x) ▸ ha
  have hWT : W≤centralizer (T : Set A) := by
    intro w hw
    rw [mem_centralizer_iff]
    intro t ht
    apply Subtype.ext
    exact mem_centralizer_iff.mp (core_intersection_centralizes h hcore hbig hw) t ht
  have hw : 2*Nat.card W=Nat.card (pCore 2 A) := by
    rw [hWc,←hQc]
    exact core_intersection_card h hcore hbig
  rw [hQc,hZc]
  exact center_card_bound_of_abelian_normal_subgroup (pCore 2 A) T W hi hn hWQ hWT hw

/-- The source pair has common Sylow order at most sixteen when both cores are abelian. -/
theorem intersection_card_le_sixteen (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsMulCommutative (pCore 2 A)] [IsMulCommutative (pCore 2 B)] :
    Nat.card (A⊓B : Subgroup G) ≤ 16 := by
  by_contra! hbig
  have hcA := center_card_lower h hcore hbig
  have hcB := center_card_lower h.symm hcore (by simpa only [inf_comm B A] using hbig)
  have hZA : Z A≤Q A⊓Q B := le_inf (center_le_core h hA) (center_le_other_core h hA hB)
  have hZB : Z B≤Q A⊓Q B := le_inf (center_le_other_core h.symm hB hA) (center_le_core h.symm hB)
  have hn : Z B≤normalizer (Z A : Set G) :=
    (hZB.trans (inf_le_left.trans (map_subtype_le _))).trans
      ((le_centralizer_iff.mp (center_centralizes A)).trans (Subgroup.centralizer_le_normalizer _))
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes (Z A) (Z B) hn
  rw [center_intersection h hcore hA,card_bot,one_mul] at hh
  have hle := card_le_of_le (sup_le hZA hZB)
  have hq := core_intersection_card h hcore hbig
  have ha := two_mul_core_card h
  have hb := two_mul_core_card h.symm
  rw [inf_comm B A] at hb
  nlinarith [Nat.mul_le_mul hcA hcB]

/-- Characteristic two already excludes common Sylow order at most four. -/
theorem intersection_card_gt_four (h : IsGoldschmidtTriple A B)
    (hA : generalizedFitting A=pCore 2 A) :
    4 < Nat.card (A⊓B : Subgroup G) := by
  by_contra! hsmall
  have hh := two_mul_core_card h
  have hQc : Nat.card (Q A) = Nat.card (pCore 2 A) := card_map_of_injective A.subtype_injective
  rw [hQc] at hh
  have hpos := Nat.card_pos (α := pCore 2 A)
  have hc : pCore 2 A ≤ center A := by
    have hcases : Nat.card (pCore 2 A)=1 ∨ Nat.card (pCore 2 A)=2 := by omega
    rcases hcases with h1 | h2
    · rw [Subgroup.card_eq_one.mp h1]
      exact bot_le
    · exact Subgroup.central_of_normal_card_two _ h2
  have ht : centralizer (pCore 2 A : Set A)=⊤ := centralizer_eq_top_iff_subset.mpr hc
  have hqt : pCore 2 A=⊤ := top_unique (ht ▸ h.local_core_selfCentralizing hA)
  have he : Nat.card (pCore 2 A)=Nat.card A := by
    rw [hqt]
    exact Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A)≃*A).toEquiv
  have ha := SymmetricThreeTwoCore.card_eq h.quotient_left.some
  omega

/-- With abelian local cores the original overlap has order eight or sixteen. -/
theorem intersection_card_cases (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsMulCommutative (pCore 2 A)] [IsMulCommutative (pCore 2 B)] :
    Nat.card (A⊓B : Subgroup G)=8 ∨ Nat.card (A⊓B : Subgroup G)=16 := by
  have hlo := intersection_card_gt_four h hA
  have hhi := intersection_card_le_sixteen h hcore hA hB
  obtain ⟨S,hS⟩ := h.intersection_sylow
  obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
  rw [hS,hn] at hlo hhi ⊢
  have hn5 : n<5 := by
    by_contra! hge
    have hp := Nat.pow_le_pow_right (by decide : 1≤2) hge
    norm_num at hp
    omega
  interval_cases n <;> norm_num at *

/-- Complete compatible marking of the original both-abelian-core branch.
There is no overlap order or local-model premise. -/
theorem marked_amalgam (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsMulCommutative (pCore 2 A)] [IsMulCommutative (pCore 2 B)] :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups A (A⊓B) B inf_le_left inf_le_right)
      GreenBook.LieModels.BinaryLinear.amalgam) ∨
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups A (A⊓B) B inf_le_left inf_le_right)
      (GreenBook.LieModels.SymplecticFour.amalgam (ZMod 2))) := by
  rcases intersection_card_cases h hcore hA hB with h8 | h16
  · exact Or.inl (h.binary_linear_amalgam_of_intersection_card_eight hcore hA hB h8)
  · exact Or.inr (BothSixteen.symplectic_four_amalgam h hcore hA hB h16)

/-- The literal remaining F.6.5/F.6.18 source branch cannot have two abelian
local cores, after the small and split-sixteen cases have been removed. -/
theorem not_both_abelian_of_remaining_source
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) (hlarge : 8<Nat.card S)
    (hns : ¬ Nonempty (S≃*Multiplicative (ZMod 2)×DihedralGroup 4)) :
    ¬ (IsMulCommutative (pCore 2 A) ∧ IsMulCommutative (pCore 2 B)) := by
  rintro ⟨ha,hb⟩
  let := ha
  let := hb
  rcases intersection_card_cases h hcore hA hB with h8 | h16
  · rw [hS] at h8
    omega
  · exact BothSixteen.common_sylow_card_ne_sixteen h hcore hA hB S hS hns (hS ▸ h16)

end CFSG.Quasithin.ChapterF.SourceAssembly.BothAbelian
