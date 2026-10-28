module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.Binary.NaturalExtension
public import Theory.SpecificGroups.AlternatingSix.SylowInvolutionFive
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# An order-five inverter in the core-free binary symplectic source

A subgroup of order two normalized by the source Sylow centralizes that
Sylow. Faithful conjugation embeds the core-free minimal parabolic in
Aut(A₆), and minimal parabolicity forces its Sylow image to escape natural
S₆. The intrinsic Sylow centralizer calculation therefore places the given
involution in A₆, where involution conjugacy supplies an inverted five-cycle.
All elements in the conclusion remain in the original source group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.2.17,
printed p.230. This discharges the order-five inversion step after the
source elementary image has been proved to have order two.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
open AlternatingSix.ShadowLocal AlternatingSix.ShadowLocal.Identification
variable {G : Type*} [Group G] [Finite G]

private theorem coreFree_sylow_central_involution_mem_component
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hcore : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup G) [K.Normal] [IsSimpleGroup K] (hKa : ¬ IsMulCommutative K)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (eK : K ≃* alternatingGroup (Fin 6))
    (v : G) (hvT : v ∈ (T : Subgroup G)) (hv2 : v ^ 2 = 1)
    (hcv : ∀ t ∈ (T : Subgroup G), t * v = v * t) : v ∈ K := by
  have hc := (Structure.Sporadic.faithful_normal_structure T hP hcore K hKa hgen).2
  let a : G →* AutA6 := (MulAut.congr eK).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have ha : Function.Injective a := (MulAut.congr eK).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot K hc)
  have hact (k : K) : a k = MulAut.conj (eK k) := by
    change MulAut.congr eK (MulAut.conjNormal (k : G)) = _
    rw [MulAut.conjNormal_val, MulAut.congr_conj]
  have hi : K.map a = AlternatingSix.ShadowLocal.inner := by
    ext x
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨eK ⟨k,hk⟩,(hact ⟨k,hk⟩).symm⟩
    · rintro ⟨k,rfl⟩
      exact ⟨eK.symm k,(eK.symm k).property,(hact (eK.symm k)).trans
        (congrArg MulAut.conj (eK.apply_symm_apply k))⟩
  let S := (T : Subgroup G).map a
  have hgena : AlternatingSix.ShadowLocal.inner ⊔ S = a.range := by
    rw [←hi,←Subgroup.map_sup,hgen,←MonoidHom.range_eq_map]
  have hout : ¬ S ≤ natural := by
    intro hS
    apply not_minimal_of_natural_extension T a ha
      (hgena ▸ (show AlternatingSix.ShadowLocal.inner ≤ AlternatingSix.ShadowLocal.inner ⊔ S from le_sup_left))
      (hgena ▸ sup_le inner_le_natural hS) hP
  obtain ⟨P,hSP⟩ := (T.isPGroup'.map a).exists_le_sylow
  obtain ⟨R,hR⟩ := T.exists_subgroupOf_eq_of_normal K
  have hK : Nat.card K = 360 := (Nat.card_congr eK.toEquiv).trans card_A6
  have hRc : Nat.card R = 8 := by
    rw [R.card_eq_multiplicity,hK]
    decide +kernel
  let F := ((R : Subgroup K).map K.subtype).map a
  have hFc : Nat.card F = 8 := by
    rw [show Nat.card F = Nat.card ((R : Subgroup K).map K.subtype) from card_map_of_injective ha,
      card_map_of_injective K.subtype_injective,hRc]
  have hFS : F ≤ S := by
    apply map_mono
    rw [hR,subgroupOf_map_subtype]
    exact inf_le_left
  have hFI : F ≤ AlternatingSix.ShadowLocal.inner := by
    rw [←hi]
    exact map_mono (map_subtype_le _)
  have hFEq : F = (sylowInner P).map (P : Subgroup AutA6).subtype := by
    apply eq_of_le_of_card_ge
    · intro x hx
      exact ⟨⟨x,hSP (hFS hx)⟩,hFI hx,rfl⟩
    · rw [card_map_of_injective (P : Subgroup AutA6).subtype_injective,sylowInner_card,hFc]
  have hinnerS : sylowInner P ≤ S.subgroupOf (P : Subgroup AutA6) := by
    intro x hx
    exact hFS (hFEq.symm ▸ mem_map_of_mem (P : Subgroup AutA6).subtype hx)
  have houtS : ¬ S.subgroupOf (P : Subgroup AutA6) ≤ sylowNatural P := by
    intro hh
    apply hout
    intro x hx
    exact hh (show (⟨x,hSP hx⟩ : P) ∈ S.subgroupOf (P : Subgroup AutA6) from hx)
  let w : P := ⟨a v,hSP (mem_map_of_mem a hvT)⟩
  have hw2 : w ^ 2 = 1 := Subtype.ext (by
    change a v ^ 2 = 1
    rw [←map_pow,hv2,map_one])
  have hwc : ∀ x ∈ S.subgroupOf (P : Subgroup AutA6), x * w = w * x := by
    intro x hx
    obtain ⟨t,ht,he⟩ := hx
    apply Subtype.ext
    change (x : AutA6) * a v = a v * (x : AutA6)
    change a t = (x : AutA6) at he
    rw [←he,←map_mul,←map_mul,hcv t ht]
  have hwI := central_involution_mem_inner_of_escape P _ hinnerS houtS w hw2 hwc
  change a v ∈ AlternatingSix.ShadowLocal.inner at hwI
  rw [←hi] at hwI
  obtain ⟨k,hk,hkv⟩ := hwI
  exact ha hkv ▸ hk

/-- A normal subgroup of order two in the original Sylow contains an inverter
of an actual order-five element in the same core-free minimal parabolic. -/
theorem coreFree_exists_inverted_five
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hcore : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup G) [K.Normal] [IsSimpleGroup K] (hKa : ¬ IsMulCommutative K)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (eK : K ≃* alternatingGroup (Fin 6))
    (W : Subgroup G) (hWT : W ≤ T)
    (hn : (T : Subgroup G) ≤ normalizer (W : Set G)) (hW : Nat.card W = 2) :
    ∃ v ∈ W, v ≠ 1 ∧ ∃ r : G, orderOf r = 5 ∧ v * r * v⁻¹ = r⁻¹ := by
  obtain ⟨v,hv,_⟩ := (Nat.card_eq_two_iff' (1 : W)).mp hW
  have hv1 : (v : G) ≠ 1 := fun hh => hv (Subtype.ext hh)
  have hv2 : (v : G) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := v)
    rw [hW] at hh
    exact congrArg Subtype.val hh
  have hcv : ∀ t ∈ (T : Subgroup G), t * (v : G) = v * t := by
    intro t ht
    exact (normalizer_le_centralizer_of_card_two W hW (hn ht) v v.property).symm
  have hvK := coreFree_sylow_central_involution_mem_component
    T hP hcore K hKa hgen eK v (hWT v.property) hv2 hcv
  let u : K := ⟨v,hvK⟩
  have hu : orderOf u = 2 := orderOf_eq_prime (Subtype.ext hv2)
    (fun hh => hv1 (congrArg Subtype.val hh))
  obtain ⟨r,hr,hvr⟩ := involution_inverts_five (eK u) ((eK.orderOf_eq u).trans hu)
  refine ⟨v,v.property,hv1,(eK.symm r : G),?_,?_⟩
  · exact (orderOf_injective K.subtype K.subtype_injective (eK.symm r)).trans
      ((eK.symm.orderOf_eq r).trans hr)
  · have hh := congrArg eK.symm hvr
    simp only [map_mul,map_inv,MulEquiv.symm_apply_apply] at hh
    exact congrArg Subtype.val hh
end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
