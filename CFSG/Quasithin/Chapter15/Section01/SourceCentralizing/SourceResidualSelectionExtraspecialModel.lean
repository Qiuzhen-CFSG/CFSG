module

public import CFSG.Quasithin.ChapterD.Section03.SourceSetup
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PGroup.ExtraspecialThreeInvolutionEndpoints
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.Representation.ExtraspecialBinarySix.CubicSelection
public import Theory.Representation.BinaryOffender.CentralSectionAction

/-!
# Proper Sylow overgroups in the extraspecial residual row

Let P be the actual two-residual, extraspecial of order27, and let the
Sylow two-subgroup S act irreducibly on P/Phi(P). A proper overgroup A of S
meets P inside its center; the residual supplement then gives A=(A∩P)S.
Thus every proper non-two overgroup is the same literal subgroup Z(P)S.

Source application: Aschbacher--Smith 15.1.2 and 15.1.14, printed
pp.1086 and 1090. No later residual centralization is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.SourceExtraspecialModel
variable {D : Type*} [Group D] [Finite D]
  (S : Sylow 2 D) [IsExtraspecial 3 (pResidual 2 D)]
  (hI : ChapterD.Section03.FrattiniIrreducible (S : Subgroup D)
    (pResidual 2 D) le_normalizer_of_normal)

include hI in
/-- Every proper Sylow-containing overgroup meets the residual only in its center. -/
theorem proper_intersection_le_center (A : Subgroup D)
    (hSA : (S : Subgroup D) ≤ A) (hne : A ≠ ⊤) :
    pResidual 2 D ⊓ A ≤ (center (pResidual 2 D)).map (pResidual 2 D).subtype := by
  let P := pResidual 2 D
  let N := P ⊓ A
  let q := QuotientGroup.mk' (frattini P)
  let B := (N.subgroupOf P).map q
  have hs : ∀ t : S, ∀ b ∈ B,
      ChapterD.Section03.frattiniAction (S : Subgroup D) P le_normalizer_of_normal t b ∈ B := by
    rintro t b ⟨n,hn,rfl⟩
    refine ⟨MulAut.conjNormal (t : D) n,?_,?_⟩
    · exact ⟨(MulAut.conjNormal (t : D) n).property,
        A.mul_mem (A.mul_mem (hSA t.property) hn.2) (A.inv_mem (hSA t.property))⟩
    · exact (quotientAut_apply_mk (frattini P) (MulAut.conjNormal (t : D)) n).symm
  rcases hI B hs with hb | ht
  · have hn : N.subgroupOf P ≤ frattini P := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff (N.subgroupOf P)).mp hb
    rw [IsExtraspecial.frattini_eq_center_three] at hn
    have hh := map_mono (f := P.subtype) hn
    rwa [map_subgroupOf_eq_of_le (show N ≤ P from inf_le_left)] at hh
  · have hn : N.subgroupOf P = ⊤ := by
      apply frattini_nongenerating
      have hh := congrArg (Subgroup.comap q) ht
      simpa only [B,comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh
    have hPA : P ≤ A := (subgroupOf_eq_top.mp hn).trans inf_le_right
    apply False.elim (hne ?_)
    apply top_unique
    rw [← pResidual_sup_sylow_eq_top S]
    exact sup_le hPA hSA

omit [IsExtraspecial 3 (pResidual 2 D)] in
/-- The literal residual intersection supplements S in every overgroup of S. -/
theorem overgroup_eq_intersection_sup (A : Subgroup D) (hSA : (S : Subgroup D) ≤ A) :
    A = (pResidual 2 D ⊓ A) ⊔ (S : Subgroup D) := by
  apply le_antisymm
  · intro a ha
    have hatop : a ∈ pResidual 2 D ⊔ (S : Subgroup D) := by
      rw [pResidual_sup_sylow_eq_top S]
      trivial
    obtain ⟨p,hp,s,hs,hps⟩ := mem_sup_of_normal_left.mp hatop
    have hpA : p ∈ A := by
      have h := A.mul_mem ha (A.inv_mem (hSA hs))
      rw [←hps,mul_inv_cancel_right] at h
      exact h
    rw [←hps]
    exact ((pResidual 2 D ⊓ A) ⊔ (S : Subgroup D)).mul_mem
      (mem_sup_left ⟨hp,hpA⟩) (mem_sup_right hs)
  · exact sup_le inf_le_right hSA

include hI in
/-- The only proper overgroups of S are S itself and the central-cubic supplement. -/
theorem proper_overgroup_cases (A : Subgroup D)
    (hSA : (S : Subgroup D) ≤ A) (hne : A ≠ ⊤) :
    A = (S : Subgroup D) ∨
      A = (center (pResidual 2 D)).map (pResidual 2 D).subtype ⊔ (S : Subgroup D) := by
  let P := pResidual 2 D
  let Z := (center P).map P.subtype
  let N := P ⊓ A
  have hNZ : N ≤ Z := proper_intersection_le_center S hI A hSA hne
  have hZc : Nat.card Z = 3 := by
    rw [card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P]
  have hd : Nat.card N ∣ 3 := hZc ▸ card_dvd_of_le hNZ
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with hc | hc
  · have hb : N = ⊥ := card_eq_one.mp hc
    left
    rw [overgroup_eq_intersection_sup S A hSA,show pResidual 2 D ⊓ A = ⊥ from hb,bot_sup_eq]
  · have he : N = Z := eq_of_le_of_card_ge hNZ (by rw [hc,hZc])
    right
    rw [overgroup_eq_intersection_sup S A hSA,show pResidual 2 D ⊓ A = Z from he]

include hI in
/-- Every proper non-two overgroup is the same original central-cubic supplement. -/
theorem proper_non_two_overgroup_eq (A : Subgroup D)
    (hSA : (S : Subgroup D) ≤ A) (hne : A ≠ ⊤) (hn : ¬ IsPGroup 2 A) :
    A = (center (pResidual 2 D)).map (pResidual 2 D).subtype ⊔ (S : Subgroup D) := by
  exact (proper_overgroup_cases S hI A hSA hne).resolve_left
    (fun he => hn (he ▸ S.isPGroup'))

include hI in
/-- The literal central-cubic supplement has three times the Sylow order. -/
theorem proper_non_two_overgroup_card (A : Subgroup D)
    (hSA : (S : Subgroup D) ≤ A) (hne : A ≠ ⊤) (hn : ¬ IsPGroup 2 A) :
    Nat.card A = 3 * Nat.card S := by
  let P := pResidual 2 D
  let Z := (center P).map P.subtype
  have hZc : Nat.card Z = 3 := by
    rw [card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P]
  have hd : Disjoint Z (S : Subgroup D) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
    rw [hZc,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  rw [proper_non_two_overgroup_eq S hI A hSA hne hn]
  change Nat.card (Z ⊔ (S : Subgroup D) : Subgroup D) = _
  rw [card_sup_eq_mul_of_normalizes_of_disjoint Z (S : Subgroup D)
    le_normalizer_of_normal hd,hZc]

include hI in
/-- S has relative index three in every proper non-two overgroup. -/
theorem proper_non_two_overgroup_relIndex (A : Subgroup D)
    (hSA : (S : Subgroup D) ≤ A) (hne : A ≠ ⊤) (hn : ¬ IsPGroup 2 A) :
    (S : Subgroup D).relIndex A = 3 := by
  have he := relIndex_mul_relIndex (⊥ : Subgroup D) (S : Subgroup D) A bot_le hSA
  simp only [relIndex_bot_left] at he
  rw [proper_non_two_overgroup_card S hI A hSA hne hn,mul_comm 3] at he
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := S)) he

include hI in
/-- A proper non-two overgroup has index nine in the original whole actor. -/
theorem proper_non_two_overgroup_index (hP : Nat.card (pResidual 2 D) = 27)
    (A : Subgroup D) (hSA : (S : Subgroup D) ≤ A) (hne : A ≠ ⊤)
    (hn : ¬ IsPGroup 2 A) : A.index = 9 := by
  let P := pResidual 2 D
  let Z := (center P).map P.subtype
  have hZP : Z ≤ P := map_subtype_le _
  have hZc : Nat.card Z = 3 := by
    rw [card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P]
  have hd : Disjoint P (S : Subgroup D) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
    rw [hP,hn]
    exact (by decide : Nat.Coprime 27 2).pow_right n
  have hDc : Nat.card D = 27 * Nat.card S := by
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint P (S : Subgroup D)
      le_normalizer_of_normal hd
    rw [pResidual_sup_sylow_eq_top S,card_top,hP] at hh
    exact hh
  have hAc : Nat.card A = 3 * Nat.card S := by
    rw [proper_non_two_overgroup_eq S hI A hSA hne hn]
    change Nat.card (Z ⊔ (S : Subgroup D) : Subgroup D) = _
    rw [card_sup_eq_mul_of_normalizes_of_disjoint Z (S : Subgroup D)
      le_normalizer_of_normal (hd.mono hZP le_rfl),hZc]
  have hi := A.card_mul_index
  rw [hAc,hDc] at hi
  have he : Nat.card S * (3 * A.index) = Nat.card S * 27 := by nlinarith [hi]
  have hh := Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := S)) he
  omega

include hI in
/-- Proper Sylow overgroups normalize every S-normalized subgroup commuting
with the residual center. -/
theorem proper_overgroup_normalizes (R : Subgroup D)
    (hSR : (S : Subgroup D) ≤ normalizer (R : Set D))
    (hRZ : R ≤ centralizer ((center (pResidual 2 D)).map (pResidual 2 D).subtype : Set D))
    (A : Subgroup D) (hSA : (S : Subgroup D) ≤ A) (hne : A ≠ ⊤) :
    A ≤ normalizer (R : Set D) := by
  rcases proper_overgroup_cases S hI A hSA hne with he | he
  · exact he ▸ hSR
  · rw [he]
    exact sup_le ((le_centralizer_iff.mp hRZ).trans (centralizer_le_normalizer _)) hSR

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
open Representation Representation.BinaryOffender

include hI in
/-- Every proper Sylow overgroup normalizes the original small involution. -/
theorem proper_overgroup_normalizes_small_involution
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hP : Nat.card (pResidual 2 D) = 27) (h6 : Module.finrank (ZMod 2) W = 6)
    (t : D) (ht : t ^ 2 = 1) (hr : fixedCodim ρ (zpowers t) ≤ 2)
    (hSt : (S : Subgroup D) ≤ normalizer (zpowers t : Set D))
    (A : Subgroup D) (hSA : (S : Subgroup D) ≤ A) (hne : A ≠ ⊤) :
    A ≤ normalizer (zpowers t : Set D) := by
  apply proper_overgroup_normalizes S hI (zpowers t) hSt _ A hSA hne
  apply zpowers_le.mpr
  exact ExtraspecialBinarySix.small_involution_centralizes_center ρ hf
    (pResidual 2 D) hP h6 t ht hr

include hI in
/-- Proper Sylow overgroups preserve the fixed space of the original small involution. -/
theorem proper_overgroup_stabilizes_small_fixed
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hP : Nat.card (pResidual 2 D) = 27) (h6 : Module.finrank (ZMod 2) W = 6)
    (t : D) (ht : t ^ 2 = 1) (hr : fixedCodim ρ (zpowers t) ≤ 2)
    (hSt : (S : Subgroup D) ≤ normalizer (zpowers t : Set D))
    (A : Subgroup D) (hSA : (S : Subgroup D) ≤ A) (hne : A ≠ ⊤) :
    A ≤ subspaceStabilizer ρ (fixedSpace ρ (zpowers t)) := by
  exact fixedSpace_stable_of_normalizes ρ
    (proper_overgroup_normalizes_small_involution S hI ρ hf hP h6 t ht hr hSt A hSA hne)

end CFSG.Quasithin.Chapter15.Section01.SourceExtraspecialModel
