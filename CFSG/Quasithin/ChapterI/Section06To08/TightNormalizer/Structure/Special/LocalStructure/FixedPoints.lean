module
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Structure.Special.Construction
public import Theory.GroupAction.FourElementInvolutionLines
public import Theory.GroupTheory.SubgroupConjugation
/-!
# Fixed points in the special branch of I.7.7

For a nonidentity element of the escaping conjugate `B = Rʸ`, the fixed
subgroup on the elementary abelian first normalizer `N` is contained in `S₁`.
The order-two action has displacement contained in its fixed subgroup, and
rank-nullity gives `|N| = |C_N(a)| |[N,a]|`. Since `|N| = |S₁|²`, both
subgroups must equal `S₁`. All commutators below are ambient subgroups.

Source: Aschbacher--Smith, I.7.7, printed p.428 (PDF p.439).
-/

open Subgroup
open scoped IsMulCommutative commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G]
private theorem fixed_square (N Z : Subgroup G) [IsElementaryAbelian 2 N]
    [Nontrivial N] (a : G) (ha : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hn : a ∈ normalizer (N : Set G))
    (hf : N ⊓ centralizer ({a} : Set G) ≤ Z)
    (hc : Nat.card N = Nat.card Z ^ 2) :
    N ⊓ centralizer ({a} : Set G) = Z ∧ ⁅N, zpowers a⁆ = Z := by
  let D := zpowers a
  have hD : D ≤ normalizer (N : Set G) := zpowers_le.mpr hn
  let : Normalizes D N := ⟨hD⟩
  let t : D := ⟨a, mem_zpowers a⟩
  have ht : t ≠ 1 ∧ t ^ 2 = 1 :=
    ⟨fun he => ha (congrArg Subtype.val he), Subtype.ext ha2⟩
  have hDc : Nat.card D = 2 := by rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha]
  let F := FixedPoints.subgroup D N
  let C := commutatorAction D N
  have hF : F.map N.subtype = N ⊓ centralizer ({a} : Set G) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.property, ?_⟩
      change (v : G) ∈ centralizer ({a} : Set G)
      rw [mem_centralizer_iff]
      intro b hb
      have hb : b = a := Set.mem_singleton_iff.mp hb
      subst b
      have he := congrArg Subtype.val (hv t)
      change a * (v : G) * a⁻¹ = (v : G) at he
      exact (mul_inv_eq_iff_eq_mul.mp he)
    · intro hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      intro b
      apply Subtype.ext
      change (b : G) * x * (b : G)⁻¹ = x
      have hxC : a ∈ centralizer ({x} : Set G) := by
        rw [mem_centralizer_iff]
        intro z hz
        obtain rfl := Set.mem_singleton_iff.mp hz
        exact (hx.2 a (Set.mem_singleton _)).symm
      have hbC := (zpowers_le.mpr hxC) b.property
      rw [← hbC x (Set.mem_singleton _), mul_inv_cancel_right]
  have hC : C.map N.subtype = ⁅N, D⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator N D hD
  obtain ⟨hcount, hle⟩ := card_two_action_fixed_commutator_card_data (U := N) t ht hDc
  change Nat.card N = Nat.card F * Nat.card C at hcount
  have hcf : Nat.card C ≤ Nat.card F := card_le_of_le hle
  have hfz : Nat.card F ≤ Nat.card Z := by
    rw [← card_map_of_injective N.subtype_injective, hF]
    exact card_le_of_le hf
  have hfe : Nat.card F = Nat.card Z := by nlinarith
  have hce : Nat.card C = Nat.card Z := by
    have hp : 0 < Nat.card Z := Nat.card_pos
    rw [hc, hfe, pow_two] at hcount
    nlinarith
  have hFZ : F.map N.subtype = Z := eq_of_le_of_card_ge (hF ▸ hf) (by
    rw [card_map_of_injective N.subtype_injective, hfe])
  refine ⟨hF.symm.trans hFZ, ?_⟩
  rw [← hC]
  exact eq_of_le_of_card_ge ((map_mono hle).trans_eq hFZ) (by
    rw [card_map_of_injective N.subtype_injective, hce])

namespace CFSG.Quasithin.ChapterI.Section06To08.TightNormalizerSetup
variable {K : Subgroup G} {g : G} {R S : Subgroup G}
variable (h : TightNormalizerSetup K g R S)
include h
/-- The fixed subgroup and the ambient cyclic commutator are both `S₁`. -/
public theorem special_fixed_commutator_eq_intersection [IsElementaryAbelian 2 R]
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    {y : G}
    (hyN : conjSubgroup R y ≤ S ⊓ normalizer (↑(S ⊓ normalizer (R : Set G)) : Set G))
    (htriv : conjSubgroup R y ⊓ normalizer (R : Set G) = ⊥)
    (a : conjSubgroup R y) (ha : a ≠ 1) :
    (S ⊓ normalizer (R : Set G)) ⊓ centralizer ({(a : G)} : Set G) =
      (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) ∧
    ⁅S ⊓ normalizer (R : Set G), zpowers (a : G)⁆ =
      (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) := by
  let N := S ⊓ normalizer (R : Set G)
  let : IsElementaryAbelian 2 N := h.special_normalizer_elementary e
  let : IsElementaryAbelian 2 (conjSubgroup R y) :=
    IsElementaryAbelian.map (MulAut.conj y).toMonoidHom
  let : Nontrivial N := (N.nontrivial_iff_ne_bot).mpr (by
    intro he
    exact h.hRne (le_bot_iff.mp (he ▸ (le_inf h.hRS R.le_normalizer))))
  apply fixed_square N _ (a : G) (fun he => ha (Subtype.ext he))
    (elemPow_eq_one_of_isElementaryAbelian _ a.property) (hyN a.property).2
    (h.special_fixed_le_intersection e hyN htriv a ha)
  rw [h.special_normalizer_card e, Nat.card_congr e.toEquiv]
end CFSG.Quasithin.ChapterI.Section06To08.TightNormalizerSetup
