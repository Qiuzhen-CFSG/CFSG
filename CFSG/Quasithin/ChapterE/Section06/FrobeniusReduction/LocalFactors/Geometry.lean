module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.Basic
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Sylow

/-!
# The two summands in the exceptional E.6.25 argument

Binary subspaces are embedded as genuine subgroups of G. The fixed space of
one factor in a two-factor decomposition is the other summand, since their
common fixed space is zero. Agreement of actions on the first summand, together
with pointwise fixation of the second, then controls the whole induced action.
An odd local action gives obstruction-family membership and an actual Sylow
subgroup of the enlarged centralizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
E.6.25, printed pp.255–256 (PDF pp.266–267).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
variable {G : Type*} [Group G] {V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Realize a binary subspace of V as a subgroup of the original ambient group. -/
def subspaceGroup (S : Submodule (ZMod 2) (Additive V)) : Subgroup G :=
  S.toAddSubgroup.toSubgroup'.map V.subtype

theorem subspaceGroup_le (S : Submodule (ZMod 2) (Additive V)) : subspaceGroup S ≤ V :=
  map_subtype_le _

theorem mem_subspaceGroup (S : Submodule (ZMod 2) (Additive V)) (v : Additive V) :
    (v.toMul : G) ∈ subspaceGroup S ↔ v ∈ S := by
  constructor
  · rintro ⟨x, hx, he⟩
    have hv : x = v.toMul := Subtype.ext he
    change Additive.ofMul x ∈ S at hx
    simpa [hv] using hx
  · intro hv
    exact ⟨v.toMul, hv, rfl⟩

theorem subspaceGroup_card (S : Submodule (ZMod 2) (Additive V)) :
    Nat.card (subspaceGroup S) = Nat.card S := by
  apply Nat.card_congr
  exact { toFun := fun x => ⟨Additive.ofMul ⟨x, subspaceGroup_le S x.property⟩,
              (mem_subspaceGroup S _).mp x.property⟩
          invFun := fun x => ⟨x.val.toMul, (mem_subspaceGroup S _).mpr x.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }

/-- Fixed spaces are transported to actual relative centralizers. -/
theorem subspaceGroup_fixedSpace (A : Subgroup G) (hAN : A ≤ normalizer (V : Set G)) :
    subspaceGroup (fixedSpace (automizerRepresentation V) (inducedAutomizer V A)) =
      V ⊓ centralizer (A : Set G) := by
  apply le_antisymm
  · rintro x ⟨v, hv, rfl⟩
    exact ⟨v.property, (mem_fixedSpace_inducedAutomizer V A hAN (Additive.ofMul v)).mp hv⟩
  · intro x hx
    exact (mem_subspaceGroup _ (Additive.ofMul ⟨x, hx.1⟩)).mpr
      ((mem_fixedSpace_inducedAutomizer V A hAN _).mpr hx.2)

private theorem fixes_of_mem_normalClosure {A W : Type*} [Group A]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) A W)
    (C : Subgroup A) (w : W)
    (hf : ∀ a ∈ normalClosure (C : Set A), ρ a w = w) :
    w ∈ fixedSpace ρ (normalClosure (C : Set A)) := fun a => hf a a.property

/-- With exactly two summands and no global fixed vector, the fixed space
of either factor is the other summand. No semisimplicity assumption is needed. -/
theorem fixedSpace_factor_eq_other {A W : Type*} [Group A]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) A W} {C : Subgroup A}
    (D : Representation.RegularCyclicNormalClosure.Decomposition ρ C)
    (hf : fixedSpace ρ (normalClosure (C : Set A)) = ⊥)
    (hs : (⨆ i, D.summand i) = ⊤) (i j : Fin D.size) (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) : fixedSpace ρ (D.factor i) = D.summand j := by
  have hsup : D.summand i ⊔ D.summand j = ⊤ := by
    rw [← hs]
    apply le_antisymm (sup_le (le_iSup _ i) (le_iSup _ j))
    apply iSup_le
    intro k
    rcases htwo k with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  apply le_antisymm
  · intro w hw
    have hwtop : w ∈ D.summand i ⊔ D.summand j := by rw [hsup]; trivial
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hwtop
    have huF : u ∈ fixedSpace ρ (normalClosure (C : Set A)) := by
      apply fixes_of_mem_normalClosure
      have hle : (⨆ k, D.factor k) ≤
          { carrier := {a | ρ a u = u}
            one_mem' := by simp
            mul_mem' := by
              intro a b ha hb
              change ρ a u = u at ha
              change ρ b u = u at hb
              change ρ (a * b) u = u
              rw [map_mul, Module.End.mul_apply, hb, ha]
            inv_mem' := by
              intro a ha
              change ρ a u = u at ha
              have he := congrArg (ρ a⁻¹) ha
              simpa [← Module.End.mul_apply, ← map_mul] using he.symm } := by
        apply iSup_le
        intro k a ha
        rcases htwo k with hk | hk
        · rw [hk] at ha
          have he := hw ⟨a, ha⟩
          change ρ a w = w at he
          rw [← huv, map_add, D.cross_fixed i j hij a ha v hv] at he
          exact add_right_cancel he
        · rw [hk] at ha
          exact D.cross_fixed j i hij.symm a ha u hu
      rw [D.group_eq] at hle
      exact fun a ha => hle ha
    have hu0 : u = 0 := by simpa only [hf, Submodule.mem_bot] using huF
    rw [hu0, zero_add] at huv
    exact huv ▸ hv
  · intro v hv a
    exact D.cross_fixed i j hij a a.property v hv

variable [Finite G]

/-- Binary dimensions are computed on the genuine quotient by the embedded subspace. -/
theorem corank_subspaceGroup (S : Submodule (ZMod 2) (Additive V)) :
    subgroupCorank V (subspaceGroup S) = Module.finrank (ZMod 2) (Additive V ⧸ S) := by
  have hsc : Nat.card ((subspaceGroup S).subgroupOf V) = Nat.card S :=
    (Nat.card_congr (subgroupOfEquivOfLe (subspaceGroup_le S)).toEquiv).trans
      (subspaceGroup_card S)
  have hcard := ((subspaceGroup S).subgroupOf V).card_mul_index
  rw [hsc] at hcard
  have hq := Submodule.card_eq_card_quotient_mul_card S
  have hindex : (subspaceGroup S).relIndex V = Nat.card (Additive V ⧸ S) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := S))
    exact hcard.trans hq
  unfold subgroupCorank
  rw [hindex, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, Nat.log_pow (by decide)]

/-- If two binary subspaces span V and have trivial intersection, the quotient
by one has the dimension of the other. -/
theorem corank_subspaceGroup_of_isCompl (S R : Submodule (ZMod 2) (Additive V))
    (hc : IsCompl S R) : subgroupCorank V (subspaceGroup R) = Module.finrank (ZMod 2) S := by
  rw [corank_subspaceGroup]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S R
  rw [hc.sup_eq_top, hc.inf_eq_bot, finrank_top, finrank_bot,
    Nat.add_zero] at hsum
  have hquot := Submodule.finrank_quotient_add_finrank R
  omega

omit [Finite G] in
/-- Agreement with a factor on one summand determines an automizer element
which fixes the complementary summand. This is the precise use of the binary
overgroup theorem; it does not assume oddness of the whole preimage. -/
theorem inducedAutomizer_le_of_summand_action
    (S R : Submodule (ZMod 2) (Additive V)) (hspan : S ⊔ R = ⊤)
    (B : Subgroup (Automizer V)) (hBR : ∀ b ∈ B, ∀ v ∈ R, automizerRepresentation V b v = v)
    (A : Subgroup G) (hAN : A ≤ normalizer (V : Set G))
    (hAR : A ≤ centralizer (subspaceGroup R : Set G))
    (hact : ∀ a ∈ inducedAutomizer V A, ∃ b ∈ B,
      ∀ v ∈ S, automizerRepresentation V a v = automizerRepresentation V b v) :
    inducedAutomizer V A ≤ B := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := hact a ha
  have he : a = b := by
    apply automizerRepresentation_injective V
    apply LinearMap.ext
    intro w
    have hw : w ∈ S ⊔ R := by rw [hspan]; trivial
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
    have hvF : v ∈ fixedSpace (automizerRepresentation V) (inducedAutomizer V A) :=
      (mem_fixedSpace_inducedAutomizer V A hAN v).mpr
        ((le_centralizer_iff.mpr hAR) ((mem_subspaceGroup R v).mpr hv))
    have hav : automizerRepresentation V a v = v := hvF ⟨a, ha⟩
    rw [map_add, map_add, hab u hu, hav, hBR b hb v hv]
  exact he ▸ hb

variable {K : GroupClass} {T : Sylow 2 G} {M U X : Subgroup G}

/-- A nonidentity summand inside U with odd induced local centralizer is
an obstruction, and Q is an actual Sylow subgroup of its full centralizer. -/
theorem summand_obstruction_and_sylow (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (S : Submodule (ZMod 2) (Additive V)) (hSU : subspaceGroup S ≤ U)
    (hne : subspaceGroup S ≠ ⊥)
    (hodd : Odd (Nat.card (inducedAutomizer V
      (M ⊓ centralizer (subspaceGroup S : Set G))))) :
    subspaceGroup S ∈ obstructionFamily M V ∧
      ∃ Q : Sylow 2 (centralizer (subspaceGroup S : Set G)),
        (Q : Subgroup (centralizer (subspaceGroup S : Set G))).map
          (centralizer (subspaceGroup S : Set G)).subtype = sylowCentralizer (T : Subgroup G) V := by
  have hS : subspaceGroup S ∈ obstructionFamily M V :=
    ⟨subspaceGroup_le S, hne, fun hc => hU.2.2.1 ((Subgroup.centralizer_le hSU).trans hc),
      oddCentralizerCondition_of_odd_image
        (h.localCentralizer_le_normalizer hne (subspaceGroup_le S)) hodd⟩
  exact ⟨hS, h.sylow_obstruction hS⟩
end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
