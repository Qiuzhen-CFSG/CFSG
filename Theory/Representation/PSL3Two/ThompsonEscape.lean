module

public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag.Model
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Calculations
public import Theory.SpecificGroups.PSL3Two.SourceFlag
public import Theory.Representation.PSL3Two.SmallModules
public import Theory.Representation.PSL3Two.FourGroupGeometry.FixedSpaces.Certificates
public import Theory.Representation.BinaryOffender.Basic
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.GroupAction.CommonFixedNormalizer

/-!
# Equal-weight involutions escaping the point radical in SL₃(2)

Every nontrivial subgroup B of the marked point four-group has cardinal
weight eight on the natural three-space. Any nonidentity element gives an
order-two subgroup C≤B with the same weight. An actual SL₃(2) conjugator
carries C to the upper root with center e₁, which lies in the marked Borel
and escapes the point radical. The original B is retained throughout.

The fixed subgroup is the literal common fixed subgroup of NaturalFlag.slAut.
The representation statement also supplies `EqualWeightLE`, the exact
rank-plus-fixed-dimension relation used by B.2.8 replacement. Neither B nor
its chosen conjugate is assumed to be Sylow; their containment in the same
specified Sylow is the conclusion needed for the source argument.

Source: Aschbacher–Smith, B.2.8 and the corrected 14.3.9(2) argument,
combined manuscript of 1 March 2004, printed pp.76 and 992–993.
-/

@[expose] public section
noncomputable section
open Subgroup Matrix Representation Representation.BinaryOffender
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
namespace BinaryLinearThree.ThompsonEscape

/-- The actual common fixed subgroup of the multiplicative natural module. -/
def Fix (B : Subgroup SL) : Subgroup Model := slAut.toMonoidHom.commonFixed B

theorem mem_Fix (B : Subgroup SL) (v : Model) :
    v ∈ Fix B ↔ ∀ b ∈ B, b.val.mulVec v.toAdd = v.toAdd := by
  rw [Fix, MonoidHom.mem_commonFixed]
  simp only [MulEquiv.coe_toMonoidHom, ← Multiplicative.toAdd.injective.eq_iff, slAut_apply]

/-- Type-tag transport retains each original vector and the original matrix action. -/
def fixedEquiv (B : Subgroup SL) : Fix B ≃ fixedSpace W B where
  toFun v := ⟨v.val.toAdd, by
    intro b
    exact (mem_Fix B v).mp v.property b b.property⟩
  invFun v := ⟨Multiplicative.ofAdd v.val, (mem_Fix B _).mpr (fun b hb => v.property ⟨b,hb⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_Fix_eq (B : Subgroup SL) : Nat.card (Fix B) = Nat.card (fixedSpace W B) :=
  Nat.card_congr (fixedEquiv B)

private def rootElement (i : Fin 4) : SL := Bruhat.upper ⟨i, by omega⟩

private theorem rootElement_injective : Function.Injective rootElement := by decide +kernel

private theorem point_elements (b : SL) (hb : b ∈ pointV) : ∃ i : Fin 4, rootElement i = b := by
  let f : Fin 4 → pointV := fun i => ⟨rootElement i, SourceFlag.upper_first i⟩
  have hi : Function.Injective f := fun i j h => rootElement_injective (congrArg Subtype.val h)
  have hc : Nat.card (Fin 4) = Nat.card pointV := by rw [card_pointV]; simp
  obtain ⟨i, he⟩ := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi,hc⟩).2 ⟨b,hb⟩
  exact ⟨i, congrArg Subtype.val he⟩

private theorem single_fixed_card : ∀ i : Fin 4, rootElement i ≠ 1 →
    Fintype.card {v : Vector // (rootElement i).val.mulVec v = v} = 4 := by decide +kernel

private theorem all_fixed_card :
    Fintype.card {v : Vector // ∀ i : Fin 4, (rootElement i).val.mulVec v = v} = 2 := by decide +kernel

/-- The complete point radical fixes just its center line. -/
theorem card_Fix_pointV : Nat.card (Fix pointV) = 2 := by
  let e : Fix pointV ≃ {v : Vector // ∀ i : Fin 4, (rootElement i).val.mulVec v = v} := {
    toFun v := ⟨v.val.toAdd, fun i => (mem_Fix pointV v).mp v.property _ (SourceFlag.upper_first i)⟩
    invFun v := ⟨Multiplicative.ofAdd v.val, (mem_Fix pointV _).mpr (by
      intro b hb
      obtain ⟨i, rfl⟩ := point_elements b hb
      exact v.property i)⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr e).trans (Nat.card_eq_fintype_card.trans all_fixed_card)

/-- Every nonidentity point translation fixes a plane on the natural module. -/
theorem card_Fix_cyclic (b : SL) (hb : b ∈ pointV) (hne : b ≠ 1) :
    Nat.card (Fix (zpowers b)) = 4 := by
  obtain ⟨i, rfl⟩ := point_elements b hb
  rw [card_Fix_eq]
  let e : fixedSpace W (zpowers (rootElement i)) ≃
      {v : Vector // (rootElement i).val.mulVec v = v} :=
    Equiv.subtypeEquivRight (mem_fixedSpace_zpowers_iff W (rootElement i))
  exact (Nat.card_congr e).trans (Nat.card_eq_fintype_card.trans (single_fixed_card i hne))

private def escapeRoot : SL := ⟨!![1,0,0;0,1,1;0,0,1], by decide⟩
private def swap : SL := ⟨!![0,1,0;1,0,0;0,0,1], by decide⟩

private theorem escapeRoot_mem : escapeRoot ∈ borelSL := by decide +kernel
private theorem escapeRoot_not_mem : escapeRoot ∉ pointV := by decide +kernel
private theorem swap_conjugates :
    swap * FourGroupGeometry.FixedSpaces.involution * swap⁻¹ = escapeRoot := by decide +kernel

/-- An actual inner conjugator puts the chosen involution in this Borel while
moving it outside the point four-group; it does not merely change the model. -/
theorem cyclic_escape (b : SL) (hb : b ∈ pointV) (hne : b ≠ 1) :
    ∃ g : SL, (zpowers b).map (MulAut.conj g).toMonoidHom ≤ borelSL ∧
      ¬ (zpowers b).map (MulAut.conj g).toMonoidHom ≤ pointV := by
  have hs : b * b = 1 := by simpa only [pow_two] using pointV_square b hb
  obtain ⟨k, hk⟩ := FourGroupGeometry.FixedSpaces.exists_involution_conjugator b hne hs
  have he : k⁻¹ * b * k = FourGroupGeometry.FixedSpaces.involution := by
    calc
      _ = k⁻¹ * (b * k) := by group
      _ = k⁻¹ * (k * FourGroupGeometry.FixedSpaces.involution) := by rw [hk]
      _ = _ := by group
  let g := swap * k⁻¹
  have hg : (MulAut.conj g) b = escapeRoot := by
    change (swap * k⁻¹) * b * (swap * k⁻¹)⁻¹ = _
    calc
      _ = swap * (k⁻¹ * b * k) * swap⁻¹ := by group
      _ = escapeRoot := by rw [he, swap_conjugates]
  refine ⟨g, ?_, ?_⟩
  · rw [MonoidHom.map_zpowers]
    change zpowers ((MulAut.conj g) b) ≤ borelSL
    rw [hg]
    exact zpowers_le.mpr escapeRoot_mem
  · intro h
    exact escapeRoot_not_mem (hg ▸ h (mem_map_of_mem _ (mem_zpowers b)))

/-- Every nontrivial subgroup of the point four-group has cardinal weight
exactly eight. The proof distinguishes its actual orders two and four. -/
theorem cardinal_weight (B : Subgroup SL) (hB : B ≤ pointV) (hne : B ≠ ⊥) :
    Nat.card B * Nat.card (Fix B) = 8 := by
  obtain ⟨b, hb, hb1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hne)
  have hc : Nat.card (zpowers b) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (pointV_square b (hB hb)) hb1
  have hCB : zpowers b ≤ B := zpowers_le.mpr hb
  have hd := card_dvd_of_le hB
  rw [card_pointV] at hd
  have hcard : Nat.card B = 2 ∨ Nat.card B = 4 := by
    have hdiv := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
      (show Nat.card B ∣ 2 ^ 2 by norm_num at hd ⊢; exact hd)
    obtain ⟨n, hn, he⟩ := hdiv
    have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hn' with rfl | rfl | rfl
    · norm_num at he
      exact (hne he).elim
    · exact Or.inl he
    · exact Or.inr he
  rcases hcard with htwo | hfour
  · have he : zpowers b = B := eq_of_le_of_card_ge hCB (by rw [hc, htwo])
    rw [← he, hc, card_Fix_cyclic b (hB hb) hb1]
  · have he : B = pointV := eq_of_le_of_card_ge hB (by rw [hfour, card_pointV])
    rw [he, card_pointV, card_Fix_pointV]

/-- The precise replacement data: preserve B, choose C≤B with equal weight,
and escape the point radical while staying in the marked Sylow subgroup. -/
theorem exists_equal_weight_escape (B : Subgroup SL) (hB : B ≤ pointV) (hne : B ≠ ⊥) :
    ∃ C : Subgroup SL, C ≤ B ∧ Nat.card C = 2 ∧
      Nat.card C * Nat.card (Fix C) = Nat.card B * Nat.card (Fix B) ∧
      ∃ g : SL, C.map (MulAut.conj g).toMonoidHom ≤ borelSL ∧
        ¬ C.map (MulAut.conj g).toMonoidHom ≤ pointV := by
  obtain ⟨b, hb, hb1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hne)
  have hCB : zpowers b ≤ B := zpowers_le.mpr hb
  have hc : Nat.card (zpowers b) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (pointV_square b (hB hb)) hb1
  refine ⟨zpowers b, hCB, hc, ?_, cyclic_escape b (hB hb) hb1⟩
  rw [hc, card_Fix_cyclic b (hB hb) hb1, cardinal_weight B hB hne]


/-- Elementary structure is a consequence of containment in the actual radical. -/
theorem elementary_of_le_pointV (B : Subgroup SL) (hB : B ≤ pointV) :
    IsElementaryAbelian 2 B where
  is_comm.comm x y := by
    have hi (x : B) : x⁻¹ = x := by
      apply inv_eq_of_mul_eq_one_right
      apply Subtype.ext
      change (x : SL) * (x : SL) = 1
      simpa only [pow_two] using pointV_square x (hB x.property)
    calc
      x * y = (x * y)⁻¹ := (hi _).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
      _ = y * x := by rw [hi y, hi x]
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro b
    exact Subtype.ext (pointV_square b (hB b.property)))

/-- Cardinal weight eight is exactly the source's rank-plus-fixed-rank weight three. -/
theorem weight_eq_three (B : Subgroup SL) (hB : B ≤ pointV) (hne : B ≠ ⊥) :
    weight W B = 3 := by
  have htwo : IsElementaryTwo B := ⟨hne, elementary_of_le_pointV B hB⟩
  have h := cardinal_weight B hB hne
  rw [card_Fix_eq, htwo.card_eq_two_pow_rank,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, ← pow_add] at h
  exact Nat.pow_right_injective (by decide : 1 < 2) (h.trans (by decide : 8 = 2 ^ 3))

/-- B.2.8-ready replacement and escape, retaining the original B and its
actual natural representation. The Borel is the specified Sylow subgroup. -/
theorem exists_replacement_escape (B : Subgroup SL) (hB : B ≤ pointV) (hne : B ≠ ⊥) :
    ∃ C : Subgroup SL, Nat.card C = 2 ∧ IsElementaryTwo C ∧ EqualWeightLE W C B ∧
      Nat.card C * Nat.card (Fix C) = Nat.card B * Nat.card (Fix B) ∧
      ∃ g : SL, C.map (MulAut.conj g).toMonoidHom ≤ borelSL ∧
        ¬ C.map (MulAut.conj g).toMonoidHom ≤ pointV := by
  obtain ⟨C, hCB, hc, hw, hg⟩ := exists_equal_weight_escape B hB hne
  have hC : C ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hc
    contradiction
  refine ⟨C, hc, ⟨hC, elementary_of_le_pointV C (hCB.trans hB)⟩,
    ⟨hCB, ?_⟩, hw, hg⟩
  rw [weight_eq_three C (hCB.trans hB) hC, weight_eq_three B hB hne]

end BinaryLinearThree.ThompsonEscape
