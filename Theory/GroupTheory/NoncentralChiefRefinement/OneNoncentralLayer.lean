module

public import Theory.GroupTheory.NoncentralChiefRefinement.CentralQuotient
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Chief counts with one noncentral layer

A central initial interval contributes zero. If the next normal interval is
chief and the terminal quotient has no binary chief factors, concatenation
and equivariant Jordan–Hölder give a bound of one for every complete series.
A simple group which is not a two-group supplies the terminal condition.

The native J₂ involution centralizer applies this to its marked involution,
its extraspecial radical, and its A₅ quotient (GLS3, Table 5.3g).
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {H K : Type*} [Group H] [Group K]

/-- A simple non-two-group has no binary chief section. -/
theorem noTwoChiefFactors_of_simple [IsSimpleGroup H] (hp : ¬ IsPGroup 2 H) :
    HasNoTwoChiefFactors H := by
  intro A B hAB hP
  have hA : A.val = ⊥ := A.property.eq_bot_or_eq_top.resolve_right (by
    intro h
    exact hAB.lt.not_ge (show B.val ≤ A.val from by rw [h]; exact le_top))
  have hB : B.val = ⊤ := B.property.eq_bot_or_eq_top.resolve_left (by
    intro h
    exact hAB.lt.not_ge (show B.val ≤ A.val from by rw [h]; exact bot_le))
  have e : Section A B ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq (by rw [hA, bot_subgroupOf])).trans
      (QuotientGroup.quotientBot.trans ((MulEquiv.subgroupCongr hB).trans topEquiv))
  exact hp (hP.of_equiv e)

/-- The literal section isomorphisms preserve the terminal condition. -/
theorem HasNoTwoChiefFactors.of_equiv (h : HasNoTwoChiefFactors H) (e : K ≃* H) :
    HasNoTwoChiefFactors K := by
  intro A B hAB hP
  exact h (actorNormalEquiv e A) (actorNormalEquiv e B)
    ((apply_covBy_apply_iff (actorNormalEquiv e)).mpr hAB)
    (hP.of_equiv (actorSectionEquiv e A B))

/-- Refine the two outer intervals and count the single middle chief interval. -/
theorem ChiefSeries.noncentralTwoCount_le_one_of_central_chief [Finite K]
    (Z Q : NormalNode K) (hc : IsCentral ⊥ Z) (hZQ : Z ⋖ Q)
    (ht : HasNoTwoChiefFactors (K ⧸ Q.val))
    (s : ChiefSeries K) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 := by
  obtain ⟨a, ha0, ha1⟩ := exists_chiefSeries (⊥ : NormalNode K) Z bot_le
  let b : ChiefSeries K := (RelSeries.singleton _ Z).snoc Q hZQ
  obtain ⟨c, hc0, hc1⟩ := exists_chiefSeries Q (⊤ : NormalNode K) le_top
  have hab : a.last = b.head := ha1
  have hbc : (a.smash b hab).last = c.head := by
    exact (RelSeries.last_smash hab).trans
      ((RelSeries.last_snoc (RelSeries.singleton _ Z) Q hZQ).trans hc0.symm)
  have ha : a.noncentralTwoCount = 0 := by
    apply a.noncentralTwoCount_eq_zero_of_central
    rwa [ha0, ha1]
  have hb : b.noncentralTwoCount ≤ 1 := by
    exact (Nat.card_le_card_of_injective (fun i : {i : Fin b.length //
      IsNoncentralTwo (b i.castSucc) (b i.succ)} => i.val) Subtype.val_injective).trans_eq
        (by rw [Nat.card_fin]; rfl)
  have hc' : c.noncentralTwoCount = 0 :=
    c.noncentralTwoCount_eq_zero_of_quotient Q hc0.ge ht
  rw [s.noncentralTwoCount_eq ((a.smash b hab).smash c hbc)
    (by simpa using h0.trans ha0.symm) (by simpa using h1.trans hc1.symm),
    ChiefSeries.noncentralTwoCount_smash, ChiefSeries.noncentralTwoCount_smash,
    ha, hc', zero_add, add_zero]
  exact hb

/-- If every binary chief section is excluded, the count vanishes. -/
theorem ChiefSeries.noncentralTwoCount_eq_zero_of_noTwo
    (h : HasNoTwoChiefFactors K) (s : ChiefSeries K) : s.noncentralTwoCount = 0 := by
  apply Nat.card_eq_zero.mpr
  exact Or.inl ⟨fun i => h _ _ (s.step i.val) i.property.1⟩

end NoncentralChiefRefinement
