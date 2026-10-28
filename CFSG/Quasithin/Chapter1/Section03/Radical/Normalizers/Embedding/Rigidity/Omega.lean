module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Recognizing the omega layer in the odd component core

An exponent-p subgroup of the A.3.6 odd core has order at least p². In
an elementary or homocyclic core, this fills the first omega subgroup by
its order. In an extraspecial core of order p³, a proper elementary plane
has a nontrivial proper intersection with the center. Thus the central
intersection dichotomy supplied by Xi irreducibility excludes that plane.

The homocyclic case retains Ω₁ even when the core has higher exponent.
Source: Aschbacher–Smith, A.3.6, printed pp.43–45, and the structural step
in the proof of 1.3.8, printed p.513.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Rigidity
open Section02 LocalModels
variable {V Q : Type*} [Group V] [Finite V] [Group Q] [Finite Q]
variable {p : ℕ} [Fact p.Prime]

omit [Finite V] in
private theorem plane_center_nondichotomy (hV : IsElementaryAbelian p V)
    (hcV : Nat.card V = p ^ 2) (hQ : OddExtraspecialThree p Q)
    (f : V →* Q) (hf : Function.Injective f) :
    (center Q).comap f ≠ ⊥ ∧ (center Q).comap f ≠ ⊤ := by
  let := hV
  let := hQ.1.1
  have hcard : Nat.card f.range = p ^ 2 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hcV
  have hnonab : ¬ IsMulCommutative Q := by
    intro h
    let := h
    exact (QuotientGroup.nontrivial_iff.mp (IsExtraspecial.quotient_nontrivial p Q))
      (center_eq_top (G := Q))
  constructor
  · intro he
    have hd : Disjoint f.range (center Q) := by
      apply disjoint_def.mpr
      rintro x ⟨v, rfl⟩ hx
      have hv : v ∈ (center Q).comap f := hx
      rw [he] at hv
      simp only [mem_bot.mp hv, map_one]
    have hc : Nat.card (f.range ⊔ center Q : Subgroup Q) = Nat.card Q := by
      rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
        ((center_le_centralizer f.range).trans (centralizer_le_normalizer _)) hd,
        hcard, IsExtraspecial.center_order_p (p := p), hQ.1.2]
      ring
    have htop : f.range ⊔ center Q = ⊤ := eq_top_of_card_eq _ hc
    have hcomm : IsMulCommutative f.range :=
      IsMulCommutative.of_comm (fun a b => by
        obtain ⟨x, rfl⟩ := f.rangeRestrict_surjective a
        obtain ⟨y, rfl⟩ := f.rangeRestrict_surjective b
        simp only [← map_mul, mul_comm])
    let := hcomm
    have hs : IsMulCommutative (f.range ⊔ center Q : Subgroup Q) := by
      apply le_centralizer_iff_isMulCommutative.mp
      apply sup_le
      · exact le_centralizer_iff.mpr (sup_le f.range.le_centralizer
          (center_le_centralizer _))
      · exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp
          (center_le_centralizer _)) (center Q).le_centralizer)
    have ht : IsMulCommutative (⊤ : Subgroup Q) := htop ▸ hs
    let := ht
    exact hnonab (IsMulCommutative.of_comm (fun a b =>
      congrArg Subtype.val (mul_comm (⟨a, trivial⟩ : (⊤ : Subgroup Q)) ⟨b, trivial⟩)))
  · intro he
    have hle : f.range ≤ center Q := by
      rintro x ⟨v, rfl⟩
      exact (show v ∈ (center Q).comap f by rw [he]; trivial)
    have hh := card_le_of_le hle
    rw [hcard, IsExtraspecial.center_order_p (p := p)] at hh
    have hp := (Fact.out : p.Prime).one_lt
    nlinarith

omit [Finite Q] [Fact p.Prime] in
private theorem omega_card_of_commutative (h : XiOddQuotient p Q)
    (hc : IsMulCommutative Q) : Nat.card Q = p ^ 2 := by
  rcases h with h | h
  · exact h.2
  · let := hc
    exact ((QuotientGroup.nontrivial_iff.mp h.1.quotient_nontrivial)
      (center_eq_top (G := Q))).elim

omit [Finite V] in
theorem range_eq_omega_of_center_dichotomy (hV : XiOddQuotient p V)
    (hQ : (IsElementaryAbelian p Q ∧ Nat.card Q = p ^ 2) ∨
      OddExtraspecialThree p Q ∨ HomocyclicTwo p Q)
    (f : V →* Q) (hf : Function.Injective f)
    (hcenter : IsElementaryAbelian p V →
      (center Q).comap f = ⊥ ∨ (center Q).comap f = ⊤) :
    f.range = omega Q (p := p) 1 := by
  have hpow : ∀ v : V, v ^ p = 1 := by
    rcases hV with h | h
    · let := h.1
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p V)
    · intro v
      simpa only [h.2.2] using Monoid.pow_exponent_eq_one v
  have hle : f.range ≤ omega Q (p := p) 1 := by
    rintro x ⟨v, rfl⟩
    apply Subgroup.subset_closure
    change (f v) ^ (p ^ 1) = 1
    rw [pow_one, ← map_pow, hpow v, map_one]
  have hcard : Nat.card f.range = Nat.card V :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hge : p ^ 2 ≤ Nat.card V := by
    rcases hV with h | h
    · exact h.2.ge
    · rw [h.2.1]
      exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by decide)
  rcases hQ with he | he | he
  · have hc : Nat.card (omega Q (p := p) 1) ≤ p ^ 2 :=
      (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans he.2.le
    exact eq_of_le_of_card_ge hle (hc.trans (hcard.symm ▸ hge))
  · rcases hV with h | h
    · exact ((hcenter h.1).elim (plane_center_nondichotomy h.1 h.2 he f hf).1
        (plane_center_nondichotomy h.1 h.2 he f hf).2).elim
    · have hc : Nat.card (omega Q (p := p) 1) ≤ Nat.card f.range := by
        rw [hcard, h.2.1]
        simpa only [he.1.2] using (Nat.card_le_card_of_injective (omega Q (p := p) 1).subtype
          (omega Q (p := p) 1).subtype_injective)
      exact eq_of_le_of_card_ge hle hc
  · obtain ⟨a, ha, ⟨e⟩⟩ := he
    have hcomm : IsMulCommutative Q := IsMulCommutative.of_comm (fun x y =>
      e.injective (by simp only [map_mul, mul_comm]))
    let := hcomm
    have hc : Nat.card (omega Q (p := p) 1) = p ^ 2 :=
      omega_card_of_commutative (RadicalStructure.homocyclic_omega ⟨a, ha, ⟨e⟩⟩)
        inferInstance
    exact eq_of_le_of_card_ge hle (by rw [hc, hcard]; exact hge)

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Rigidity
