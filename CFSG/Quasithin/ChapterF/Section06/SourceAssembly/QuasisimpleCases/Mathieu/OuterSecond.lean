module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.OuterSylow
/-!
# The actual second-vertex quotient in the outer Mathieu row

Modulo the literal C₄² radical, a rotation of order six commutes with the
outer involution. Their order-three and two-torsion factors give an injective
C₃ × E₄ homomorphism. Its range has index two in the quotient of order 24,
so it is normal and the remaining quotient is C₂.

Source: Aschbacher–Smith, F.6.18(13), printed p.310, and 14.2.21.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
open Sporadic.Mathieu Sporadic.Mathieu.M12ExceptionalExtension
open Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu.OuterSquare

abbrev C3 := Multiplicative (ZMod 3)
abbrev C2 := Multiplicative (ZMod 2)
abbrev Q := secondParabolic ⧸ localRadical
private def localRotation : secondParabolic := ⟨rotation, rotation_mem⟩
private def localSwap : secondParabolic := ⟨swap, swap_mem_overlap.2⟩
private def q : secondParabolic →* Q := QuotientGroup.mk' localRadical
private def rq : Q := q localRotation
private def tq : Q := q localSwap

private theorem localRotation_six : localRotation ^ 6 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  decide +kernel
private theorem localSwap_two : localSwap ^ 2 = 1 := by
  apply Subtype.ext
  exact (pow_two swap).trans swap_square
private theorem rq_six : rq ^ 6 = 1 := by
  rw [rq, ← map_pow, localRotation_six, map_one]
private theorem tq_two : tq ^ 2 = 1 := by
  rw [tq, ← map_pow, localSwap_two, map_one]
private theorem rotation_swap_commutator : ⁅rotation,swap⁆ = rootTwo ^ 2 := by
  apply Subtype.ext
  decide +kernel
private theorem rq_tq_commute : Commute rq tq := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [rq, tq, ← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff _).mpr
  change ⁅rotation,swap⁆ ∈ radical
  rw [rotation_swap_commutator]
  exact (mem_radical_iff _).mpr ⟨0,2,by simp⟩
private def cyclicThree : C3 →* Q :=
  FiveFour.cyclicHom (rq ^ 2) (by rw [← pow_mul]; exact rq_six)
private def cyclicTwo : C2 →* Q :=
  FiveFour.cyclicHom (rq ^ 3) (by rw [← pow_mul]; exact rq_six)
private def outerTwo : C2 →* Q := FiveFour.cyclicHom tq tq_two
private def fourMap : InnerSquare.E4 →* Q :=
  cyclicTwo.noncommCoprod outerTwo (fun a b => by
    change Commute ((rq ^ 3) ^ a.toAdd.val) (tq ^ b.toAdd.val)
    exact (rq_tq_commute.pow_left 3).pow_pow _ _)
private def abelianMap : C3 × InnerSquare.E4 →* Q :=
  cyclicThree.noncommCoprod fourMap (fun a b => by
    change Commute ((rq ^ 2) ^ a.toAdd.val)
      (((rq ^ 3) ^ b.1.toAdd.val) * tq ^ b.2.toAdd.val)
    apply Commute.mul_right
    · exact (Commute.refl rq).pow_pow _ _ |>.pow_pow _ _
    · exact (rq_tq_commute.pow_left 2).pow_pow _ _)
private def abelianValue (a : C3 × InnerSquare.E4) : secondParabolic :=
  localRotation ^ (2 * a.1.toAdd.val + 3 * a.2.1.toAdd.val) * localSwap ^ a.2.2.toAdd.val
private theorem abelianMap_apply (a : C3 × InnerSquare.E4) :
    abelianMap a = q (abelianValue a) := by
  change (rq ^ 2) ^ a.1.toAdd.val *
    ((rq ^ 3) ^ a.2.1.toAdd.val * tq ^ a.2.2.toAdd.val) = _
  simp only [abelianValue, map_mul, map_pow, rq, tq, pow_add, pow_mul, mul_assoc]
private theorem abelian_disjoint : ∀ a : C3 × InnerSquare.E4, ∀ i j : Fin 4,
    (abelianValue a : Carrier) = rootOne ^ i.val * rootTwo ^ j.val → a = 1 := by
  decide +kernel
private theorem abelianMap_injective : Function.Injective abelianMap := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro a ha
  have he : q (abelianValue a) = 1 := (abelianMap_apply a).symm.trans ha
  have hm : abelianValue a ∈ localRadical := (QuotientGroup.eq_one_iff _).mp he
  obtain ⟨i,j,hij⟩ := (mem_radical_iff (abelianValue a : Carrier)).mp hm
  exact abelian_disjoint a i j hij.symm
private theorem local_quotient_card : Nat.card Q = 24 := by
  have h := localRadical.card_mul_index
  rw [localRadical_card, card_secondParabolic innerModel] at h
  change localRadical.index = 24
  omega

/-- The actual normal twelve-subgroup of the second quotient. -/
def quotientTwelve : Subgroup Q := abelianMap.range

def quotientTwelveEquiv : quotientTwelve ≃* C3 × InnerSquare.E4 :=
  (MonoidHom.ofInjective abelianMap_injective).symm

theorem quotientTwelve_index : quotientTwelve.index = 2 := by
  have hc : Nat.card quotientTwelve = 12 := by
    rw [Nat.card_congr quotientTwelveEquiv.toEquiv]
    simp [InnerSquare.E4, Nat.card_eq_fintype_card]
  have h := quotientTwelve.card_mul_index
  rw [hc, local_quotient_card] at h
  omega
instance : quotientTwelve.Normal := normal_of_index_eq_two quotientTwelve_index

def secondOuterQuotientEquiv : (Q ⧸ quotientTwelve) ≃* C2 :=
  mulEquivOfPrimeCardEq (p := 2) quotientTwelve_index (by simp [Nat.card_eq_fintype_card])

/-- The second vertex has the literal C₄² denominator and the prescribed
normal C₃ × E₄ subgroup in its quotient, with outer quotient C₂. -/
theorem second_extension : ∃ N : Subgroup secondParabolic, ∃ _ : N.Normal,
    Nonempty (N ≃* InnerSquare.C4Square) ∧
    ∃ K : Subgroup (secondParabolic ⧸ N), ∃ _ : K.Normal,
      Nonempty (K ≃* C3 × InnerSquare.E4) ∧
        Nonempty (((secondParabolic ⧸ N) ⧸ K) ≃* C2) :=
  ⟨localRadical, inferInstance, ⟨localRadicalEquiv⟩,
    quotientTwelve, inferInstance, ⟨quotientTwelveEquiv⟩, ⟨secondOuterQuotientEquiv⟩⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu.OuterSquare
