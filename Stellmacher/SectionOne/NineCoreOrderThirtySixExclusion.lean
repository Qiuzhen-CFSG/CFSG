module

public import Stellmacher.SectionOne.NineCoreElementary
public import Stellmacher.SectionOne.NineCoreOrderInvariant
public import Stellmacher.UniqueMaximalContainingMap
public import Theory.GroupTheory.ElementaryOddSylowUniqueMaximal

/-!
# Excluding order thirty-six for the unique-maximal nine-core group

If the group had order thirty-six, its Sylow two-subgroup would have
order four. The given elementary four is then a Sylow subgroup, and
Sylow conjugacy transfers its elementary structure to the specified Sylow.
Its faithful conjugation action makes the order-nine odd core elementary.

Maschke's invariant-complement argument turns unique maximal containment
into maximality of the Sylow itself. Product counting then makes every
Sylow-invariant subgroup of the odd core trivial or the whole core.
The elementary-four irreducible-complement exclusion contradicts this:
the fixed subgroup of each nonidentity actor is invariant, so faithfulness
would force all three nonidentity involutions to induce inversion.

Thus the splitting and proper-overgroup obstruction is supplied by
general coprime-action results, without an offender or a wreath model.
This is the order-thirty-six exclusion toward Stellmacher (9.1)(8),
printed p.47 / PDF p.37 of `refs/files/stellmacher-n-group.pdf`.
No assumption on the cardinality of the module is required.
-/

namespace Stellmacher.SectionOne

universe u

public theorem nineCore_card_ne_thirty_six
    {K V : Type u} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (R : Sylow 2 K)
    (hgen : oddCore K ⊔ (R : Subgroup K) = ⊤)
    (hunique : Stellmacher.IsUniqueMaximalContaining (R : Subgroup K) ⊤)
    (hoddcard : Nat.card (oddCore K) = 9)
    (X : Subgroup K) (hX : IsElementaryAbelian 2 X)
    (hXcard : Nat.card X = 4) : Nat.card K ≠ 36 := by
  classical
  intro hKcard
  have hRcard : Nat.card R = 4 := by
    rw [Sylow.card_eq_multiplicity R, hKcard]
    decide +kernel
  let _ : IsElementaryAbelian 2 X := hX
  obtain ⟨Q, hXQ⟩ := (IsElementaryAbelian.isPGroup 2 X).exists_le_sylow
  have hQcard : Nat.card Q = 4 := (Nat.card_congr (Q.equiv R).toEquiv).trans hRcard
  have hXQeq : X = (Q : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hXQ (by rw [hXcard, hQcard])
  let _ : IsElementaryAbelian 2 Q := hXQeq ▸ hX
  let equiv : R ≃* Q := R.equiv Q
  have hRelementary : IsElementaryAbelian 2 R := by
    refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · rw [isMulCommutative_iff]
      intro first second
      apply equiv.injective
      simpa only [map_mul] using
        (isMulCommutative_iff.mp (inferInstance : IsMulCommutative Q)
          (equiv first) (equiv second))
    · rw [Monoid.exponent_eq_of_mulEquiv equiv]
      exact IsElementaryAbelian.exponent_dvd_p 2 Q
  let _ : (oddCore K).Normal := pPrimeCore_normal
  let _ : IsElementaryAbelian 3 (oddCore K) :=
    nineCore_elementary_of_elementary_four h hoddcard X hX hXcard
  obtain ⟨maximal, hmaximal, hRmaximal, huniq⟩ :=
    (uniqueMaximalContaining_top_iff (R : Subgroup K)).mp hunique
  have hcoatom : IsCoatom (R : Subgroup K) :=
    Theory.GroupTheory.sylow_isCoatom_of_elementary_odd_supplement_unique_maximal
      (oddCore K) R hgen
      ⟨maximal, ⟨hmaximal, hRmaximal⟩, fun subgroup hsubgroup =>
        huniq subgroup hsubgroup.1 hsubgroup.2⟩
  exact nineCore_not_elementary_four_coatom h R hRelementary hRcard hgen hoddcard hcoatom

end Stellmacher.SectionOne
