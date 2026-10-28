module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary
public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.GroupTheory.CoveringKernelBound
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient

/-!
# Triviality of the even symplectic four-space multiplier

The two-primary positive-root section and the independent odd-primary
transfer calculations exclude every prime from the order of the canonical
universal kernel. Thus the identity cover of the literal Sp₄(F) matrix group
is universal for every finite characteristic-two field with more than three
elements, including F₄. The kernel is identified multiplicatively with PUnit.

The final application turns an actual perfect central cover into an
isomorphism, and turns a central-quotient model of a component into its whole
matrix model. The equivalence retains the given quotient map. These are the
multiplier inputs to Aschbacher–Smith 13.6.6, printed p.927.

Source: Aschbacher–Smith I.1.3, printed p.407, citing GLS98 §6.1.
No table omission, group-order calculation or simplicity assertion is used
as a substitute for the two central-extension calculations.
-/

public section
noncomputable section

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.Even

open Theory.GroupTheory PerfectCentralCovering

universe u v w
variable {F : Type u} [Field F] [Finite F] [CharP F 2]

/-- The matrix group is quasisimple throughout the multiplier range. -/
theorem isQuasisimple (hF : 3 < Nat.card F) : IsQuasisimple (Sp F) where
  toIsPerfect := CentralRootLifts.perfect (by omega)
  simple := SimpleQuotients.isSimpleGroup hF

/-- The exact canonical universal kernel is trivial, including at field order four. -/
theorem universalProjection_ker_eq_bot (hF : 3 < Nat.card F) :
    (universalProjection (Sp F)).ker = ⊥ := by
  apply Subgroup.card_eq_one.mp
  by_contra h
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd h
  by_cases hp2 : p = 2
  · exact TwoPrimary.not_two_dvd_universal_kernel hF (hp2 ▸ hdiv)
  · exact OddPrimary.not_dvd_card_universal_kernel hF p hp hp2 hdiv

/-- The Schur multiplier as a group, rather than only its order. -/
def universalKernelEquivPUnit (hF : 3 < Nat.card F) :
    (universalProjection (Sp F)).ker ≃* PUnit := by
  let : Subsingleton (universalProjection (Sp F)).ker := by
    rw [universalProjection_ker_eq_bot hF]
    infer_instance
  let : Unique (universalProjection (Sp F)).ker := uniqueOfSubsingleton 1
  exact MulEquiv.ofUnique

/-- The literal identity covering is universal in every target universe. -/
theorem identity_isUniversal (hF : 3 < Nat.card F) :
    letI : IsQuasisimple (Sp F) := isQuasisimple hF
    Covering.IsUniversal.{u, u, w} (Covering.id : Covering (Sp F) (Sp F)) := by
  let : IsQuasisimple (Sp F) := isQuasisimple hF
  apply Covering.isUniversal_of_kernel_card_le
  rw [Subgroup.card_eq_one.mpr (universalProjection_ker_eq_bot hF)]
  exact Nat.card_pos

/-- Every actual perfect central cover is injective; its domain may be infinite. -/
theorem cover_injective (hF : 3 < Nat.card F)
    {E : Type v} [Group E] (f : Cover E (Sp F)) :
    Function.Injective f.toMonoidHom :=
  f.injective_of_universalProjection_ker_eq_bot (universalProjection_ker_eq_bot hF)

/-- The whole covering group, using the specified projection as the equivalence. -/
def coverEquiv (hF : 3 < Nat.card F)
    {E : Type v} [Group E] (f : Cover E (Sp F)) : E ≃* Sp F :=
  MulEquiv.ofBijective f.toMonoidHom ⟨cover_injective hF f, f.surjective⟩

@[simp] theorem coverEquiv_apply (hF : 3 < Nat.card F)
    {E : Type v} [Group E] (f : Cover E (Sp F)) (x : E) :
    coverEquiv hF f x = f.toMonoidHom x := by
  unfold coverEquiv
  rfl

omit [CharP F 2] in
/-- The consumer convention |F| = 2^n, n > 1 supplies characteristic two itself. -/
theorem universalProjection_ker_eq_bot_of_card_pow
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    (universalProjection (Sp F)).ker = ⊥ := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  apply universalProjection_ker_eq_bot
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
  omega

omit [CharP F 2] in
/-- Application to a component's literal central quotient: the given model
lifts to the whole component and preserves its quotient triangle. -/
theorem exists_whole_model
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {K : Type v} [Group K] [Group.IsPerfect K]
    (e : K ⧸ Subgroup.center K ≃* Sp F) :
    ∃ eWhole : K ≃* Sp F, ∀ k : K,
      eWhole k = e (QuotientGroup.mk' (Subgroup.center K) k) := by
  exact ⟨centralQuotientEquivOfUniversalKernelEqBot
    (universalProjection_ker_eq_bot_of_card_pow hF hn) e, fun k =>
      centralQuotientEquivOfUniversalKernelEqBot_apply
        (universalProjection_ker_eq_bot_of_card_pow hF hn) e k⟩

end Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
