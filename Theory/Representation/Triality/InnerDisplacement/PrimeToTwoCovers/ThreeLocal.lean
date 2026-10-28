module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Normalizer
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Order
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Split
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.Reduction
public import Theory.GroupTheory.Covering

/-!
# The triality three-primary exclusion

The split and nonsplit constructions supply actual tori of orders
(q³ − 1)(q − 1) and (q³ + 1)(q + 1), respectively, with the required Weyl
actions. Every binary parameter lies in one of their congruence classes.
The index calculation and normalizer argument construct an ambient Sylow
three-subgroup, and central transfer excludes three from the kernel of
every finite perfect central cover. No bound on the three-adic valuation
of q − 1 or q + 1 is imposed.

The final application uses precisely the marked quotient R/Z(R). The
conditional interfaces are retained; `geometry`, `not_three_dvd_kernel`
and `not_three_dvd_center` discharge their concrete configuration premises.

Source: GLS3 §6.1, Theorem 6.1.4 and Tables 6.1.2–3. There is no triality
odd-multiplier exception at q = 2, which belongs to the nonsplit branch.
-/

public section

namespace Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal

open Standard ConcreteBruhat Parabolics
open PerfectCentralCovering PerfectCentralCovering.OddSylow

/-- The concrete split configuration supplies the prime-three transfer input. -/
theorem split_geometry_of_configuration (n : ℕ) (hn : 0 < n)
    (hd : 3 ∣ 2 ^ n - 1) (d : Configuration (torus (binaryParameters n hn))) :
    Geometry 3 (BinaryCarrier n hn) :=
  d.geometry (nine_not_dvd_split_torus_index n hn hd)

/-- The concrete nonsplit configuration supplies the same input, including q = 2. -/
theorem nonsplit_geometry_of_configuration (n : ℕ) (hn : 0 < n)
    (hd : 3 ∣ 2 ^ n + 1) (A : Subgroup (BinaryCarrier n hn))
    (hA : Nat.card A = ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1)) (d : Configuration A) :
    Geometry 3 (BinaryCarrier n hn) :=
  d.geometry (nine_not_dvd_nonsplit_torus_index n hn A hA hd)

/-- The two independent concrete torus constructions exhaust all positive exponents. -/
theorem geometry_of_configurations (n : ℕ) (hn : 0 < n)
    (hsplit : 3 ∣ 2 ^ n - 1 → Nonempty (Configuration (torus (binaryParameters n hn))))
    (hnonsplit : 3 ∣ 2 ^ n + 1 → ∃ A : Subgroup (BinaryCarrier n hn),
      Nat.card A = ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1) ∧ Nonempty (Configuration A)) :
    Geometry 3 (BinaryCarrier n hn) := by
  rcases three_dvd_sub_one_or_add_one n with hd | hd
  · obtain ⟨d⟩ := hsplit hd
    exact split_geometry_of_configuration n hn hd d
  · obtain ⟨A, hA, ⟨d⟩⟩ := hnonsplit hd
    exact nonsplit_geometry_of_configuration n hn hd A hA d

/-- Uniform application to arbitrary finite perfect covers. Neither local
construction takes a cover, a multiplier bound, or a kernel conclusion as input. -/
theorem not_three_dvd_kernel_of_configurations (n : ℕ) (hn : 0 < n)
    (hsplit : 3 ∣ 2 ^ n - 1 → Nonempty (Configuration (torus (binaryParameters n hn))))
    (hnonsplit : 3 ∣ 2 ^ n + 1 → ∃ A : Subgroup (BinaryCarrier n hn),
      Nat.card A = ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1) ∧ Nonempty (Configuration A))
    {E : Type*} [Group E] [Finite E] (f : Cover E (BinaryCarrier n hn)) :
    ¬ 3 ∣ Nat.card f.toMonoidHom.ker :=
  (geometry_of_configurations n hn hsplit hnonsplit).not_dvd_card_kernel (by decide) f

/-- Specialization through the literal central-quotient model witness, expressed
in terms of the two concrete configurations. -/
theorem not_three_dvd_center_of_configurations {R : Type*} [Group R] [Finite R]
    [Theory.GroupTheory.IsQuasisimple R] (n : ℕ) (hn : 0 < n)
    (hmodel : IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R))
    (hsplit : 3 ∣ 2 ^ n - 1 → Nonempty (Configuration (torus (binaryParameters n hn))))
    (hnonsplit : 3 ∣ 2 ^ n + 1 → ∃ A : Subgroup (BinaryCarrier n hn),
      Nat.card A = ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1) ∧ Nonempty (Configuration A)) :
    ¬ 3 ∣ Nat.card (Subgroup.center R) := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff _ n hn).mp hmodel
  rw [← centralQuotientCover_ker e]
  exact not_three_dvd_kernel_of_configurations n hn hsplit hnonsplit (centralQuotientCover e)

/-- The concrete split and nonsplit configurations supply the three-primary
transfer geometry for every positive binary exponent, including n = 1. -/
theorem geometry (n : ℕ) (hn : 0 < n) : Geometry 3 (BinaryCarrier n hn) :=
  geometry_of_configurations n hn (fun _ => Split.nonempty_configuration n hn)
    (fun _ => Nonsplit.exists_configuration n hn)

/-- Three never divides the kernel of a finite perfect central cover of the
genuine binary triality group. The covering group may lie in any universe. -/
theorem not_three_dvd_kernel (n : ℕ) (hn : 0 < n)
    {E : Type*} [Group E] [Finite E] (f : Cover E (BinaryCarrier n hn)) :
    ¬ 3 ∣ Nat.card f.toMonoidHom.ker :=
  (geometry n hn).not_dvd_card_kernel (by decide) f

/-- The three-primary center exclusion for a finite quasisimple group whose
literal quotient R/Z(R) is the specified triality model. There are no additional
local-geometry or covering premises, including at q = 2. -/
theorem not_three_dvd_center {R : Type*} [Group R] [Finite R]
    [Theory.GroupTheory.IsQuasisimple R] (n : ℕ) (hn : 0 < n)
    (hmodel : IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R)) :
    ¬ 3 ∣ Nat.card (Subgroup.center R) := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff _ n hn).mp hmodel
  rw [← centralQuotientCover_ker e]
  exact not_three_dvd_kernel n hn (centralQuotientCover e)

end Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal
