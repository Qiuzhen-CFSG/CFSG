module

public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.MatrixFactorization
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.RootExtension
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.HighestUnipotent.OrthogonalModel

/-!
# Transporting the orthogonal calculation to the highest-root commutant

Nilpotence of `g - 1` in the faithful Geck matrices is equivalent to p-power
order. In odd characteristic, the two highest-root values at parameter one
determine centralization of the full highest-root SL₂: conjugate back to a
simple root and use quadratic interpolation, including over characteristic
three. A faithful comparison marking the four rank-one subgroups then applies
the proved orthogonal centralizer calculation and recovers the ordered arm
factorization in the original group.

The comparison is an explicit outstanding premise. This module does not claim
unconditional Geck centralizer exhaustion. Its final application feeds the
literal inverse-conjugated split centralizer used by `ElementaryIndex`.

Sources: GLS3 §§2.4, 2.6–2.7 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith A.2.17, printed p.39, (*) and the triality case.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent
open Parabolics
variable {P : Parameters} (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)

/-- Nilpotence detects exactly p-power order in the faithful Geck matrices. -/
theorem matrixHom_isNilpotent_sub_one_iff (g : SplitGroup P) :
    IsNilpotent (Geometry.matrixHom P g - 1) ↔ ∃ n : ℕ, g ^ (P.prime ^ n) = 1 := by
  constructor
  · rintro ⟨n, hn⟩
    let : CharP (Matrix Geometry.Integral.Ix Geometry.Integral.Ix (ExtensionField P)) P.prime :=
      charP_of_injective_algebraMap (algebraMap (ExtensionField P) _).injective P.prime
    have hh := pow_eq_zero_of_le
      (Nat.le_of_lt (Nat.lt_pow_self (n := n) P.prime_prime.one_lt)) hn
    rw [sub_pow_char_pow_of_commute P.prime n (Commute.one_right _), one_pow,
      sub_eq_zero] at hh
    exact ⟨n, Geometry.matrixHom_injective P (by simpa only [map_pow, map_one] using hh)⟩
  · rintro ⟨n, hn⟩
    exact matrixHom_isNilpotent_sub_one_of_pow g n hn

private theorem matrixHom_conjugatedRoot (b : Bool) (t : ExtensionField P) :
    Geometry.matrixHom P ((MulAut.conj (splitHighestWeyl D C))
      (if b then positiveRoot P 1 t else negativeRoot P 1 t)) =
      Geometry.highestCurve b t := by
  have hc : Geometry.matrixHom P (if b then positiveRoot P 1 t else negativeRoot P 1 t) =
      Geometry.curve 1 b t := by
    cases b
    · exact Geometry.matrixHom_negative P 1 t
    · exact Geometry.matrixHom_positive P 1 t
  change Geometry.matrixHom P (splitHighestWeyl D C * _ * (splitHighestWeyl D C)⁻¹) = _
  simp only [map_mul, hc, Geometry.matrixHom_highest]
  rw [Geometry.highest_curve, mul_assoc, ← Geometry.matrixHom_highest D C, ← map_mul,
    mul_inv_cancel, map_one, mul_one]

/-- The two specified highest-root matrices detect the full highest-root SL₂
centralizer; no restriction on the odd prime or positive field exponent is needed. -/
theorem commute_highestHom_of_curves (hp : Odd P.prime) (g : SplitGroup P)
    (hc : ∀ b : Bool, Commute (Geometry.matrixHom P g)
      (Geometry.highestCurve b (1 : ExtensionField P)))
    (a : SL(2, ExtensionField P)) : Commute g (highestHom D C a) := by
  let e := MulAut.conj (splitHighestWeyl D C)
  have hr (b : Bool) :
      Commute g (e (if b then positiveRoot P 1 1 else negativeRoot P 1 1)) := by
    apply Geometry.matrixHom_injective P
    simpa only [map_mul, e, matrixHom_conjugatedRoot] using (hc b).eq
  have hs (b : Bool) :
      Commute (e.symm g) (if b then positiveRoot P 1 1 else negativeRoot P 1 1) := by
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulEquiv.symm_apply_apply] using (hr b).map e.symm.toMonoidHom
  have hall : Commute (e.symm g) (D.hom 1 a) := by
    apply sl2_root_induction (fun a => Commute (e.symm g) (D.hom 1 a)) ?_ ?_ ?_ a
    · intro t
      simpa only [D.positive] using commute_positiveRoot_of_one hp (e.symm g) 1 (hs true) t
    · intro t
      simpa only [D.negative] using commute_negativeRoot_of_one hp (e.symm g) 1 (hs false) t
    · intro x y hx hy
      simpa only [map_mul] using hx.mul_right hy
  simpa only [highestHom, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, e, MulEquiv.apply_symm_apply] using hall.map e.toMonoidHom

/-- A faithful comparison of the four marked rank-one subgroups discharges the
geometric factorization. The comparison itself remains a separate obligation. -/
theorem highest_factorization_of_markedComparison (hp : Odd P.prime)
    (E : MarkedComparison D C) : HighestUnipotentFactorization D C := by
  intro g hn hc
  obtain ⟨n, hg⟩ := (matrixHom_isNilpotent_sub_one_iff g).mp hn
  have hcentral : E.hom g ∈ Subgroup.centralizer
      ((OrthogonalModel.highest (F := ExtensionField P)).range :
        Set (ClassicalOrthogonal.POmegaPlus 4 (ExtensionField P))) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    obtain ⟨a, rfl⟩ := E.highest_range.ge hx
    exact ((commute_highestHom_of_curves D C hp g hc a).map E.hom).symm.eq
  let x : Subgroup.centralizer
      ((OrthogonalModel.highest (F := ExtensionField P)).range :
        Set (ClassicalOrthogonal.POmegaPlus 4 (ExtensionField P))) :=
    ⟨E.hom g, hcentral⟩
  have hx : x ^ (P.prime ^ n) = 1 := by
    apply Subtype.ext
    exact (map_pow E.hom g _).symm.trans ((congrArg E.hom hg).trans (map_one E.hom))
  have hp2 : P.prime ≠ 2 := by rintro h; exact (by decide : ¬Odd (2 : ℕ)) (h ▸ hp)
  obtain ⟨a, ha⟩ := (E.arms_range D C).ge (OrthogonalModel.p_element_mem_arms P.prime hp2 x n hx)
  exact ⟨a, E.injective ha⟩

/-- Application to the exact inverse-conjugated split centralizer of the parent
index calculation, retaining only the missing marked model comparison. -/
theorem split_p_element_mem_of_markedComparison (hp : Odd P.prime)
    (E : MarkedComparison D C) (g : splitCentralizer D) (n : ℕ)
    (hg : g ^ (P.prime ^ n) = 1) : g.val ∈ splitComplementSubgroup D C :=
  split_p_element_mem_of_highest_factorization D C
    (highest_factorization_of_markedComparison D C hp E) g n hg

end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent
