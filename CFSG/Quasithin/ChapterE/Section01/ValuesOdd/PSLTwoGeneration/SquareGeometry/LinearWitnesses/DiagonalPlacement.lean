module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.Structure
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.Actors
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.TorusWitness
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.OvergroupModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Sylow
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.InnerSymmetric
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups
public import Mathlib.NumberTheory.Multiplicity

/-!
# Prime-square PGL₂ placement: inner and outer four-group witnesses

An outer four-group has a reflected nonsplit-torus witness of order `4*r`,
where r is an odd prime divisor of `p²+1`. Its intersection with the original
Sylow subgroup is Sylow. This is the odd-field reflected-torus construction,
with the split alternative excluded by `8 ∣ p²-1`.

The ambient Sylow has order divisible by sixteen. Thus, among the proposed
maximal-overgroup models, only the split torus normalizer can contain it.
An S₄ subgroup escapes every dihedral group: squares commute in a dihedral
group, but two explicit squared three-cycles in S₄ do not commute. An
order-eight overlap then gives the literal Sylow intersection for an inner
actor's S₄ witness.

The final `concreteLocalGeometryAt` theorem discharges both geometric inputs
using the maximal-overgroup classification and paired inner S₄ normalizers.
It supplies the exact PGL₂ placement premise of
`LinearWitnesses.largeFamilyEscape_of_linear_model_geometry`, including
p = 3 and p = 5. Intrinsic E1 verification remains in `PrimeGeometry.OddSections`.

Source: Aschbacher--Smith, A.2.3(2), E.1.2 and E.1.14(6), printed
pp.33, 209--210 and 214; the latter cites Aschbacher (1982), Lemma 4.10.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement

open Subgroup GorensteinWalter

variable {F : Type*} [Field F] [Finite F]

local instance : Finite (PGL2 F) := Finite.of_surjective
  Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem dihedral_squares_commute {n : ℕ} (x y : DihedralGroup n) :
    x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2 := by
  cases x <;> cases y <;> simp [pow_two, add_comm]

private theorem symmetric_four_not_injective_dihedral
    (n : ℕ) (f : Equiv.Perm (Fin 4) →* DihedralGroup n) :
    ¬ Function.Injective f := by
  intro hf
  have hh (x y : Equiv.Perm (Fin 4)) : x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2 := by
    apply hf
    simpa only [map_mul, map_pow] using dihedral_squares_commute (f x) (f y)
  let x : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
  let y : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 3
  have hne : x ^ 2 * y ^ 2 ≠ y ^ 2 * x ^ 2 := by decide +kernel
  exact hne (hh x y)

private theorem symmetric_four_not_le_dihedral
    {G : Type*} [Group G] (H M : Subgroup G) {n : ℕ}
    (eH : H ≃* Equiv.Perm (Fin 4)) (eM : M ≃* DihedralGroup n) : ¬ H ≤ M := by
  intro hHM
  let f := eM.toMonoidHom.comp ((inclusion hHM).comp eH.symm.toMonoidHom)
  exact symmetric_four_not_injective_dihedral n f
    (eM.injective.comp ((inclusion_injective hHM).comp eH.symm.injective))

/-- The ambient PGL₂ Sylow order in odd square degree is divisible by sixteen. -/
theorem sixteen_dvd_card {p : ℕ} (ho : Odd p) (hF : Nat.card F = p ^ 2) :
    16 ∣ Nat.card (PGL2 F) := by
  have h8 : 8 ∣ Nat.card F - 1 := by
    rw [hF]
    exact Nat.eight_dvd_sq_sub_one_of_odd ho
  have h2 : 2 ∣ Nat.card F + 1 := by
    have hq : Odd (Nat.card F) := hF ▸ ho.pow
    obtain ⟨k, hk⟩ := hq
    exact ⟨k + 1, by omega⟩
  have h16 : 16 ∣ Nat.card F ^ 2 - 1 := by
    have he : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
      simpa using Nat.sq_sub_sq (Nat.card F) 1
    rw [he]
    exact Nat.mul_dvd_mul h2 h8
  rw [pgl2_card_formula]
  exact dvd_mul_of_dvd_right h16 _

/-- Of the proposed maximal-overgroup models, only the split torus
normalizer can contain the specified Sylow in square degree. This does not
prove the maximal-overgroup classification. -/
theorem split_overgroup_of_model {p : ℕ} (ho : Odd p) (hF : Nat.card F = p ^ 2)
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hTM : (T : Subgroup (PGL2 F)) ≤ M)
    (hM : PrimeGeometry.Diagonal.SylowOvergroupModel F M) :
    Nonempty (M ≃* DihedralGroup (Nat.card F - 1)) := by
  have h16M : 16 ∣ Nat.card M :=
    (T.pow_dvd_card_of_pow_dvd_card
      (show 2 ^ 4 ∣ Nat.card (PGL2 F) from sixteen_dvd_card ho hF)).trans
        (card_dvd_of_le hTM)
  unfold PrimeGeometry.Diagonal.SylowOvergroupModel at hM
  rcases hM with heM | heM
  · obtain ⟨eM⟩ := heM
    have hc : Nat.card M = 24 := by
      rw [Nat.card_congr eM.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
      norm_num
    rw [hc] at h16M
    norm_num at h16M
  · obtain ⟨n, hn, ⟨eM⟩⟩ := heM
    rcases hn with rfl | rfl
    · exact ⟨eM⟩
    · rw [Nat.card_congr eM.toEquiv, DihedralGroup.nat_card, hF] at h16M
      obtain ⟨k, hk⟩ := Nat.eight_dvd_sq_sub_one_of_odd ho
      have hpos : 0 < p ^ 2 := by
        rw [← hF]
        exact Nat.card_pos
      obtain ⟨m, hm⟩ := h16M
      omega

/-- Every outer four-group has a nonsplit dihedral witness, with its actual
Sylow intersection and an odd prime divisor of `p²+1`. No escape hypothesis
is needed to construct this witness. -/
theorem outer_nonsplit_witness {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hlarge : 5 < p ^ 2) (hF : Nat.card F = p ^ 2)
    (T : Sylow 2 (PGL2 F)) (A : Subgroup (PGL2 F))
    (hA : IsKleinFour A) (hAT : A ≤ (T : Subgroup (PGL2 F)))
    (hAJ : ¬ A ≤ Matrix.ProjectiveSpecialLinearGroup.toPGL.range) :
    ∃ H : Subgroup (PGL2 F), A ≤ H ∧
      (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup (PGL2 F)).subgroupOf H) ∧
      ∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∣ p ^ 2 + 1 ∧
        Nonempty (H ≃* DihedralGroup (2 * r)) := by
  have hq : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, ho, by decide, hF⟩
  have hq3 : 3 < Nat.card F := by omega
  have hAJ' : ¬ A ≤ commutator (PGL2 F) := by
    rwa [pgl2_commutator_eq_psl2_range_of_card_gt_three F hq hq3]
  obtain ⟨H, hAH, hS, r, hr, hro, he, hlow⟩ :=
    PrimeGeometry.Diagonal.outer_kleinFour_dihedral_witness F hq hq3 T A hA hAT hAJ'
  refine ⟨H, hAH, hS, r, hr, hro, ?_, he⟩
  rcases hlow with ⟨_, hsplit⟩ | ⟨hdiv, _⟩
  · rw [hF] at hsplit
    obtain ⟨k, hk⟩ := Nat.eight_dvd_sq_sub_one_of_odd ho
    obtain ⟨m, hm⟩ := hsplit
    omega
  · simpa only [hF] using hdiv

/-- The nonsplit witness escapes a proposed Sylow overgroup: its odd rotation
prime divides `p²+1`, while the overgroup is a split torus normalizer. -/
theorem outer_escape_of_overgroup_model {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hlarge : 5 < p ^ 2) (hF : Nat.card F = p ^ 2)
    (T : Sylow 2 (PGL2 F)) (A M : Subgroup (PGL2 F))
    (hA : IsKleinFour A) (hAT : A ≤ (T : Subgroup (PGL2 F)))
    (hAJ : ¬ A ≤ Matrix.ProjectiveSpecialLinearGroup.toPGL.range)
    (hTM : (T : Subgroup (PGL2 F)) ≤ M)
    (hM : PrimeGeometry.Diagonal.SylowOvergroupModel F M) :
    ∃ H : Subgroup (PGL2 F), A ≤ H ∧
      (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup (PGL2 F)).subgroupOf H) ∧
      PrimeGeometry.LocalModel A H ∧ ¬ H ≤ M := by
  obtain ⟨H, hAH, hS, r, hr, hro, hrplus, ⟨eH⟩⟩ :=
    outer_nonsplit_witness hp ho hlarge hF T A hA hAT hAJ
  obtain ⟨eM⟩ := split_overgroup_of_model ho hF T M hTM hM
  refine ⟨H, hAH, hS, Or.inr ⟨r, hr, hro, ⟨eH⟩⟩, ?_⟩
  intro hHM
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    have := hro.not_two_dvd_nat
    omega
  have hr2 : ¬ r ∣ 2 := by
    intro hd
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hrM : r ∣ 2 * (p ^ 2 - 1) := by
    have hd := card_dvd_of_le hHM
    rw [Nat.card_congr eH.toEquiv, Nat.card_congr eM.toEquiv,
      DihedralGroup.nat_card, DihedralGroup.nat_card, hF] at hd
    exact (show r ∣ 2 * (2 * r) from ⟨4, by ring⟩).trans hd
  have hrminus : r ∣ p ^ 2 - 1 := (hr.dvd_mul.mp hrM).resolve_left hr2
  apply hr2
  convert Nat.dvd_sub hrplus hrminus using 1
  omega

/-- A positioned S₄ through an inner actor escapes every proposed square-field
Sylow overgroup. The order-eight overlap supplies the literal Sylow equality. -/
theorem inner_escape_of_symmetric_placement {p : ℕ}
    (ho : Odd p) (hF : Nat.card F = p ^ 2)
    (T : Sylow 2 (PGL2 F)) (A D H M : Subgroup (PGL2 F))
    (hAH : A ≤ H) (hDT : D ≤ (T : Subgroup (PGL2 F))) (hDH : D ≤ H)
    (hD : Nat.card D = 8) (eH : H ≃* Equiv.Perm (Fin 4))
    (hAn : ¬ (A.subgroupOf H).Normal)
    (hTM : (T : Subgroup (PGL2 F)) ≤ M)
    (hM : PrimeGeometry.Diagonal.SylowOvergroupModel F M) :
    A ≤ H ∧
      (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup (PGL2 F)).subgroupOf H) ∧
      PrimeGeometry.LocalModel A H ∧ ¬ H ≤ M := by
  obtain ⟨eM⟩ := split_overgroup_of_model ho hF T M hTM hM
  exact ⟨hAH, PrimeGeometry.Inner.sylow_intersection_symmetric_four T D H hDT hDH hD eH,
    Or.inl ⟨⟨eH⟩, hAn⟩, symmetric_four_not_le_dihedral H M eH eM⟩

/-- The exact PGL₂ consumer, conditional on the maximal-overgroup classification
and positioned inner S₄ subgroups. The outer construction and both escape
arguments are discharged here; `concreteLocalGeometryAt` supplies both inputs. -/
theorem concreteGeometryAt_of_overgroups_and_inner_symmetric
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 5 < p ^ 2)
    (hF : Nat.card F = p ^ 2) (T : Sylow 2 (PGL2 F))
    (hover : ∀ M : Subgroup (PGL2 F), IsCoatom M →
      (T : Subgroup (PGL2 F)) ≤ M → PrimeGeometry.Diagonal.SylowOvergroupModel F M)
    (hinner : ∀ A : Subgroup (PGL2 F), IsKleinFour A →
      A ≤ (T : Subgroup (PGL2 F)) → A ≤ Matrix.ProjectiveSpecialLinearGroup.toPGL.range →
      ∃ H D : Subgroup (PGL2 F), A ≤ H ∧ D ≤ (T : Subgroup (PGL2 F)) ∧
        D ≤ H ∧ Nat.card D = 8 ∧ Nonempty (H ≃* Equiv.Perm (Fin 4)) ∧
          ¬ (A.subgroupOf H).Normal) :
    PrimeGeometry.ConcreteLocalGeometryAt T := by
  intro Ω hΩ hActors M hM hTM hNM
  have hq : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, ho, by decide, hF⟩
  obtain ⟨A, hAΩ, hAT, hA⟩ :=
    PrimeGeometry.Diagonal.exists_four_actor F hq T Ω hΩ hActors M hM.ne_top hNM
  refine ⟨A, hAΩ, hAT, hA, ?_⟩
  by_cases hAJ : A ≤ Matrix.ProjectiveSpecialLinearGroup.toPGL.range
  · obtain ⟨H, D, hAH, hDT, hDH, hD, ⟨eH⟩, hAn⟩ := hinner A hA hAT hAJ
    exact ⟨H, inner_escape_of_symmetric_placement ho hF T A D H M
      hAH hDT hDH hD eH hAn hTM (hover M hM hTM)⟩
  · exact outer_escape_of_overgroup_model hp ho hlarge hF T A M hA hAT hAJ
      hTM (hover M hM hTM)

/-- Every odd prime-square PGL₂ model has the concrete local geometry required
by the diagonal branch of `largeFamilyEscape_of_linear_model_geometry`.
The maximal-overgroup and positioned inner S₄ premises are fully discharged;
the witnesses retain the literal intersection with the specified Sylow. -/
theorem concreteLocalGeometryAt
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 5 < p ^ 2)
    (hF : Nat.card F = p ^ 2) :
    ∀ T : Sylow 2 (PGL2 F), PrimeGeometry.ConcreteLocalGeometryAt T := by
  let : Fact p.Prime := ⟨hp⟩
  intro T
  exact concreteGeometryAt_of_overgroups_and_inner_symmetric hp ho hlarge hF T
    (MaximalOvergroups.sylowOvergroupModel_of_square_card ho hlarge hF T)
    (InnerSymmetric.exists_inner_symmetric hp ho hlarge hF T)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement
