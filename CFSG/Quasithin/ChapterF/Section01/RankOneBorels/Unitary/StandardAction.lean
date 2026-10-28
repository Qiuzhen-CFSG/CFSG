module

public import BenderSuzuki.SE.Borel
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FieldParameters
public import Theory.GroupTheory.SolvableNormalSup

/-!
# The standard PSU₃ Borel, including PSU₃(2)

For the antidiagonal Hermitian form over a field of order (2^n)², the root
subgroup is Sylow and its normalizer is the actual isotropic-point stabilizer.
The normalizer is proper and solvable, with a cyclic odd-order complement.
Its natural matrix action and regular root-group action are retained.

The proof adapts `BenderSuzuki.psu_sylow_normalizer_action`: its Sylow and
normalizer argument only needs n > 0. Huppert II.10.12 supplies the concrete
root subgroup and torus, including at n = 1; the fixed-field cardinality is
derived from the stored Frobenius involution. Solvability follows from the
normal two-group and cyclic complement.

Source: Aschbacher–Smith, printed pp.259–260, F.1.3(1), and Huppert II.10.12.
Uniqueness among all proper Sylow overgroups is a separate generation
problem and is not asserted here. Arbitrary Gram matrices and SU₃ require
additional results before this proves either complete source alternative.
-/

noncomputable section
open BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped LinearAlgebra.Projectivization
namespace CFSG.Quasithin.ChapterF.Source.Unitary
universe u

private theorem sylow_normalizer_solvable_of_cyclic_complement
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (D : Subgroup G)
    (hD : D ≤ Subgroup.normalizer ((S : Subgroup G) : Set G)) (hcyc : IsCyclic D)
    (hsup : (S : Subgroup G) ⊔ D = Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    Group.IsSolvable (Subgroup.normalizer ((S : Subgroup G) : Set G)) := by
  let B := Subgroup.normalizer ((S : Subgroup G) : Set G)
  let : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
  let : IsCyclic D := hcyc
  let := IsCyclic.commGroup (α := D)
  let eS := Subgroup.subgroupOfEquivOfLe (S : Subgroup G).le_normalizer
  let eD := Subgroup.subgroupOfEquivOfLe hD
  let : Group.IsSolvable ((S : Subgroup G).subgroupOf B) :=
    Group.isSolvable_of_isSolvable_injective (f := eS.toMonoidHom) eS.injective
  let : Group.IsSolvable (D.subgroupOf B) :=
    Group.isSolvable_of_isSolvable_injective (f := eD.toMonoidHom) eD.injective
  apply Group.isSolvable_of_normal_sup_eq_top
    ((S : Subgroup G).subgroupOf B) (D.subgroupOf B)
  rw [← Subgroup.subgroupOf_sup (S : Subgroup G).le_normalizer hD, hsup]
  exact Subgroup.subgroupOf_self B


/-- The concrete natural Borel action and its local group structure, for all n > 0. -/
public theorem standard_psu_borel_data
    {K : Type u} [Field K] [Finite K]
    (J : HermitianForm 3 K) (n : ℕ) (hn : 0 < n)
    (hKcard : Nat.card K = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    let q := 2 ^ n
    let P := ℙ K (Fin 3 → K)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
        x = Projectivization.mk K v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let Omega := {x : P // x ∈ A}
    let G := ProjectiveSpecialUnitaryMatrixGroup J
    ∃ (rho : G →* Equiv.Perm Omega) (pinf : Omega) (S : Sylow 2 G),
      (∃ D : Subgroup G, D ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) ∧
        Nat.Coprime 2 (Nat.card D) ∧ IsCyclic D ∧
        Disjoint (S : Subgroup G) D ∧
        (S : Subgroup G) ⊔ D = Subgroup.normalizer ((S : Subgroup G) : Set G)) ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) < ⊤ ∧
      Group.IsSolvable (Subgroup.normalizer ((S : Subgroup G) : Set G)) ∧
      Function.Injective rho ∧
      (∀ g : G, ∀ z : Omega, ∀ M : J.specialSubgroup,
        Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) K) =
            (g : Matrix.ProjGenLinGroup (Fin 3) K) →
          ((rho g z : Omega) : P) =
            (Matrix.GeneralLinearGroup.toLin
              (M : GL (Fin 3) K)).toLinearEquiv • (z : P)) ∧
      Nat.card S = q ^ 3 ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho ∧
      (∀ a b : Omega, a ≠ pinf → b ≠ pinf →
        ∃! s : S, rho (s : G) a = b) ∧
      (∀ a b c d : Omega, a ≠ b → c ≠ d →
        ∃ g : G, rho g a = c ∧ rho g b = d) := by
  have hfixed_card := fixed_card J n hn hKcard hconj
  let q := 2 ^ n
  let P := ℙ K (Fin 3 → K)
  let A : Set P :=
    {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
      x = Projectivization.mk K v hv ∧
        dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Omega := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  change ∃ (rho : G →* Equiv.Perm Omega) (pinf : Omega)
      (S : Sylow 2 G),
    (∃ D : Subgroup G, D ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) ∧
      Nat.Coprime 2 (Nat.card D) ∧ IsCyclic D ∧
      Disjoint (S : Subgroup G) D ∧
      (S : Subgroup G) ⊔ D = Subgroup.normalizer ((S : Subgroup G) : Set G)) ∧
    Subgroup.normalizer ((S : Subgroup G) : Set G) < ⊤ ∧
    Group.IsSolvable (Subgroup.normalizer ((S : Subgroup G) : Set G)) ∧
    Function.Injective rho ∧
    (∀ g : G, ∀ z : Omega, ∀ M : J.specialSubgroup,
      Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) K) =
          (g : Matrix.ProjGenLinGroup (Fin 3) K) →
        ((rho g z : Omega) : P) =
          (Matrix.GeneralLinearGroup.toLin
            (M : GL (Fin 3) K)).toLinearEquiv • (z : P)) ∧
    Nat.card S = q ^ 3 ∧
    Subgroup.normalizer ((S : Subgroup G) : Set G) =
      (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho ∧
    (∀ a b : Omega, a ≠ pinf → b ≠ pinf →
      ∃! s : S, rho (s : G) a = b) ∧
    (∀ a b c d : Omega, a ≠ b → c ≠ d →
      ∃ g : G, rho g a = c ∧ rho g b = d)
  rcases External.huppert_II_10_12 J q
      (by simpa [q] using hKcard)
      (by simpa [q] using hfixed_card) hJstandard with
    ⟨hOmegaCard, rho, pinf, hrho, hnatural, _hUcard,
      hroot, htwo, _hGcard, _hthree⟩
  rcases hroot with
    ⟨R, H, hR_le_U, hH_le_U, hU_le_normalizer_R,
      hR_disjoint_H, hR_sup_H, hH_cyclic, hRcard,
      _hcommutator_center, _hcommutator_card, hHcard,
      hRregular, _hcoordR, _hHcoord, _hHcoord_surjective⟩
  let : Fintype K := Fintype.ofFinite K
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective
      (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
        (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  have hq : 1 < q := by
    dsimp [q]
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hRpower : Nat.card R = 2 ^ (n * 3) := by
    simpa [q, pow_mul] using hRcard
  have hRp : IsPGroup 2 R := IsPGroup.of_card hRpower
  have hq_even : Even q := by
    dsimp [q]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hq_sq_even : Even (q ^ 2) :=
    hq_even.pow_of_ne_zero (by norm_num)
  have hq_sq_pos : 0 < q ^ 2 :=
    pow_pos (by omega) 2
  have hq_sq_sub_one_odd : Odd (q ^ 2 - 1) :=
    Nat.Even.sub_odd hq_sq_pos hq_sq_even odd_one
  have hgcd_dvd : Nat.gcd (q + 1) 3 ∣ q ^ 2 - 1 := by
    have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq q 1
    rw [hfactor]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (q + 1) 3) _
  have hHodd : Odd (Nat.card H) := by
    rw [hHcard]
    exact Odd.of_dvd_nat hq_sq_sub_one_odd
      (Nat.div_dvd_of_dvd hgcd_dvd)
  have hHnot : ¬ 2 ∣ Nat.card H := by
    intro htwo_dvd
    exact (Nat.not_even_iff_odd.mpr hHodd)
      (even_iff_two_dvd.mpr htwo_dvd)
  obtain ⟨PU, hPU⟩ :=
    exists_sylow_map_eq_of_normal_complement
      hR_le_U hH_le_U hU_le_normalizer_R
      hR_disjoint_H hR_sup_H hRp hHnot
  let : MulAction G Omega := MulAction.compHom Omega rho
  have hR_ne : R ≠ ⊥ := by
    intro hRbot
    have hRcard_one : Nat.card R = 1 := by rw [hRbot]; simp
    have hqcube_one : q ^ 3 = 1 := hRcard.symm.trans hRcard_one
    have hq_one : q = 1 :=
      (pow_eq_one_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp hqcube_one
    omega
  have hnormalizer :
      Subgroup.normalizer (R : Set G) = MulAction.stabilizer G pinf :=
    normalizer_eq_stabilizer_of_regular_compl R pinf hR_le_U hR_ne
      hRregular hU_le_normalizer_R
  have hnormalizer_le :
      Subgroup.normalizer
          (((PU : Subgroup _).map
            ((MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho).subtype :
              Subgroup G) : Set G) ≤
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho := by
    rw [hPU]
    have hstab :
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho =
          MulAction.stabilizer G pinf := by
      ext g
      change (rho g) pinf = pinf ↔ (rho g) pinf = pinf
      rfl
    rw [hstab]
    exact hnormalizer.le
  obtain ⟨S, hSmap⟩ :=
    exists_sylow_map_eq_of_normalizer_le PU hnormalizer_le
  have hSR : (S : Subgroup G) = R := hSmap.trans hPU
  have hScard : Nat.card S = q ^ 3 := by
    rw [hSR]
    exact hRcard
  have hSnormalizer :
      Subgroup.normalizer ((S : Subgroup G) : Set G) =
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho := by
    rw [hSR]
    exact hnormalizer
  have hSregular : IsRegularOn (S : Subgroup G)
      {omega : Omega | omega ≠ pinf} := by
    rw [hSR]
    exact hRregular
  have hSregular_rho :
      ∀ a b : Omega, a ≠ pinf → b ≠ pinf →
        ∃! s : S, rho (s : G) a = b := by
    intro a b ha hb
    exact hSregular ha hb
  have hproper : Subgroup.normalizer ((S : Subgroup G) : Set G) < ⊤ := by
    have hcardOmega : 1 < Nat.card Omega := by
      rw [hOmegaCard]
      have : 0 < q ^ 3 := pow_pos (by omega) _
      omega
    have : Nontrivial Omega := Finite.one_lt_card_iff_nontrivial.mp hcardOmega
    obtain ⟨a, ha⟩ := exists_ne pinf
    obtain ⟨g, hg, _⟩ := htwo pinf a a pinf ha.symm ha
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hmem : g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by rw [htop]; trivial
    rw [hSnormalizer] at hmem
    exact ha (hg.symm.trans hmem)
  have hHN : H ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    rw [hSnormalizer]
    exact hH_le_U
  have hSH : (S : Subgroup G) ⊔ H =
      Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    rw [hSR, hR_sup_H]
    exact hnormalizer.symm
  have hsolv := sylow_normalizer_solvable_of_cyclic_complement S H hHN hH_cyclic hSH
  refine ⟨rho, pinf, S, ?_, hproper, hsolv, hrho, hnatural, hScard,
    hSnormalizer, hSregular_rho, htwo⟩
  refine ⟨H, hHN, ?_, hH_cyclic, ?_, hSH⟩
  · exact Nat.prime_two.coprime_iff_not_dvd.mpr hHnot
  · rw [hSR]
    exact disjoint_iff.mpr hR_disjoint_H

end CFSG.Quasithin.ChapterF.Source.Unitary
