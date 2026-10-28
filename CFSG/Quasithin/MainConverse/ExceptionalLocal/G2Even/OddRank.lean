module

public import CFSG.Quasithin.Defs
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero
public import Theory.Quasithin.Rank
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear
public import Theory.SpecificGroups.GL2.OddPrimeRank
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Odd-prime ranks of the full even-field G₂ parabolics

The short parabolic preserves the standard null plane. Its action on that
plane gives a homomorphism to `GL₂(F)` whose kernel is the five-root radical,
a 2-group. The established odd-rank bound for `GL₂` therefore gives rank at
most two for the full parabolic, including its split torus.

On the long side, the scalar on the distinguished singular line gives a
homomorphism from the full parabolic to `Fˣ`. Its kernel is the full long local
group. The latter maps onto `SL₂(F)` with a five-root 2-group kernel, and odd
p-subgroups of `SL₂(F)` are cyclic. Thus both the local kernel and the scalar
image contribute at most one generator at an odd prime.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, Theorem
0.1.2(1), printed pp.3--4 and 481--482. The concrete local quotients and
radical identifications are supplied by the ATLAS G₂ Lie-parabolic port.
-/

open Subgroup
open Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped MatrixGroups

namespace CFSG.Quasithin.MainConverse.G2Even

noncomputable section

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

noncomputable def shortGLHom : shortPlaneStabilizer (F := F) →* GL (Fin 2) F where
  toFun g := Matrix.GeneralLinearGroup.mk'' (shortRepresentation g) (by
    have hmat : shortRepresentation g * shortRepresentation g⁻¹ = 1 := by
      simpa only [map_mul, mul_inv, map_one] using
        congrArg shortRepresentation (mul_inv_cancel g)
    have hunit : IsUnit (shortRepresentation g) := by
      rw [isUnit_iff_exists_inv]
      exact ⟨shortRepresentation g⁻¹, hmat⟩
    exact (Matrix.isUnit_iff_isUnit_det _).mp hunit
  )
  map_one' := by
    apply Units.ext
    simp [shortRepresentation]
  map_mul' g h := by
    apply Units.ext
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    change shortRepresentation (g * h) = shortRepresentation g * shortRepresentation h
    exact (map_mul shortRepresentation g h)



variable {F : Type*} [Field F] [Finite F] [CharP F 2]

noncomputable def parabolicShortGLHom : parabolic₁ (F := F) →* GL (Fin 2) F :=
  shortGLHom.comp (inclusion parabolic₁_le_shortPlaneStabilizer)

theorem parabolicShortGLHom_ker : (parabolicShortGLHom (F := F)).ker =
    (radical₁ (F := F)).subgroupOf (parabolic₁ (F := F)) := by
  have hlocal : local₁ (F := F) ≤ parabolic₁ := by
    rw [← local₁_sup_borel]
    exact le_sup_left
  have hlocalPlane : local₁ (F := F) ≤ shortPlaneStabilizer :=
    hlocal.trans (show parabolic₁ (F := F) ≤ shortPlaneStabilizer from
      parabolic₁_le_shortPlaneStabilizer)
  ext g
  change shortGLHom ⟨g.val, parabolic₁_le_shortPlaneStabilizer g.property⟩ = 1 ↔
    g.val ∈ radical₁
  constructor
  · intro h
    let gS : shortPlaneStabilizer (F := F) :=
      ⟨g.val, parabolic₁_le_shortPlaneStabilizer g.property⟩
    have hmat : shortRepresentation gS = 1 := by
      exact congrArg (fun z : GL (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F)) h
    have hspecial : g.val ∈ shortSpecial := by
      refine ⟨gS, ?_, rfl⟩
      change Matrix.det (shortRepresentation gS) = 1
      simpa using congrArg Matrix.det hmat
    have hlocal' : g.val ∈ local₁ := by
      rw [local₁_eq_shortSpecial]
      exact hspecial
    let x : local₁ (F := F) := ⟨g.val, hlocal'⟩
    have hx : shortSLHom x = 1 := by
      apply Subtype.ext
      have hxx : (⟨g.val, hlocalPlane x.property⟩ :
          shortPlaneStabilizer (F := F)) = gS := by
        apply Subtype.ext
        rfl
      change shortRepresentation (⟨x.val, _⟩ : shortPlaneStabilizer (F := F)) = 1
      rw [hxx]
      exact hmat
    have hxmem : x ∈ (shortSLHom (F := F)).ker := MonoidHom.mem_ker.mpr hx
    rw [shortSLHom_ker] at hxmem
    exact hxmem
  · intro hrad
    let x : local₁ (F := F) := ⟨g.val, radical₁_le_local₁ hrad⟩
    have hxmem : x ∈ (shortSLHom (F := F)).ker := by
      rw [shortSLHom_ker]
      exact hrad
    have hx : shortSLHom x = 1 := MonoidHom.mem_ker.mp hxmem
    apply Units.ext
    change shortRepresentation
      ⟨g.val, parabolic₁_le_shortPlaneStabilizer g.property⟩ = 1
    have hxx : (⟨g.val, hlocalPlane x.property⟩ :
        shortPlaneStabilizer (F := F)) =
        (⟨g.val, parabolic₁_le_shortPlaneStabilizer g.property⟩ :
          shortPlaneStabilizer (F := F)) := by
      apply Subtype.ext
      rfl
    have hxmat := congrArg Subtype.val hx
    change shortRepresentation (⟨x.val, _⟩ : shortPlaneStabilizer (F := F)) = 1 at hxmat
    rw [hxx] at hxmat
    exact hxmat



variable {F : Type*} [Field F] [Finite F] [CharP F 2]

public theorem short_parabolic_primeRank_le_two {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p (parabolic₁ (F := F)) ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let π := parabolicShortGLHom (F := F)
  have hker : IsPGroup 2 π.ker := by
    rw [parabolicShortGLHom_ker]
    exact radical₁_isTwoGroup.comap_subtype
  have hz : primeRank p π.ker = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    intro hd
    obtain ⟨n, hn⟩ := hker.exists_card_eq
    rw [hn] at hd
    have hpd : p ∣ 2 := hp.dvd_of_dvd_pow hd
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpd
    apply ho.not_two_dvd_nat
    rw [hp2]
  calc
    primeRank p (parabolic₁ (F := F)) ≤ primeRank p π.ker +
        primeRank p (GL (Fin 2) F) := Theory.GroupTheory.primeRank_le_ker_add π
    _ = primeRank p (GL (Fin 2) F) := by rw [hz, zero_add]
    _ ≤ 2 := Matrix.GeneralLinearGroup.primeRank_le_two_of_odd F ho



variable {F : Type*} [Field F] [Finite F] [CharP F 2]

noncomputable def longScalarHom : parabolic₂ (F := F) →* Fˣ :=
  lineScalarHom.comp (inclusion (parabolic_le_pointStabilizer (F := F)))

omit [Finite F] in
theorem longScalarHom_ker : (longScalarHom (F := F)).ker =
    (local₂ (F := F)).subgroupOf (parabolic₂ (F := F)) := by
  ext g
  let gP : pointStabilizer (K := F) :=
    ⟨g.val, parabolic_le_pointStabilizer g.property⟩
  change lineScalarHom gP = 1 ↔ g.val ∈ local₂
  constructor
  · intro h
    have hm : gP ∈ (lineScalarHom (K := F)).ker := MonoidHom.mem_ker.mpr h
    rw [lineScalarHom_kernel] at hm
    rw [local₂_eq_fixingFirstVector]
    exact hm
  · intro h
    have hm : gP ∈ (fixingFirstVector (K := F)).comap pointStabilizer.subtype := by
      rw [← local₂_eq_fixingFirstVector]
      exact h
    have hm' : gP ∈ (lineScalarHom (K := F)).ker := by
      rw [lineScalarHom_kernel]
      exact hm
    exact MonoidHom.mem_ker.mp hm'

private theorem sl2_primeRank_le_one {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p SL(2,F) ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow p SL(2,F) := default
  apply P.primeRank_le_one_of_isCyclic
  exact Matrix.SL2.odd_pGroup_isCyclic_of_injective P.isPGroup'
    (by rintro rfl; exact ho.not_two_dvd_nat (dvd_refl 2))
    (P : Subgroup (SL(2,F))).subtype (P : Subgroup (SL(2,F))).subtype_injective

public theorem long_parabolic_primeRank_le_two {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p (parabolic₂ (F := F)) ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let f := longSLHom (F := F)
  have hker : IsPGroup 2 f.ker := by
    rw [longSLHom_ker]
    exact radical₂_isTwoGroup.comap_subtype
  have hz : primeRank p f.ker = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    intro hd
    obtain ⟨n, hn⟩ := hker.exists_card_eq
    rw [hn] at hd
    have hpd : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow hd
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hpd
    apply ho.not_two_dvd_nat
    rw [hp2]
  have hlocal : primeRank p (local₂ (F := F)) ≤ 1 := by
    calc
      primeRank p (local₂ (F := F)) ≤ primeRank p f.ker + primeRank p SL(2,F) :=
        Theory.GroupTheory.primeRank_le_ker_add f
      _ = primeRank p SL(2,F) := by rw [hz, zero_add]
      _ ≤ 1 := sl2_primeRank_le_one hp ho
  let χ := longScalarHom (F := F)
  have hχ : primeRank p χ.ker ≤ 1 := by
    rw [longScalarHom_ker]
    let e : (local₂ (F := F)).subgroupOf (parabolic₂ (F := F)) ≃* local₂ (F := F) :=
      subgroupOfEquivOfLe (local₂_le_parabolic₂ (F := F))
    have he : primeRank p ((local₂ (F := F)).subgroupOf (parabolic₂ (F := F))) =
        primeRank p (local₂ (F := F)) :=
      Theory.GroupTheory.primeRank_equiv p e
    rw [he]
    exact hlocal
  have hunit : primeRank p Fˣ ≤ 1 := by
    let P : Sylow p Fˣ := default
    apply P.primeRank_le_one_of_isCyclic
    exact Subgroup.isCyclic_of_le (show (P : Subgroup Fˣ) ≤ ⊤ from le_top)
  calc
    primeRank p (parabolic₂ (F := F)) ≤ primeRank p χ.ker + primeRank p Fˣ :=
      Theory.GroupTheory.primeRank_le_ker_add χ
    _ ≤ 1 + 1 := Nat.add_le_add hχ hunit
    _ ≤ 2 := by decide

public theorem parabolics_odd_primeRank_le_two {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p (parabolic₁ (F := F)) ≤ 2 ∧
      primeRank p (parabolic₂ (F := F)) ≤ 2 :=
  ⟨short_parabolic_primeRank_le_two hp ho, long_parabolic_primeRank_le_two hp ho⟩

public theorem parabolics_odd_primeRank_le_two_of_card {F : Type*} [Field F] [Finite F]
    {f : ℕ} (hcard : Nat.card F = 2 ^ f) {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p (parabolic₁ (F := F)) ≤ 2 ∧
      primeRank p (parabolic₂ (F := F)) ≤ 2 := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  exact parabolics_odd_primeRank_le_two hp ho


end
end CFSG.Quasithin.MainConverse.G2Even
