module

public import Glauberman.ZStar.LocalSectionCharacter
public import Theory.Character.ModularBlock.PrincipalKernel
public import FeitThompson.PCore.CentralizerControl

/-!
# Kernel witnesses for local section invariance

An actual centralizer representation agreeing with an ambient section on the
local odd core proves section invariance whenever that core lies in its kernel.
The global affording representation supplies such a witness when the local
odd core maps into the global odd core; the principal-block kernel theorem
then applies. Existing solvable centralizer control provides this containment
for a finite solvable ambient group and an involution.

This module preserves the kernel-witness and solvable-case APIs in the final
part of historical `Submission/ZStar/LocalBlockSection.lean` at commit
`c3503435`. It reuses the existing involution, odd-core, and block definitions.
The main LocalBlockSection module re-exports these alternate sufficient
witnesses alongside its more general canonical support interface.
-/

public section

noncomputable section
open scoped BigOperators
namespace Glauberman.ZStar.LocalBlockSection
open ModularBlock ModularBlock.PrincipalBlockConstruction BenderSuzuki.PFAppendixIII
universe u
attribute [local instance] Fintype.ofFinite
variable {G : Type u} [Group G] [Finite G]

/-- An alternative sufficient representation-level witness for the local
section calculation.

This is stronger than the generalized-decomposition expansion above, but is
convenient whenever an actual local representation is already available.
Only agreement on the odd core is recorded, since those are the only values
used below. -/
structure LocalSectionKernelWitness
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G) where
  n : ℕ
  theta : Representation ℂ (Subgroup.centralizer ({z} : Set G)) (Fin n → ℂ)
  core_le_ker :
    pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)) ≤ theta.ker
  agrees_on_core : ∀ x : Subgroup.centralizer ({z} : Set G),
    x ∈ pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)) →
      d.chi i (ConjClasses.mk (z * (x : G))) =
        theta.character (selfInCentralizer z * x)

/-- Once the local section representation is known to lie over the local
principal block, its odd-core kernel gives section invariance immediately. -/
theorem section_invariance_of_localSectionKernelWitness
    (d : PrincipalCongruenceBlockData G) {i : d.I} {z v : G}
    (hlocal : LocalSectionKernelWitness d i z)
    (hv : v ∈
      (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype) :
    d.chi i (ConjClasses.mk (z * v)) = d.chi i (ConjClasses.mk z) := by
  rcases Subgroup.mem_map.mp hv with ⟨vC, hvC, rfl⟩
  have hagree :
      d.chi i
          (ConjClasses.mk
            (z * (Subgroup.centralizer ({z} : Set G)).subtype vC)) =
        hlocal.theta.character (selfInCentralizer z * vC) := by
    simpa using hlocal.agrees_on_core vC hvC
  have hagreeOne :
      d.chi i (ConjClasses.mk z) =
        hlocal.theta.character (selfInCentralizer z) := by
    simpa using hlocal.agrees_on_core 1 (pPrimeCore 2 _).one_mem
  rw [hagree, hagreeOne]
  have hvker : vC ∈ hlocal.theta.ker := hlocal.core_le_ker hvC
  rw [MonoidHom.mem_ker] at hvker
  simp [Representation.character, map_mul, hvker]

/-- A family of the local witnesses supplies exactly the section-invariance
field expected by `PrincipalCongruenceBlockData.toPrincipalTwoBlockData`. -/
theorem principalBlock_section_invariance_of_localSectionKernelWitnesses
    (d : PrincipalCongruenceBlockData G)
    (hlocal : ∀ i ∈ d.block, ∀ z : G, IsInvolution z →
      LocalSectionKernelWitness d i z) :
    ∀ i ∈ d.block, ∀ z : G, IsInvolution z → ∀ v : G,
      v ∈ (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype →
      d.chi i (ConjClasses.mk (z * v)) = d.chi i (ConjClasses.mk z) := by
  intro i hi z hzI v hv
  exact section_invariance_of_localSectionKernelWitness
    d (hlocal i hi z hzI) hv

/-- The global affording representation itself is a local witness whenever
the centralizer odd core maps into the global odd core. -/
@[expose] noncomputable def localSectionKernelWitness_of_localCore_le_globalCore
    (d : PrincipalCongruenceBlockData G) {i : d.I} (hi : i ∈ d.block)
    (z : G)
    (hlocal :
      (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype ≤
        pPrimeCore 2 G) :
    LocalSectionKernelWitness d i z := by
  let n : ℕ := Classical.choose (d.complete.1 i).1
  have hn : ∃ rho : Representation ℂ G (Fin n → ℂ),
      d.chi i = characterClassFunction rho :=
    Classical.choose_spec (d.complete.1 i).1
  let rho : Representation ℂ G (Fin n → ℂ) := Classical.choose hn
  have hchar : d.chi i = characterClassFunction rho :=
    Classical.choose_spec hn
  refine {
    n := n
    theta := rho.comp (Subgroup.centralizer ({z} : Set G)).subtype
    core_le_ker := ?_
    agrees_on_core := ?_ }
  · intro x hx
    have hxMap : (x : G) ∈
        (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype := by
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hxKer : (x : G) ∈ rho.ker :=
      PrincipalBlockKernel.pPrimeCore_le_representation_ker_of_mem_block
        d hi rho hchar (hlocal hxMap)
    rw [MonoidHom.mem_ker] at hxKer ⊢
    exact hxKer
  · intro x _hx
    rw [hchar]
    rfl

/-- If the odd core of the involution centralizer maps into the global odd
core, the global principal-block kernel theorem already gives the desired
section identity. -/
theorem section_invariance_of_localCore_le_globalCore
    (d : PrincipalCongruenceBlockData G) {i : d.I} (hi : i ∈ d.block)
    (z v : G)
    (hlocal :
      (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype ≤
        pPrimeCore 2 G)
    (hv : v ∈
      (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype) :
    d.chi i (ConjClasses.mk (z * v)) = d.chi i (ConjClasses.mk z) := by
  exact PrincipalBlockKernel.character_mul_right_eq_of_mem_block
    d hi z v (hlocal hv)

/-- The odd core of an element centralizer maps into the global odd core in
a finite solvable group.  This specializes the existing centralizer-control
theorem from a cyclic `2`-subgroup to the singleton centralizer used by the
Z*-argument. -/
theorem localCore_le_globalCore_of_solvable
    (hsolv : Group.IsSolvable G) (z : G) (hzI : IsInvolution z) :
    (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype ≤
      pPrimeCore 2 G := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup G := Subgroup.zpowers z
  have hzOrder : orderOf z = 2 := orderOf_eq_two
    (by simpa [pow_two] using hzI.2) hzI.1
  have hRp : IsPGroup 2 R := by
    have hcard : Nat.card (Subgroup.zpowers z) = 2 ^ 1 := by
      rw [Nat.card_zpowers, hzOrder]
      norm_num
    exact IsPGroup.of_card (n := 1) (by simpa [R] using hcard)
  have hcentralizer :
      Subgroup.centralizer (R : Set G) =
        Subgroup.centralizer ({z} : Set G) := by
    change Subgroup.centralizer (Subgroup.zpowers z : Set G) =
      Subgroup.centralizer ({z} : Set G)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hlocal :=
    pPrimeCore_map_centralizer_le_pPrimeCore_of_solvable
      hsolv 2 R hRp
  rw [hcentralizer] at hlocal
  exact hlocal

/-- Principal-block section invariance for finite solvable groups. -/
theorem principalBlock_section_invariance_of_solvable
    (d : PrincipalCongruenceBlockData G) (hsolv : Group.IsSolvable G)
    {i : d.I} (hi : i ∈ d.block) (z : G) (hzI : IsInvolution z)
    (v : G)
    (hv : v ∈
      (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype) :
    d.chi i (ConjClasses.mk (z * v)) = d.chi i (ConjClasses.mk z) := by
  exact section_invariance_of_localCore_le_globalCore d hi z v
    (localCore_le_globalCore_of_solvable hsolv z hzI) hv


end Glauberman.ZStar.LocalBlockSection

