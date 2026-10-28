module
public import Theory.Representation.BinaryDuadModule.IncidenceRank
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Small involution displacement on quotients of the even duad module

A quotient whose kernel annihilates every line-complement vector has three
independent displacement vectors for each involution of S₆. Three even vectors
and three incidence functionals give a small matrix certificate for each of the
three cycle types. Conjugacy transports the bound to every involution.

The source consumer applies this to the annihilator layer in the G.5.3 flag,
excluding quotient dimensions 9, 10 and 14 when displacement is at most two.
The constant line of the five-dimensional cover is retained.
Source: Aschbacher--Smith, G.5.3, printed pp.344--345, and the whole-module
comparison in the proof of 13.8.33, printed p.967.
-/

public section
open Representation BinaryPermutation BinaryDuadModule
open Theory.SpecificGroups.SymmetricSix
open Representation.BinaryOffender.NaturalTensor
namespace BinaryDuadModule.SmallDisplacement

private def involution (i : Fin 3) : S6 :=
  ![Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5] i
private def target (i j : Fin 3) : Duad := ![![5,6,7],![6,5,7],![6,5,8]] i j
private def seedIndex (j : Fin 3) : Duad := ![1,2,3] j
private def testIndex (i j : Fin 3) : Syntheme := ![![3,4,5],![4,5,7],![4,5,7]] i j
private def seed (j : Fin 3) : core Duad :=
  ⟨Pi.single (seedIndex j) 1 + Pi.single 0 1, by
    simp [mem_core,Finset.sum_add_distrib,CharTwo.add_self_eq_zero]⟩
private def delta (i j : Fin 3) : core Duad :=
  ⟨Pi.single (target i j) 1 - Pi.single (seedIndex j) 1, by
    simp [mem_core,Finset.sum_sub_distrib]⟩
private theorem involution_seed (i j : Fin 3) : involution i • seedIndex j = target i j := by
  apply duadSet_injective
  rw [duadSet_smul]
  have cert : ∀ i j : Fin 3,
      (involution i) • duadSet (seedIndex j) = duadSet (target i j) := by decide +kernel
  exact cert i j
private theorem involution_zero (i : Fin 3) : involution i • (0 : Duad) = 0 := by
  apply duadSet_injective
  rw [duadSet_smul]
  have cert : ∀ i : Fin 3, (involution i) • duadSet (0 : Duad) = duadSet 0 := by decide +kernel
  exact cert i
private theorem point_single (g : S6) (d : Duad) :
    pointAction g (Pi.single d 1) = Pi.single (g • d) 1 := by
  ext a
  change (Pi.single d (1 : ZMod 2) : Full Duad) (g⁻¹ • a) = (Pi.single (g • d) (1 : ZMod 2) : Full Duad) a
  simp only [Pi.single_apply,inv_smul_eq_iff]
private theorem delta_eq (i j : Fin 3) :
    (delta i j).val = pointAction (involution i) (seed j).val - (seed j).val := by
  change Pi.single (target i j) 1 - Pi.single (seedIndex j) 1 =
    pointAction (involution i) (Pi.single (seedIndex j) 1 + Pi.single 0 1) -
      (Pi.single (seedIndex j) 1 + Pi.single 0 1)
  rw [map_add,point_single,point_single,involution_seed,involution_zero]
  abel
private def matrix (i j k : Fin 3) : ZMod 2 :=
  ![![![1,1,1],![1,0,0],![0,1,0]],
    ![![1,1,0],![0,0,1],![1,0,1]],
    ![![1,1,0],![0,0,1],![0,1,0]]] i j k
private theorem pairings (i j k : Fin 3) :
    (∑ d : Duad, (delta i j).val d * lineComplement (testIndex i k) d) = matrix i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide
private theorem detection (i : Fin 3) (v : Fin 3 → ZMod 2)
    (h : ∀ k : Fin 3, ∑ d : Duad,
      (∑ j : Fin 3, v j * (delta i j).val d) * lineComplement (testIndex i k) d = 0) : v = 0 := by
  have hm (k : Fin 3) : ∑ j : Fin 3, v j * matrix i j k = 0 := by
    have hh := h k
    simp_rw [Finset.sum_mul,mul_assoc] at hh
    rw [Finset.sum_comm] at hh
    simpa only [← Finset.mul_sum,pairings] using hh
  have cert : ∀ (i : Fin 3) (a b c : ZMod 2),
      (∀ k : Fin 3, a * matrix i 0 k + b * matrix i 1 k + c * matrix i 2 k = 0) →
        a = 0 ∧ b = 0 ∧ c = 0 := by decide +kernel
  have hh := cert i (v 0) (v 1) (v 2) (by simpa only [Fin.sum_univ_three] using hm)
  ext j
  fin_cases j
  · exact hh.1
  · exact hh.2.1
  · exact hh.2.2

/-- The symmetric action on the literal even duad core. -/
@[expose] noncomputable def symmetricCoreAction : Representation (ZMod 2) S6 (core Duad) :=
  (coreRepresentation Duad).comp (MulAction.toPermHom S6 Duad)

private theorem delta_eq_core (i j : Fin 3) :
    delta i j = symmetricCoreAction (involution i) (seed j) - seed j :=
  Subtype.ext (delta_eq i j)

variable {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]

private theorem representative_displacement
    (ρ : Representation (ZMod 2) S6 X)
    (f : symmetricCoreAction.IntertwiningMap ρ)
    (hk : ∀ v : core Duad, f v = 0 → ∀ s : Syntheme,
      ∑ d : Duad, v.val d * lineComplement s d = 0) (i : Fin 3) :
    3 ≤ operatorFixedCodim (ρ (involution i)) := by
  let D := Fintype.linearCombination (ZMod 2) (delta i)
  let F := f.toLinearMap.comp D
  have hi : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro v hv
    apply detection i v
    intro k
    have hh := hk (D v) hv (testIndex i k)
    change (∑ d : Duad, (∑ j : Fin 3, v j • delta i j).val d *
      lineComplement (testIndex i k) d) = 0 at hh
    simpa only [Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hh
  have hr : ∀ v, F v ∈ (ρ (involution i) - 1).range := by
    intro v
    refine ⟨f (∑ j : Fin 3, v j • seed j),?_⟩
    change ρ (involution i) (f (∑ j : Fin 3, v j • seed j)) -
      f (∑ j : Fin 3, v j • seed j) = f (∑ j : Fin 3, v j • delta i j)
    rw [← f.isIntertwining,← map_sub]
    congr 1
    simp only [map_sum,map_smul,delta_eq_core,smul_sub,Finset.sum_sub_distrib]
  let F' := F.codRestrict (ρ (involution i) - 1).range hr
  have hinj : Function.Injective F' := fun x y he => hi (congrArg Subtype.val he)
  have hb := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [operatorFixedCodim, Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,mul_one] using hb

private theorem involution_cases (g : S6) (hg : orderOf g = 2) :
    ∃ i : Fin 3, IsConj g (involution i) := by
  have hs : g ^ 2 = 1 := hg ▸ pow_orderOf_eq_one g
  have hc := Equiv.Perm.cycleType_of_pow_prime_eq_one hs
  have hn : g.cycleType.card ≠ 0 := by
    intro hz
    have he : g = 1 := Equiv.Perm.card_cycleType_eq_zero.mp hz
    simp [he] at hg
  have hb := g.sum_cycleType_le
  rw [hc,Multiset.sum_replicate] at hb
  have hd : g.cycleType.card = 1 ∨ g.cycleType.card = 2 ∨ g.cycleType.card = 3 := by
    simp only [Fintype.card_fin,smul_eq_mul] at hb
    omega
  have cert : ∀ i : Fin 3, (involution i).cycleType = Multiset.replicate (i.val+1) 2 := by decide +kernel
  rcases hd with h | h | h
  · exact ⟨0,Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [cert,hc,h]; rfl)⟩
  · exact ⟨1,Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [cert,hc,h]; rfl)⟩
  · exact ⟨2,Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [cert,hc,h]; rfl)⟩

/-- If the kernel annihilates every line complement, every involution moves
at least three dimensions of the quotient. The three certificates each use
only three even vectors and three line-complement functionals. -/
theorem involution_displacement_ge_three
    (ρ : Representation (ZMod 2) S6 X)
    (f : symmetricCoreAction.IntertwiningMap ρ)
    (hk : ∀ v : core Duad, f v = 0 → ∀ s : Syntheme,
      ∑ d : Duad, v.val d * lineComplement s d = 0)
    (g : S6) (hg : orderOf g = 2) : 3 ≤ operatorFixedCodim (ρ g) := by
  obtain ⟨i,hi⟩ := involution_cases g hg
  obtain ⟨a,ha⟩ := isConj_iff.mp hi
  have he := operatorFixedCodim_eq_of_equiv (ρ g) (ρ (involution i))
    (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a)) (fun v => by
      change ρ a (ρ g v) = ρ (involution i) (ρ a v)
      rw [← Module.End.mul_apply,←map_mul,← Module.End.mul_apply,←map_mul]
      rw [mul_inv_eq_iff_eq_mul.mp ha])
  rw [he]
  exact representative_displacement ρ f hk i

end BinaryDuadModule.SmallDisplacement
