module

public import Theory.Representation.BinaryPermutation
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic

/-!
# Alternating bilinear maps from the five-point core to itself

An A₅-equivariant alternating bilinear map on the binary deleted-permutation
module is zero. Four explicit even permutations constrain its value on the
first two standard core vectors. A finite check on the thirty-two binary
five-tuples makes that value zero. Even permutations fixing the fifth point
transport this to every distinct basis pair, and bilinearity finishes.

Both source and target are the deleted-permutation (Steinberg) module. The
statement does not concern the distinct four-dimensional restriction of the
natural SL₂(4) module, whose exterior square does map nontrivially here.
-/

public section
namespace BinaryPermutation.FiveAlternatingBilinear
private abbrev C := core (Fin 5)
private abbrev act (g : alternatingGroup (Fin 5)) := coreRepresentation (Fin 5) g.val

private def basisVector (i : Fin 4) : C :=
  ⟨Pi.single i.castSucc 1 + Pi.single 4 1, by
    simp [mem_core,Finset.sum_add_distrib,show (1 : ZMod 2) + 1 = 0 from rfl]⟩

private def r : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 4, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def t : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def g : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def p : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩

private theorem basis_actions :
    act r (basisVector 0) = basisVector 0 + basisVector 1 ∧
    act r (basisVector 1) = basisVector 0 ∧
    act t (basisVector 0) = basisVector 1 ∧
    act t (basisVector 1) = basisVector 0 ∧
    act g (basisVector 0) = basisVector 1 ∧
    act g (basisVector 1) = basisVector 2 ∧
    act (g^2) (basisVector 0) = basisVector 2 ∧
    act (g^2) (basisVector 1) = basisVector 0 ∧
    act p (basisVector 0) = basisVector 0 + basisVector 1 ∧
    act p (basisVector 1) = basisVector 0 + basisVector 2 := by decide +kernel

private theorem value_inspection : ∀ c : Full (Fin 5),
    (∑ i, c i) = 0 →
    representation (Fin 5) r.val c = c →
    representation (Fin 5) t.val c = c →
    representation (Fin 5) p.val c =
      c + representation (Fin 5) g.val c + representation (Fin 5) (g^2).val c →
    c = 0 := by decide +kernel

private theorem pair_orbit : ∀ i j : Fin 4, i ≠ j →
    ∃ a : alternatingGroup (Fin 5),
      act a (basisVector 0) = basisVector i ∧
      act a (basisVector 1) = basisVector j := by decide +kernel

private theorem expansion (x : C) :
    (∑ i : Fin 4, x.val i.castSucc • basisVector i) = x := by
  have hc : ∀ v : Full (Fin 5), (∑ i, v i) = 0 →
      (∑ i : Fin 4, v i.castSucc • (basisVector i).val) = v := by decide +kernel
  apply Subtype.ext
  exact hc x.val x.property

/-- An alternating bilinear map between the literal five-point binary cores,
equivariant for the same A₅ actor, vanishes. -/
theorem eq_zero
    (b : core (Fin 5) →ₗ[ZMod 2] core (Fin 5) →ₗ[ZMod 2] core (Fin 5))
    (halt : ∀ x, b x x = 0)
    (heq : ∀ (a : alternatingGroup (Fin 5)) x y,
      b (coreRepresentation (Fin 5) a.val x) (coreRepresentation (Fin 5) a.val y) =
        coreRepresentation (Fin 5) a.val (b x y)) : b = 0 := by
  have hsym (x y : C) : b x y = b y x := by
    have hh := halt (x+y)
    simp only [map_add,LinearMap.add_apply,halt,zero_add,add_zero] at hh
    apply Subtype.ext
    ext i
    exact (CharTwo.add_eq_zero.mp (congrArg (fun v : C => v.val i) hh)).symm
  obtain ⟨hr0,hr1,ht0,ht1,hg0,hg1,hg20,hg21,hp0,hp1⟩ := basis_actions
  let c := b (basisVector 0) (basisVector 1)
  have hrc : act r c = c := by
    have hh := heq r (basisVector 0) (basisVector 1)
    rw [hr0,hr1,map_add,LinearMap.add_apply,halt,zero_add,hsym] at hh
    exact hh.symm
  have htc : act t c = c := by
    have hh := heq t (basisVector 0) (basisVector 1)
    rw [ht0,ht1,hsym] at hh
    exact hh.symm
  have h12 : b (basisVector 1) (basisVector 2) = act g c := by
    simpa only [hg0,hg1] using heq g (basisVector 0) (basisVector 1)
  have h02 : b (basisVector 0) (basisVector 2) = act (g^2) c := by
    have hh := heq (g^2) (basisVector 0) (basisVector 1)
    rw [hg20,hg21,hsym] at hh
    exact hh
  have hpc : act p c = c + act g c + act (g^2) c := by
    have hh := heq p (basisVector 0) (basisVector 1)
    rw [hp0,hp1] at hh
    simp only [map_add,LinearMap.add_apply,halt,zero_add] at hh
    rw [h02,hsym (basisVector 1) (basisVector 0),h12] at hh
    calc
      act p c = _ := hh.symm
      _ = c + act g c + act (g^2) c := by dsimp [c]; abel
  have hc : c = 0 := by
    apply Subtype.ext
    exact value_inspection c.val c.property (congrArg Subtype.val hrc)
      (congrArg Subtype.val htc) (congrArg Subtype.val hpc)
  have hb (i j : Fin 4) : b (basisVector i) (basisVector j) = 0 := by
    by_cases hij : i = j
    · subst j
      exact halt _
    obtain ⟨a,ha0,ha1⟩ := pair_orbit i j hij
    have hh := heq a (basisVector 0) (basisVector 1)
    change b (act a (basisVector 0)) (act a (basisVector 1)) = act a c at hh
    rwa [ha0,ha1,hc,map_zero] at hh
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [←expansion x,←expansion y]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,hb,smul_zero,
    Finset.sum_const_zero,LinearMap.zero_apply]

end BinaryPermutation.FiveAlternatingBilinear
