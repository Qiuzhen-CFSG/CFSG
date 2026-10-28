module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Passage
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusData
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.OrbitCounting

/-!
# Reduction of the ambient D4 count to twisted torus kernels

Each odd-order graph-field fixed point is semisimple. A torus representative
of its ambient conjugacy class therefore gives a stable Weyl orbit. Twisted
orbit counting bounds the number of these classes by the total number of
solutions of `σ(t) = w(t)`, divided by the Weyl-group order.

The transporter count is proved here without assuming that all stable
ambient classes contain fixed points. The torus data and the finite kernel
calculation remain explicit inputs; this module does not yet assert the
unconditional ambient bound.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 14.7--14.9, in the
D4 graph-field situation of §§11--13.
-/

public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound

open Theory.AlgebraicGroup AmbientCount

universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The torus/Weyl passage for the actual ambient image. Every counted class
contributes a full Weyl-group order to the twisted-kernel total. Finiteness
of every kernel is required, so no infinite `Nat.card` convention is used. -/
theorem ambient_card_mul_weyl_le_kernelTotal
    (S : Geometry K) (n : ℕ) (hn : 0 < n) (D : TorusData S n)
    (hfin : ∀ w : Weyl, Finite (TwistedKernel D w)) :
    Nat.card (fixedAmbientOddClasses S n) * Nat.card Weyl ≤ kernelTotal D := by
  let := D.action
  let f : Variety.Point S.torus.carrierVariety → ConjClasses (Variety.Point K) :=
    fun t => ConjClasses.mk (S.torus.includePoint t)
  have hf : ∀ t u, f t = f u ↔ ∃ w : Weyl, w • t = u := by
    intro t u
    exact ConjClasses.mk_eq_mk_iff_isConj.trans (D.conjugate_iff t u)
  have hmap : ∀ t, f (D.map t) = ConjClasses.map (graphFieldEnd S n) (f t) := by
    intro t
    exact congrArg ConjClasses.mk (D.map_ambient t)
  have himage : fixedAmbientOddClasses S n ⊆ Set.range f := by
    intro c hc
    obtain ⟨x, hx, hxc⟩ := (mem_fixedAmbientOddClasses_spec S n hn hc).1
    obtain ⟨t, ht⟩ := D.semisimple_conjugate x hx
    refine ⟨t, ?_⟩
    exact (ConjClasses.mk_eq_mk_iff_isConj.mpr ht).symm.trans hxc
  have hfixed : ∀ c ∈ fixedAmbientOddClasses S n,
      ConjClasses.map (graphFieldEnd S n) c = c :=
    fun _ hc => (mem_fixedAmbientOddClasses_spec S n hn hc).2
  exact (TwistedCount.finite_and_card_mul_le f hf D.map
    (ConjClasses.map (graphFieldEnd S n)) hmap
    (fixedAmbientOddClasses S n) himage hfixed hfin).2

/-- Conditional assembly of Steinberg's ambient upper bound. Constructing
`D` and proving the finite twisted-kernel total are separate geometric and
arithmetic obligations, retained as explicit premises here. -/
theorem ambientClassBound_of_torusData
    (S : Geometry K) (n : ℕ) (hn : 0 < n) (D : TorusData S n)
    (hfin : ∀ w : Weyl, Finite (TwistedKernel D w))
    (hcount : kernelTotal D = (2 ^ n) ^ 4 * Nat.card Weyl) :
    AmbientClassBound S n := by
  have hmul := ambient_card_mul_weyl_le_kernelTotal S n hn D hfin
  rw [hcount] at hmul
  exact Nat.le_of_mul_le_mul_right hmul (Nat.card_pos (α := Weyl))

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
