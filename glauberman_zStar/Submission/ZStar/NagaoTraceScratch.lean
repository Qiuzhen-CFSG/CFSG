import Submission.FeitThompson.Representation.CharacterValues

/-!
# Order-two specialization of the finite-order commuting trace congruence

This is the exact linear-algebra template potentially usable in the Nagao
trace step.  It proves congruence modulo `2 = 1 - (-1)`; it does not assert
the projectivity/vertex input needed to turn that congruence into vanishing.
-/

noncomputable section

namespace Submission.ZStar

namespace NagaoTraceScratch

/-- If `f` is an involution and commutes with a finite-order endomorphism
`T`, then `tr(fT)` and `tr(T)` are congruent modulo `2` in the chosen
cyclotomic order. -/
theorem involution_commuting_trace_mul_congruent
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {η : ℂ} {N M : ℕ}
    (hη : IsPrimitiveRoot η M) (hM : M ≠ 0) (hNM : N ∣ M)
    {f T : Module.End ℂ V} (hN : N ≠ 0)
    (hf : f ^ 2 = 1) (hTpow : T ^ N = 1) (hcomm : f * T = T * f) :
    ∃ hmul : LinearMap.trace ℂ V (f * T) ∈
        Representation.cyclotomicOrder η,
      ∃ hTmem : LinearMap.trace ℂ V T ∈
          Representation.cyclotomicOrder η,
        Representation.CongruentModOneSub η (-1)
          (LinearMap.trace ℂ V (f * T)) (LinearMap.trace ℂ V T)
          ((Representation.cyclotomicOrder η).neg_mem
            (Representation.cyclotomicOrder η).one_mem)
          hmul hTmem := by
  have hneg : IsPrimitiveRoot (-1 : ℂ) 2 :=
    IsPrimitiveRoot.neg_one 0 (by omega)
  have hnegMem : (-1 : ℂ) ∈ Representation.cyclotomicOrder η :=
    (Representation.cyclotomicOrder η).neg_mem
      (Representation.cyclotomicOrder η).one_mem
  exact Representation.finite_order_commuting_trace_mul_congruent
    (η := η) (ξ := (-1 : ℂ)) (p := 2) (N := N) (M := M)
    hneg (by omega) hη hM hNM hnegMem hN hf hTpow hcomm

end NagaoTraceScratch

end Submission.ZStar
