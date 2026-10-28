module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.CenterPreimage
public import Theory.GroupTheory.SolvableRadical.Transport
public import FeitThompson.FinalTheorem

/-!
# The actual odd-core quotient in the minimal counterexample

The center preimage is both the Fitting subgroup and the solvable radical.
Its odd order then identifies it with the odd core. Consequently the actual
odd-core quotient is the center quotient of the semisimple section and has
trivial center. These facts precede the exclusion of the other Sylow primes;
they do not assume that the Fitting subgroup is already a p-group.

Source: Aschbacher–Smith A.2.11–12, printed pp.35–36, in particular the
Z-star obstruction in the equality case of A.1.28.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.center_preimage_eq_solvableRadical
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f) :
    (center S).comap f = solvableRadical G := by
  apply le_antisymm
  · let := h.center_preimage_isNilpotent ih f hf
    exact le_solvableRadical _ inferInstance inferInstance
  · apply map_le_iff_le_comap.mp
    rw [← solvableRadical_eq_center_of_componentLayer_eq_top h.2.2.2.1]
    exact map_solvableRadical_le_of_surjective f hf

theorem CounterexampleToTheoremA.center_preimage_eq_oddCore
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f) :
    (center S).comap f = pPrimeCore 2 G := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance,
      Nat.coprime_two_left.mpr (h.center_preimage_odd_card ih f hf)⟩
  · rw [h.center_preimage_eq_solvableRadical ih f hf]
    let : Group.IsSolvable (pPrimeCore 2 G) := odd_order_theorem _
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    exact le_solvableRadical _ inferInstance inferInstance

/-- The equivalence uses the original epimorphism onto the offending section. -/
noncomputable def CounterexampleToTheoremA.oddCoreQuotientEquiv
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f) :
    G ⧸ pPrimeCore 2 G ≃* S ⧸ center S := by
  let q := (QuotientGroup.mk' (center S)).comp f
  have hk : q.ker = pPrimeCore 2 G := by
    rw [show q = (QuotientGroup.mk' (center S)).comp f from rfl,
      ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact h.center_preimage_eq_oddCore ih f hf
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q
      ((QuotientGroup.mk'_surjective _).comp hf))

/-- The Z-star equality-case premise of A.1.28 is discharged before the
prime-core identity of A.2.11. -/
theorem CounterexampleToTheoremA.center_oddCore_quotient_eq_bot
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G) :
    center (G ⧸ pPrimeCore 2 G) = ⊥ := by
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  let e := h.oddCoreQuotientEquiv ih f hf
  let := h.2.2.2.1.isPerfect
  apply le_bot_iff.mp
  intro x hx
  apply e.injective
  rw [map_one]
  apply mem_bot.mp
  rw [← Group.IsPerfect.center_quotient_center_eq_bot (G := S)]
  apply mem_center_iff.mpr
  intro y
  obtain ⟨y, rfl⟩ := e.surjective y
  simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)

end CFSG.Quasithin.ChapterA.Section02
