module

public import Theory.Alternating.OddCentralCovers

/-!
# Quasisimple groups with an alternating-eight quotient and trivial two-core

A surjection from a quasisimple group onto A₈ has the whole center as its
kernel. The nonexceptional alternating multiplier bounds that center by two.
It is therefore a normal two-subgroup, and a trivial two-core kills it.
The original surjection is injective; no replacement marking is chosen.

Source: GLS3, Theorem 5.2.3; Aschbacher–Smith I.1.3, p.407.
Used to recover L/O₂(L) from the faithful actor in 12.2.16, p.800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace AlternatingEightQuasisimple
variable {A : Type*} [Group A] [Finite A] [IsQuasisimple A]

/-- The original surjection to A₈ is an isomorphism when the two-core vanishes. -/
theorem surjection_injective (hcore : pCore 2 A = ⊥)
    (f : A →* alternatingGroup (Fin 8)) (hf : Function.Surjective f) :
    Function.Injective f := by
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let c : Covering A (alternatingGroup (Fin 8)) := { toMonoidHom := f, surjective := hf }
  have hk : f.ker = center A := c.ker_eq_center_of_isSimple
  let e : (A ⧸ center A) ≃* alternatingGroup (Fin 8) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hd := GLS3.Chapter5.OddCentralCovers.center_card_dvd_two_of_nonexceptional
    8 (by decide) (by decide) (by decide) e
  have hp : IsPGroup 2 (center A) := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with h | h
    · exact IsPGroup.of_card (n := 0) (by simpa using h)
    · exact IsPGroup.of_card (n := 1) (by simpa using h)
  have hz : center A ≤ pCore 2 A := le_sSup ⟨inferInstance,hp⟩
  apply f.ker_eq_bot_iff.mp
  exact hk.trans (bot_unique (hz.trans_eq hcore))
end AlternatingEightQuasisimple

