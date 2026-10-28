module

public import CFSG.Quasithin.ChapterG.Section09.Setup
public import Theory.Representation.Triality.SevenPlaneDegree

/-!
# The seven-plane exclusion of the binary triality endpoint in G.9

Restrict the original faithful action to its component and transport it along
the actual triality model isomorphism. A marked seven-plane in that genuine
carrier gives degree at least 24, whereas the original G.9 hypothesis gives
degree at most 2*(m+1). Thus m <= 10 is already sufficient for exclusion.

Source: Aschbacher--Smith, G.9.3, combined manuscript (1 March 2004), printed
p.356 (PDF p.367), `refs/quasithin.pdf`. The concrete seven-plane construction
discharges the subgroup premise in the final two exclusion theorems.
No irreducibility, model simplicity, or model perfectness premise is added.
The actor-rank bound remains with the source assembly owner.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {rho : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

/-- The actual G.9 component is excluded by a seven-plane in its triality model. -/
theorem not_triality_two_of_sevenPlane_data
    (d : QuaternionSevenPlane.Data
      (Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one))
    (h : ComponentHypothesis K rho A L L m)
    (model : Triality.Standard.IsTrialityGroupAt 2 L) (hm : m ≤ 10) : False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_two_iff L).mp model
  have hd := Triality.SevenPlaneDegree.finrank_ge_of_data d
    ((rho.comp L.subtype).comp e.symm.toMonoidHom)
    ((h.faithful.comp L.subtype_injective).comp e.symm.injective)
  have hu := h.degree_le
  omega

/-- Specialization to the actor bound of `triality_two_endpoint`. -/
theorem not_triality_two_endpoint_of_sevenPlane_data
    (d : QuaternionSevenPlane.Data
      (Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one))
    (h : ComponentHypothesis K rho A L L m)
    (model : Triality.Standard.IsTrialityGroupAt 2 L) (hm : m ≤ 5) : False :=
  not_triality_two_of_sevenPlane_data d h model (by omega)

/-- The constructed seven-plane excludes the actual G.9 triality component
whenever the original actor has rank at most ten. -/
theorem not_triality_two_of_sevenPlane
    (h : ComponentHypothesis K rho A L L m)
    (model : Triality.Standard.IsTrialityGroupAt 2 L) (hm : m ≤ 10) : False :=
  not_triality_two_of_sevenPlane_data Triality.Standard.binarySevenPlane h model hm

/-- Exclusion of the degree-twelve endpoint isolated by `triality_two_endpoint`,
with the subgroup-construction premise fully discharged. -/
theorem not_triality_two_endpoint_of_sevenPlane
    (h : ComponentHypothesis K rho A L L m)
    (model : Triality.Standard.IsTrialityGroupAt 2 L) (hm : m ≤ 5) : False :=
  not_triality_two_of_sevenPlane h model (by omega)

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
