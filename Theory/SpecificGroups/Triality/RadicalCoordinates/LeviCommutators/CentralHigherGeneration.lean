module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.RootArithmetic
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.CentralHigherGeneration.Exchange

/-!
# Generation of the remaining central-radical folded root group

A subgroup of the genuine triality carrier containing short orbits 0 and 1
and long orbits 1 and 2 contains short orbit 2. The checked folded exchange
first supplies every leading coefficient s F(t) + F(s) t after cancellation
of its two fixed singleton corrections. Every cubic scalar is a sum of two
such coefficients, so additivity supplies the whole remaining root group.
No normalization hypothesis is required. This is the independent `hhigher`
contract of the Levi-commutator assembly; torus motion remains with its owner.

Source: GLS3 2.4.5(b)(4) and §2.6 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith F.1.12(II), printed pp.263–264 (`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.RadicalCoordinates.LeviCommutators

/-- Cancel the two known singleton corrections from the folded exchange. -/
theorem short_higherCoefficient_mem (P : Parameters) (hp : P.prime = 2)
    (H : Subgroup (Carrier P))
    (h0 : ∀ t, short P hp 0 t ∈ H) (h1 : ∀ t, short P hp 1 t ∈ H)
    (hl1 : ∀ z, long P hp 1 z ∈ H) (hl2 : ∀ z, long P hp 2 z ∈ H)
    (s t : ExtensionField P) : short P hp 2 (higherCoefficient P s t) ∈ H := by
  have he := short_zero_one_exchange P hp s t
  have hm := H.mul_mem (h0 s) (h1 t)
  rw [he] at hm
  exact (H.mul_mem_cancel_left (H.mul_mem (h1 t) (h0 s))).mp
    ((H.mul_mem_cancel_right (hl1 _)).mp ((H.mul_mem_cancel_right (hl2 _)).mp hm))

/-- The first two short groups and last two long groups generate the third
short group. The scalar argument also covers the binary base field. -/
theorem short_two_mem_of_zero_one (P : Parameters) (hp : P.prime = 2)
    (H : Subgroup (Carrier P))
    (h0 : ∀ t, short P hp 0 t ∈ H) (h1 : ∀ t, short P hp 1 t ∈ H)
    (hl1 : ∀ z, long P hp 1 z ∈ H) (hl2 : ∀ z, long P hp 2 z ∈ H)
    (v : ExtensionField P) : short P hp 2 v ∈ H := by
  obtain ⟨s, t, u, rfl⟩ := exists_sum_higherCoefficient P hp v
  rw [short_add]
  exact H.mul_mem (short_higherCoefficient_mem P hp H h0 h1 hl1 hl2 s t)
    (short_higherCoefficient_mem P hp H h0 h1 hl1 hl2 1 u)

/-- The precise `hhigher` input to `central_le_commutator_of_motion` for q > 2.
The four membership hypotheses are discharged by the parent's torus motion. -/
theorem central_higher_generation (P : Parameters) (hp : P.prime = 2) (_hq : 2 < P.q)
    (H : Subgroup (Carrier P))
    (h0 : ∀ t, short P hp 0 t ∈ H) (h1 : ∀ t, short P hp 1 t ∈ H)
    (hl1 : ∀ z, long P hp 1 z ∈ H) (hl2 : ∀ z, long P hp 2 z ∈ H)
    (v : ExtensionField P) : short P hp 2 v ∈ H :=
  short_two_mem_of_zero_one P hp H h0 h1 hl1 hl2 v

end Triality.Standard.RadicalCoordinates.LeviCommutators
