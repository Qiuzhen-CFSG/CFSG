module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionCentralizerSetup
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionWords
public import Theory.GroupTheory.DoubleCosetGeneratorRecovery

/-!
# A generation criterion for the concrete Lyons involution subgroup

The first output of `LyG1-max4W1` is `ab`, so an overgroup of the specified
subgroup containing `a` contains both ambient generators. Double-coset coverage
and word certificates recovering `a` from the outside representatives therefore
prove maximality. The commutation and transporter certificates prove properness:
if the subgroup were the whole group, its proposed central involution would be
central, and its conjugate `a` would contradict the certified noncommutativity.

The commutation and transporter identities are checked in
`Atlas111InvolutionWords`, which also proves properness unconditionally.
The final theorem here is conditional on coverage and recovery certificates;
it does not assert that such certificates have been constructed. No ambient
simplicity, order recognition, or abstract double-cover identification is used.

Source for the subgroup and transporter words: ATLAS of Finite Group
Representations, Lyons entry and `LyG1-max4W1`; the original program and its
attribution are preserved in `Atlas111InvolutionSource/`.
-/

namespace Lyons.SimplicityCertificate

/-- The one missing ambient generator suffices in every overgroup of the
concrete subgroup, since `ab` is already in it. -/
public theorem involutionLocal_overgroup_eq_top_of_generatorA_mem
    (K : Subgroup LyonsGroup) (hHK : involutionLocalSubgroup ≤ K)
    (ha : generatorA ∈ K) : K = ⊤ := by
  have hab : generatorA * generatorB ∈ K := by
    rw [← involutionLocalA_eq]
    exact hHK involutionLocalA_mem
  have hb : generatorB ∈ K := by
    simpa only [inv_mul_cancel_left] using K.mul_mem (K.inv_mem ha) hab
  apply top_unique
  rw [← OrderCertificate.closure_generators]
  apply (Subgroup.closure_le K).mpr
  intro x hx
  rcases hx with rfl | hx
  · exact ha
  · rcases hx with rfl
    exact hb

/-- The two finite word certificates imply properness without local-order or
local-identification hypotheses. -/
public theorem involutionLocalSubgroup_ne_top_of_word_certificates
    (hcomm : involutionLocalB * involutionLocalT = involutionLocalT * involutionLocalB)
    (htransport : involutionTransporter⁻¹ * involutionLocalT * involutionTransporter =
      generatorA) : involutionLocalSubgroup ≠ ⊤ := by
  intro htop
  have hc (g : LyonsGroup) : g * involutionLocalT = involutionLocalT * g := by
    apply Subgroup.mem_centralizer_singleton_iff.mp
    apply involutionLocalSubgroup_le_centralizer hcomm
    rw [htop]
    trivial
  have ht : involutionLocalT = generatorA := by
    rw [mul_assoc, ← hc involutionTransporter, inv_mul_cancel_left] at htransport
    exact htransport
  apply generators_not_commute
  exact (ht ▸ hc generatorB).symm

/-- Assemble maximality from actual word identities, double-coset coverage,
and certificates recovering `a` from each outside representative. -/
public theorem involutionLocalSubgroup_isCoatom_of_doubleCosets
    (hcomm : involutionLocalB * involutionLocalT = involutionLocalT * involutionLocalB)
    (htransport : involutionTransporter⁻¹ * involutionLocalT * involutionTransporter =
      generatorA)
    {ι : Type*} (r : ι → LyonsGroup)
    (hcover : ∀ g : LyonsGroup, g ∉ involutionLocalSubgroup →
      ∃ i, ∃ h ∈ involutionLocalSubgroup, ∃ k ∈ involutionLocalSubgroup,
        g = h * r i * k)
    (hrecover : ∀ i, r i ∉ involutionLocalSubgroup →
      generatorA ∈ Subgroup.closure (insert (r i) (involutionLocalSubgroup : Set LyonsGroup))) :
    IsCoatom involutionLocalSubgroup :=
  Subgroup.isCoatom_of_doubleCoset_generator_recovery involutionLocalSubgroup generatorA
    (involutionLocalSubgroup_ne_top_of_word_certificates hcomm htransport)
    involutionLocal_overgroup_eq_top_of_generatorA_mem r hcover hrecover

/-- With the concrete matrix word identities discharged, only the exhaustive
double-coset cover and the recovery words remain to establish maximality. -/
public theorem involutionLocalSubgroup_isCoatom_of_doubleCoset_certificates
    {ι : Type*} (r : ι → LyonsGroup)
    (hcover : ∀ g : LyonsGroup, g ∉ involutionLocalSubgroup →
      ∃ i, ∃ h ∈ involutionLocalSubgroup, ∃ k ∈ involutionLocalSubgroup,
        g = h * r i * k)
    (hrecover : ∀ i, r i ∉ involutionLocalSubgroup →
      generatorA ∈ Subgroup.closure (insert (r i) (involutionLocalSubgroup : Set LyonsGroup))) :
    IsCoatom involutionLocalSubgroup :=
  involutionLocalSubgroup_isCoatom_of_doubleCosets involutionLocalB_commutes
    involutionTransporter_conjugates r hcover hrecover

end Lyons.SimplicityCertificate
