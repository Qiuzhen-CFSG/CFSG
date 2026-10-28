module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreeSylowContainment.RootCapture.Descent
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreeSylowContainment.RootCapture.Generation

/-!
# A non-Borel Ree normalizer word captures a rank-one seed

A simple descent of the inverse Weyl element occurs on an entire exceptional
node orbit. It carries the corresponding complete negative fixed block into
the conjugate of the positive subgroup. The fixed Levi–radical factorization
and signed fixed-block generation then put the actual root-defined seed in
the join of the two positive subgroups. The Suzuki side retains all four
positive B₂ roots. Conjugation is `x ↦ n * x * n⁻¹` throughout.

This proves the geometric input to the solvable Sylow-overgroup reduction.
It uses neither simplicity nor seed nonsolvability. It does not itself assert
the source Borel containment, which also requires the Levi quotients.

Source: GLS3 2.3.4–8 and 2.6.2–5, `refs/KGroup/GLS3/chapter2.tex`,
underlying Aschbacher–Smith, Proposition 1.3.4, printed p.511, and
F.1.12(I)(5), printed p.263 of `refs/quasithin.pdf`.
-/

public section
namespace ReeF4.Parabolics.ThreeSylowContainment.RootCapture
open Subgroup LargeLocalSeeds SectionGeometry.BNPair
open LocalBlockInput.PairRigidity

/-- Generation of the literal fixed seed by the positive subgroup and its
complete negative relative block, including its fixed Levi torus. -/
theorem seed_le_unipotent_sup_negativeBlock {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    seed m s ≤ unipotent m ⊔ (splitSimpleBlock m s false).comap (toSplitGroup m) := by
  let d := canonicalLocalBlockInput m
  let H := unipotent m ⊔ (splitSimpleBlock m s false).comap (toSplitGroup m)
  have hU : standardUnipotent d ≤ H.comap d.modelEquiv.toMonoidHom := by
    intro u hu
    apply mem_sup_left
    change toSplitGroup m (d.modelEquiv u) ∈ splitUnipotent m
    rw [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe]
    exact hu
  have hN : simpleBlock d s false ≤ H.comap d.modelEquiv.toMonoidHom := by
    intro u hu
    apply mem_sup_right
    change toSplitGroup m (d.modelEquiv u) ∈ splitSimpleBlock m s false
    rw [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe]
    exact hu
  intro x hx
  have hx' : d.modelEquiv.symm x ∈ standardSeed d s := by
    change (d.modelEquiv.symm x).val ∈ splitSeed m s
    rw [modelEquiv_symm_coe]
    simpa only [seed, mem_comap, toSplitGroup_apply] using hx
  have hh := (sup_le hU hN) (fixedSeed_le_positive_sup_negative hm d s hx')
  change d.modelEquiv (d.modelEquiv.symm x) ∈ H at hh
  simpa only [MulEquiv.apply_symm_apply] using hh

/-- A word outside the root Borel generates one of the two root-defined
fixed seeds together with the positive subgroup and its conjugate. -/
theorem exists_seed_le_sup_conjugate {m : ℕ} (hm : 1 ≤ m) (n : Model m)
    (hn : n ∈ normalizerWords m) (hnb : n ∉ borel m) :
    ∃ s : Side, seed m s ≤
      unipotent m ⊔ (unipotent m).map (MulAut.conj n).toMonoidHom := by
  obtain ⟨s, hs⟩ := exists_negativeBlock_le_conjugate m hn hnb
  exact ⟨s, (seed_le_unipotent_sup_negativeBlock hm s).trans (sup_le_sup_left hs _)⟩

end ReeF4.Parabolics.ThreeSylowContainment.RootCapture
