module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.Model
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.ProjectiveComparison.ActionBridge
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.ProjectiveComparison.LiftContract
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.ProjectiveComparison.Generators
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.ProjectiveComparison.ConcreteLifts

/-!
# Comparing the actual Held 2A orbit image with matrix PSL₃(4)

Two explicit projective matrices generate PSL₃(4) and act on the 21 labelled
points. Their certified Held lifts lie in the literal derived subgroup, so
projective transitivity puts every label in its actual orbit. The subgroup of
pairs of agreeing actors maps onto matrix PSL and injects into the orbit image.
The centralizer and orbit-kernel orders bound that image by 40320. Perfectness
therefore forces the agreement subgroup to project onto the whole image.
Orbit transitivity makes the point embedding a bijection, and faithfulness
then yields the actual group isomorphism. The final field transport is a proved
ring equivalence to `GaloisField 2 2`.

The concrete lift certificate is discharged by `generator_lifts` from
`ConcreteLifts`, using checked Held words and their actual point actions.
The comparison remains conditional only on
perfectness of the derived subgroup and the centralizer and orbit-kernel
orders. Kernel centrality is not needed for this comparison step.

Source: GLS3 Table 5.3p (2A row) and the perfect-cover interpretation on
printed pp.260–261. The unconditional Held cover remains with `TwoA`'s owner.
-/

@[expose] public section
namespace Held.InvolutionFixedData.TwoA.ProjectiveComparison

/-- An actual comparison of the faithful orbit image with the canonical matrix group,
conditional on the finite Held generator-action certificate and three order/perfectness inputs. -/
theorem nonempty_equiv_of_generator_lifts [Group.IsPerfect derived]
    (hc : Nat.card centralizer = 161280) (hk : Nat.card orbitKernel = 4)
    (hl : GeneratorLifts) : Nonempty (orbitImage ≃* Matrix.PSL3Four.PSL) := by
  have hgen := projective_pair_generates
  have hlifts := label_generator_lifts hl
  have hmem (p : PG) : label p ∈ MulAction.orbit derived (25 : Fin 2058) := by
    have h := labels_mem_orbit label _ hgen hlifts (pointEquiv 0) p
    simpa only [label_pointEquiv, pointLabel_zero] using h
  let f : PG → PointOrbit := fun p => ⟨label p, hmem p⟩
  have hf : Function.Injective f := fun p q hpq =>
    label_injective (congrArg Subtype.val hpq)
  let : Group.IsPerfect orbitImage := Group.IsPerfect.range orbitAction
  let : MulAction.IsPretransitive orbitImage PointOrbit := ⟨by
    intro u v
    obtain ⟨d, hd⟩ := MulAction.exists_smul_eq derived u v
    exact ⟨orbitAction.rangeRestrict d, hd⟩⟩
  have hcard : Nat.card orbitImage ≤ 2 * Nat.card PSL := by
    have h := orbitKernel.card_mul_index
    rw [Subgroup.index_ker, hk] at h
    change 4 * Nat.card orbitImage = Nat.card derived at h
    have hb := derived.card_le_card_group
    rw [hc] at hb
    have hm : Nat.card PSL = 20160 :=
      (Nat.card_congr modelEquiv.toEquiv).trans Matrix.PSL3Four.card_PSL
    rw [hm]
    omega
  have hlifts' : ∀ s ∈ ({projectiveA, projectiveB} : Set PSL),
      ∃ d : orbitImage, ∀ p : PG, d • f p = f (s • p) := by
    intro s hs
    obtain ⟨d, hd⟩ := hlifts s hs
    refine ⟨orbitAction.rangeRestrict d, ?_⟩
    intro p
    apply Subtype.ext
    exact hd p
  exact ⟨(equivOfGeneratorLifts f hf hcard _ hgen hlifts').trans modelEquiv⟩

/-- The literal Held 2A derived-subgroup orbit image is matrix PSL₃(4), using
the certified actions of the two concrete Held words. The only remaining
inputs are derived perfectness and the two finite cardinality facts. -/
theorem nonempty_equiv [Group.IsPerfect derived]
    (hc : Nat.card centralizer = 161280) (hk : Nat.card orbitKernel = 4) :
    Nonempty (orbitImage ≃* Matrix.PSL3Four.PSL) :=
  nonempty_equiv_of_generator_lifts hc hk generator_lifts

end Held.InvolutionFixedData.TwoA.ProjectiveComparison
