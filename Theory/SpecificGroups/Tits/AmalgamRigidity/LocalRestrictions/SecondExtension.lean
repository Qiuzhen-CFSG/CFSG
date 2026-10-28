module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.Witnesses
public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.SecondExtension.Certificates
public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.SecondExtension.Graph

/-!
# The additional automorphism of the second Tits parabolic

The assignment with Sylow images `[10,9,76,16,41,193,456,1168]` and reflection
image `NF(1224)*(s8*r8)` satisfies the cyclic and three-coset collection equations.
The graph subgroup therefore projects isomorphically to the actual parabolic;
explicit inverse words make the other projection surjective. Its automorphism
preserves the marked Sylow subgroup and restricts to the pair `(76,1168)`.

This supplies the precise witness consumed by
`secondRestrictions_card_ge_of_extra`, with the literal Sylow inclusion and no
additional premise. The construction uses finite-model equations, not an
assumed amalgam rigidity theorem or a permutation normalizer.

Source context: Parrott (1972), §5, p.683; Aschbacher--Smith F.1.11–12,
printed pp.262–263. Witness discovery and conventions are recorded in
`LocalRestrictions/source/README.md`.
-/

public section
noncomputable section
namespace Tits.AmalgamRigidity
open ExceptionalParabolics RelativeSecondBlockLayers
open SharpOuterBound.LocalImageBound

namespace SecondExtension

private theorem endpoint_exists :
    ∃ a : MulAut second, ∀ i, a (gen i) = images gen i := by
  apply exists_aut gen (images gen) gen_sylowRelations images_sylowRelations
    gen_cosetRelations images_cosetRelations gen_generates images_generate
  intro p q h
  apply secondNormalForm_bijective.injective
  simpa only [normalForm_gen] using h

/-- The concrete endpoint automorphism with the specified generator images. -/
def endpointAut : MulAut second := by exact Classical.choose endpoint_exists

theorem endpointAut_gen (i : Fin 9) : endpointAut (gen i) = images gen i :=
  Classical.choose_spec endpoint_exists i

private theorem image_mem_sylow (a : Fin 9) (ha : a ≠ 0) :
    (images gen a).val ∈ S := by
  have hi : (imageIndex a).2 = 0 := by fin_cases a <;> simp_all [imageIndex]
  change (word gen (imageIndex a).1 * rep gen (imageIndex a).2).val ∈ S
  rw [hi]
  simp only [rep, Fin.val_zero, pow_zero, mul_one, word_gen_val]
  exact atlas1600SylowTwoNormalForm_mem _

private theorem image_word_mem_sylow (n : Fin 2048) :
    (word (images gen) n).val ∈ S := by
  exact word_mem_of (images gen) (S.subgroupOf second) image_mem_sylow n

private theorem endpointAut_preserves (s : S) :
    (endpointAut (sylowAmalgam.right s)).val ∈ S := by
  obtain ⟨n, hn⟩ := atlas1600SylowTwoNormalForm_surjective s.property
  have hs : sylowAmalgam.right s = word gen n := Subtype.ext (hn.symm.trans (word_gen_val n).symm)
  rw [hs]
  have he : endpointAut.toMonoidHom ∘ gen = images gen := funext endpointAut_gen
  change (endpointAut.toMonoidHom (word gen n)).val ∈ S
  rw [map_word, he]
  exact image_word_mem_sylow n

private def sylowHom : S →* S where
  toFun s := ⟨(endpointAut (sylowAmalgam.right s)).val, endpointAut_preserves s⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

private theorem sylowHom_injective : Function.Injective sylowHom := by
  intro x y h
  apply Subtype.ext
  have he : endpointAut (sylowAmalgam.right x) = endpointAut (sylowAmalgam.right y) :=
    Subtype.ext (congrArg (fun z : S => z.val) h)
  exact congrArg (fun z : second => z.val) (endpointAut.injective he)

/-- Its restriction to the literal marked Sylow subgroup. -/
def sylowAut : MulAut S := by
  exact MulEquiv.ofBijective sylowHom sylowHom_injective.bijective_of_finite

theorem sylowAut_compatible (s : S) :
    endpointAut (sylowAmalgam.right s) = sylowAmalgam.right (sylowAut s) :=
  Subtype.ext rfl

private theorem sylowAut_third : sylowAut (sylowGenerator 2) = atlas1600SylowTwoEquiv 76 := by
  apply Subtype.ext
  change (endpointAut (gen 3)).val = _
  rw [endpointAut_gen]
  change (word gen 76 * rep gen 0).val = _
  simp only [rep, Fin.val_zero, pow_zero, mul_one, word_gen_val, atlas1600SylowTwoEquiv_apply]

private theorem sylowAut_eighth : sylowAut (sylowGenerator 7) = atlas1600SylowTwoEquiv 1168 := by
  apply Subtype.ext
  change (endpointAut (gen 8)).val = _
  rw [endpointAut_gen]
  change (word gen 1168 * rep gen 0).val = _
  simp only [rep, Fin.val_zero, pow_zero, mul_one, word_gen_val, atlas1600SylowTwoEquiv_apply]

theorem sylowAut_pair : generatorPair sylowAut = (76, 1168) := by
  simp only [generatorPair, sylowAut_third, sylowAut_eighth, Equiv.symm_apply_apply]

end SecondExtension

/-- The extra second-endpoint restriction required for the Tits amalgam count. -/
theorem secondExtraExtension : SecondExtraExtension :=
  ⟨SecondExtension.sylowAut,
    ⟨SecondExtension.endpointAut, SecondExtension.sylowAut_compatible⟩,
    SecondExtension.sylowAut_pair⟩

end Tits.AmalgamRigidity
