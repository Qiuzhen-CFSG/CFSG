module
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.CoreCalculation.LinearAction
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.CoreCalculation.LinearKernel
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.CoreCalculation.Transfer
/-!
# Local actions and two-cores in actual linear-field extensions of PSL₃

For either concrete local factor, a normalizing actor has parabolic linear
part. Its marked GL₂ block, rescaled to determinant one, intertwines the
literal local core quotient with an inner SL₂ action followed by the same
coefficient automorphism recovered from the original ambient actor.

If a two-element acts trivially on this quotient, trace forces its field
coefficient to be trivial. The parabolic determinant calculation then puts
it in the embedded local factor. Applying this detection to the two-core
of the relative join proves the core identity for every normalizing
supplement. The final point and line applications retain the original
root-plane radicals and their maps into the common ambient extension.

Source: Aschbacher–Smith F.1.12, printed p.264 (PDF p.275). These calculations
hold over every finite field of characteristic two, in particular under
the source's nonbinary hypotheses. Containment in the actual linear-field
subgroup is an explicit input; geometric diagram-kernel coverage belongs
to the source assembly.
-/

@[expose] public section
open Matrix
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open Theory.GroupTheory.AutomorphismExtensionBorel
namespace Matrix.PSL3.LinearThree.OuterExtensions
open CoreCalculation
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (E : Subgroup (MulAut PSL(3,F)))
    (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E) (hlinear : E ≤ linearField F)

omit [Finite F] [CharP F 2] in
private theorem inverse_linear_preserves (point : Bool) (g : GL (Fin 3) F)
    (h : (localFactor F point).map (linearConj F g).toMonoidHom = localFactor F point) :
    (localFactor F point).map (linearConj F g⁻¹).toMonoidHom = localFactor F point := by
  rw [map_inv]
  conv_lhs => rw [← h]
  rw [Subgroup.map_map]
  have he : (linearConj F g)⁻¹.toMonoidHom.comp (linearConj F g).toMonoidHom =
      MonoidHom.id PSL(3,F) := by
    ext x
    exact (linearConj F g).symm_apply_apply x
  rw [he, Subgroup.map_id]

include hlinear

/-- The literal local quotient action uses the original ambient coefficient.
The conjugating SL₂ matrix comes from the marked GL₂ block of the actor. -/
theorem localBlockAction_semilinear (point : Bool)
    (a : Subgroup.normalizer (localIn F E hinner point : Set E)) :
    ∃ c : SL(2,F), localBlockAction F E hinner point a = MulAut.conj c *
      Atlas.RankOneFieldAutomorphisms.slFieldAction
        (coefficient F ⟨a.val.val,hlinear a.val.property⟩) := by
  let σ := coefficient F ⟨a.val.val,hlinear a.val.property⟩
  obtain ⟨g,hg⟩ := coefficient_factorization F ⟨a.val.val,hlinear a.val.property⟩
  have hp := linear_preserves_of_expression F point a.val.val g σ hg
    (normalizer_preserves F E hinner point a)
  have hs := linear_preserves_shape F point g hp
  have hsi := linear_preserves_shape F point g⁻¹ (inverse_linear_preserves F point g hp)
  obtain ⟨c,hc⟩ := linear_block_inner F point g hs hsi
  refine ⟨c, (localBlockAction_eq_iff F E hinner point a _).mpr ?_⟩
  intro x
  obtain ⟨y,rfl⟩ := (localProjectEquiv F point).surjective x
  have he : actorLocal F E hinner point a (localProjectEquiv F point y) =
      localProjectEquiv F point (linearLocalSL F point g hs hsi (slField F point σ y)) := by
    apply Subtype.ext
    change a.val.val (localProjectEquiv F point y).val = _
    rw [localProjectEquiv_val,localProjectEquiv_val]
    have hf : fieldAction F σ (projection F y.val) =
        projection F (slField F point σ y).val := fieldAction_mk F σ y.val
    have hl : linearConj F g (projection F (slField F point σ y).val) =
        projection F (linearLocalSL F point g hs hsi (slField F point σ y)).val :=
      linearConj_mk F g _
    rw [hg]
    change linearConj F g (fieldAction F σ (projection F y.val)) = _
    exact (congrArg (linearConj F g) hf).trans hl
  rw [he]
  change slBlock F point (linearLocalSL F point g hs hsi (slField F point σ y)) =
    MulAut.conj c (Atlas.RankOneFieldAutomorphisms.slFieldAction σ (slBlock F point y))
  rw [hc, slBlock_field]

/-- A two-element with trivial action on the actual local core quotient lies
in the embedded local factor. -/
theorem two_element_mem_local_of_trivial_block (point : Bool)
    (a : Subgroup.normalizer (localIn F E hinner point : Set E))
    (hp : ∃ k : ℕ, a.val ^ (2 ^ k) = 1)
    (htrivial : localBlockAction F E hinner point a = 1) :
    a.val ∈ localIn F E hinner point := by
  obtain ⟨c,hc⟩ := localBlockAction_semilinear F E hinner hlinear point a
  have hσ := coefficient_eq_one_of_trivial_block F E hinner hlinear point a c hc htrivial
  obtain ⟨g,hg⟩ := coefficient_factorization F ⟨a.val.val,hlinear a.val.property⟩
  rw [hσ,map_one,mul_one] at hg
  have hpres : (localFactor F point).map (linearConj F g).toMonoidHom = localFactor F point :=
    hg ▸ normalizer_preserves F E hinner point a
  obtain ⟨k,hk⟩ := hp
  have hgpow : (linearConj F g) ^ (2 ^ k) = 1 := by
    rw [← hg]
    exact congrArg Subtype.val hk
  obtain ⟨x,hx⟩ := linear_two_element_local F point g (linear_preserves_shape F point g hpres) k hgpow
  refine ⟨(localProjectEquiv F point x).val, (localProjectEquiv F point x).property, ?_⟩
  apply Subtype.ext
  change MulAut.conj (localProjectEquiv F point x).val = a.val.val
  rw [localProjectEquiv_val]
  exact hx.symm.trans hg.symm

/-- The detection statement expressed on the actual quotient, before transporting to SL₂. -/
theorem two_element_mem_local_of_trivial_quotient (point : Bool)
    (a : Subgroup.normalizer (localIn F E hinner point : Set E))
    (hp : ∃ k : ℕ, a.val ^ (2 ^ k) = 1)
    (htrivial : localQuotientAction F E hinner point a = 1) :
    a.val ∈ localIn F E hinner point := by
  apply two_element_mem_local_of_trivial_block F E hinner hlinear point a hp
  exact (congrArg (MulAut.congr (localQuotientEquiv F E hinner point)) htrivial).trans (map_one _)

/-- The local join has the same two-core, compared by the literal inclusions
into the common ambient extension. Normality is only required inside the join. -/
theorem local_join_twoCore_eq (point : Bool) (S : Subgroup E)
    (hS : S ≤ Subgroup.normalizer (localIn F E hinner point : Set E)) :
    (pCore 2 (localIn F E hinner point ⊔ S : Subgroup E)).map
      (localIn F E hinner point ⊔ S).subtype =
      (pCore 2 (localIn F E hinner point)).map (localIn F E hinner point).subtype :=
  join_core_eq_of_detection F E hinner point
    (two_element_mem_local_of_trivial_block F E hinner hlinear point) S hS

/-- Application to the actual point local, preserving its root-plane coordinates. -/
theorem pointLocal_join_twoCore_eq (S : Subgroup E)
    (hS : S ≤ Subgroup.normalizer (localIn F E hinner true : Set E)) :
    (pCore 2 (localIn F E hinner true ⊔ S : Subgroup E)).map
      (localIn F E hinner true ⊔ S).subtype =
      ((pointRadical F).map (pointLocal F).subtype).map (innerEmbedding E hinner) := by
  rw [local_join_twoCore_eq F E hinner hlinear true S hS,local_core_map]
  change ((pCore 2 (pointLocal F)).map (pointLocal F).subtype).map _ = _
  rw [pointLocal_twoCore_eq]

/-- Application to the actual line local, preserving its root-plane coordinates. -/
theorem lineLocal_join_twoCore_eq (S : Subgroup E)
    (hS : S ≤ Subgroup.normalizer (localIn F E hinner false : Set E)) :
    (pCore 2 (localIn F E hinner false ⊔ S : Subgroup E)).map
      (localIn F E hinner false ⊔ S).subtype =
      ((lineRadical F).map (lineLocal F).subtype).map (innerEmbedding E hinner) := by
  rw [local_join_twoCore_eq F E hinner hlinear false S hS,local_core_map]
  change ((pCore 2 (lineLocal F)).map (lineLocal F).subtype).map _ = _
  rw [lineLocal_twoCore_eq]
end Matrix.PSL3.LinearThree.OuterExtensions
