module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases.Quotients
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases.SixUniform
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases.BinaryDouble
public import Theory.Representation.BinaryOffender.SubspaceAction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.SmallOvergroups

/-!
# The L₃(2) and A₆ point branches of 15.3.49

These conditional source reductions start with the genuine conjugation action
on the literal section U_H/Z. `PointData` keeps Ũ₀ = [Ũ_H,L*], the projection
of the source vector along a fixed complement, its actual stabilizer Y₀*T*,
and the conjugacy taking the strong offender Vγ* to Vα* inside its two-core.

The enumerated classification inputs contain actual actor and equivariant
module identifications. The binary cases are a natural central quotient and
a doubled natural module. The six-letter cases are the natural and core
modules for A₆ or S₆, with the actual component marked. These include all
moved-module alternatives relevant here; possible extensions of the ambient
module are handled by restricting the strong offender to Ũ₀.

For the central binary extension the stabilizer of a lift is normal in the
quotient point stabilizer, so its intrinsic core lies in the computed natural
point core. The doubled module has no strong offender by the elementary
rank bound and additivity of codimension. In the six-letter core the natural
projection preserves vector stabilizers. No point-core bound, preferred
coordinate for the source point, or no-offender assertion is assumed.

`binary_overgroup_le` constructs the contradiction from local witnesses for
K outside M using K's own quotient K/O₂(K). Its containment conclusion feeds
the published small-overgroup generation reduction. The parent still supplies
the genuine universal local conclusions and the enumerated earlier
classification outputs; this module does not assert the full 15.3.49.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.2–3,
printed pp.83–84; B.4.2, p.86; B.5.1, pp.99–103; B.5.6, pp.105–106;
and the final point paragraphs of 15.3.49, printed p.1145.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open ModelExclusions
open Theory.SpecificGroups.SymmetricSix
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases

section Alternatives
variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]

/-- The two B.5.1 alternatives for the actual moved module in the binary
three-dimensional component branch. Natural and dual natural are both
allowed by changing the actual actor equivalence. The central quotient
includes the natural module itself and its nonsplit central extension. -/
inductive BinaryModuleCase (ρ : Representation (ZMod 2) K V) (L : Subgroup K) : Prop
  | centralNatural (e : K ≃* Matrix.PSL3Two.SL) (whole : L = ⊤)
      (C : Subrepresentation ρ) (central : C.toSubmodule = fixedSpace ρ L)
      (E : (V ⧸ C.toSubmodule) ≃ₗ[ZMod 2] PointCases.Binary.Vector)
      (equivariant : ∀ g v, E (C.quotientRepresentation g v) =
        PointCases.Binary.natural (e g) (E v))
  | doubledNatural (e : K ≃* Matrix.PSL3Two.SL) (whole : L = ⊤)
      (E : V ≃ₗ[ZMod 2] (PointCases.Binary.Vector × PointCases.Binary.Vector))
      (equivariant : ∀ g v, E (ρ g v) =
        (PointCases.Binary.natural.prod PointCases.Binary.natural) (e g) (E v))

/-- The actual component is A₆, and the whole actor is A₆ or S₆. For the
moved module the B.5.1/B.3.3 alternatives are natural and core. Ambient
full/deleted extensions are covered by restriction to this moved module. -/
inductive SixModuleCase (ρ : Representation (ZMod 2) K V) (L : Subgroup K) : Prop
  | naturalAlternating (e : K ≃* alternatingGroup (Fin 6)) (whole : L = ⊤)
      (E : V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
      (equivariant : ∀ g v, E (ρ g v) =
        BinaryPermutation.naturalRepresentation (Fin 6) (e g).val (E v))
  | coreAlternating (e : K ≃* alternatingGroup (Fin 6)) (whole : L = ⊤)
      (E : V ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6))
      (equivariant : ∀ g v, E (ρ g v) =
        BinaryPermutation.coreRepresentation (Fin 6) (e g).val (E v))
  | naturalSymmetric (e : K ≃* S6)
      (component : L.map e.toMonoidHom = alternatingGroup (Fin 6))
      (E : V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
      (equivariant : ∀ g v, E (ρ g v) =
        BinaryPermutation.naturalRepresentation (Fin 6) (e g) (E v))
  | coreSymmetric (e : K ≃* S6)
      (component : L.map e.toMonoidHom = alternatingGroup (Fin 6))
      (E : V ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6))
      (equivariant : ∀ g v, E (ρ g v) =
        BinaryPermutation.coreRepresentation (Fin 6) (e g) (E v))

variable [FiniteDimensional (ZMod 2) V]

theorem BinaryModuleCase.exclude (ρ : Representation (ZMod 2) K V) (L : Subgroup K)
    (h : BinaryModuleCase ρ L) (z : V) (hp : pointStabilizer ρ z ≠ ⊤)
    {A : Subgroup K} (hA : A ≤ localTwoCore (pointStabilizer ρ z)) :
    ¬ IsStrongOffender ρ A := by
  cases h with
  | centralNatural e whole C hc E he =>
    apply PointCases.Quotients.binary_central_natural_exclusion ρ e C _ E he z hp hA
    rw [hc,whole]
  | doubledNatural e whole E he =>
    intro hs
    exact PointCases.BinaryDouble.not_strong_double _
      (strong_map_equivariant ρ (PointCases.Binary.natural.prod PointCases.Binary.natural)
        e.toMonoidHom e.injective E he hs)

omit [FiniteDimensional (ZMod 2) V] in
private theorem stabilizer_ne_top_map
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) K V) (σ : Representation (ZMod 2) D W)
    (e : K ≃* D) (E : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, E (ρ g v) = σ (e g) (E v))
    (z : V) (hp : pointStabilizer ρ z ≠ ⊤) :
    pointStabilizer σ (E z) ≠ ⊤ := by
  intro ht
  apply hp
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [pointStabilizer_map_equivariant ρ σ e E he,ht,
    Subgroup.map_top_of_surjective _ e.surjective]

omit [FiniteDimensional (ZMod 2) V] in
theorem SixModuleCase.exclude (ρ : Representation (ZMod 2) K V) (L : Subgroup K)
    (h : SixModuleCase ρ L) (z : V) (hp : pointStabilizer ρ z ≠ ⊤)
    {A : Subgroup K} (hA : A ≤ localTwoCore (pointStabilizer ρ z)) :
    ¬ IsStrongOffender ρ A := by
  intro hs
  cases h with
  | naturalAlternating e whole E he =>
    let f := (alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom
    have hm := strong_map_equivariant ρ (BinaryPermutation.naturalRepresentation (Fin 6))
      f ((alternatingGroup (Fin 6)).subtype_injective.comp e.injective) E he hs
    exact SixPoint.not_strong_natural_of_even (by rintro _ ⟨g,hg,rfl⟩; exact (e g).property) hm
  | coreAlternating e whole E he =>
    let f := (alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom
    have hm := strong_map_equivariant ρ (BinaryPermutation.coreRepresentation (Fin 6))
      f ((alternatingGroup (Fin 6)).subtype_injective.comp e.injective) E he hs
    exact SixPoint.not_strong_core_of_even (by rintro _ ⟨g,hg,rfl⟩; exact (e g).property) hm
  | naturalSymmetric e comp E he =>
    have hn := stabilizer_ne_top_map ρ (BinaryPermutation.naturalRepresentation (Fin 6)) e E he z hp
    have hz : E z ≠ 0 := by
      intro hz
      apply hn
      rw [hz]
      exact top_unique (fun _ _ => map_zero _)
    apply exclude_strong_at_identified_point ρ (BinaryPermutation.naturalRepresentation (Fin 6))
      e E he z (pointStabilizer ρ z) A rfl hA _ hs
    exact fun _ hB => PointCases.SixUniform.not_strong_point (E z) hz hB
  | coreSymmetric e comp E he =>
    have hn := stabilizer_ne_top_map ρ (BinaryPermutation.coreRepresentation (Fin 6)) e E he z hp
    apply exclude_strong_at_identified_point ρ (BinaryPermutation.coreRepresentation (Fin 6))
      e E he z (pointStabilizer ρ z) A rfl hA _ hs
    exact fun _ hB => PointCases.SixUniform.not_strong_core_point (E z) hn hB
end Alternatives

section Source
variable {G : Type*} [Group G] [Finite G]
  {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

/-- The local source conclusions used by the two point branches. All
objects remain on the literal action on U_H/Z. The linear retraction
specifies the projection along a globally fixed complement; the moved-space
equality prevents replacing Ũ₀ by an unrelated model module. -/
structure PointData (action : SectionAction H U Z)
    (L Y₀ T Vα Vγ : Subgroup G) where
  moved : Subrepresentation action.representation
  moved_eq : moved.toSubmodule = subspaceCommutator action.representation ⊤ (starImage H L)
  sourceGenerator : U
  projection : Additive (U ⧸ Z.subgroupOf U) →ₗ[ZMod 2] moved.toSubmodule
  projection_retract : ∀ v : moved.toSubmodule, projection v.val = v
  fixed_remainder : ∀ v, v - (projection v).val ∈ fixedSpace action.representation ⊤
  point_nonzero : projection (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) sourceGenerator)) ≠ 0
  stabilizer : starImage H Y₀ ⊔ starImage H T = pointStabilizer moved.toRepresentation
    (projection (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) sourceGenerator)))
  proper : starImage H Y₀ ⊔ starImage H T ≠ ⊤
  alpha_in_core : starImage H Vα ≤ localTwoCore (starImage H Y₀ ⊔ starImage H T)
  conjugator : H ⧸ pCore 2 H
  conjugate : starImage H Vα = (starImage H Vγ).map (MulAut.conj conjugator).toMonoidHom
  gamma_quadratic : IsQuadratic action.representation (starImage H Vγ)
  gamma_best : IsBestOffender action.representation (starImage H Vγ)
  gamma_strong : IsStrongOffender action.representation (starImage H Vγ)

variable (action : SectionAction H U Z) {L Y₀ T Vα Vγ : Subgroup G}

/-- The point is the projection of a literal quotient representative. -/
def PointData.point (d : PointData action L Y₀ T Vα Vγ) : d.moved.toSubmodule :=
  d.projection (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) d.sourceGenerator))

omit [Finite G] in
/-- Projection along the fixed complement preserves the actual source
point stabilizer in the whole star actor. -/
theorem PointData.point_stabilizer_eq_source (d : PointData action L Y₀ T Vα Vγ) :
    pointStabilizer d.moved.toRepresentation (d.point action) =
      pointStabilizer action.representation
        (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) d.sourceGenerator)) := by
  ext g
  let z := Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) d.sourceGenerator)
  have hh := d.fixed_remainder z ⟨g,mem_top g⟩
  change action.representation g (z - (d.projection z).val) = z - (d.projection z).val at hh
  rw [map_sub] at hh
  constructor
  · intro hg
    have hg' := congrArg Subtype.val hg
    change action.representation g (d.projection z).val = (d.projection z).val at hg'
    change action.representation g z = z
    simpa only [hg',sub_left_inj] using hh
  · intro hg
    apply Subtype.ext
    change action.representation g (d.projection z).val = (d.projection z).val
    change action.representation g z = z at hg
    simpa only [hg,sub_right_inj] using hh

/-- The L₃(2) branch of p.1145, conditional on the enumerated B.5.1 output.
The point-core bound is proved by the binary model calculation above. -/
theorem exclude_binary (d : PointData action L Y₀ T Vα Vγ)
    (hmodels : BinaryModuleCase d.moved.toRepresentation (starImage H L)) : False := by
  have ha := strong_alpha action d.gamma_strong d.conjugator d.conjugate
  have hs : IsStrongOffender d.moved.toRepresentation (starImage H Vα) :=
    ⟨ha.1,(fixedCodim_subrepresentation_le action.representation d.moved _).trans_lt ha.2⟩
  apply hmodels.exclude _ _ (d.point action) _ _ hs
  · exact d.stabilizer.symm ▸ d.proper
  · exact d.stabilizer ▸ d.alpha_in_core

/-- The A₆ branch treats both whole actors and both moved-module extensions.
No no-offender premise or selected model point is an input. -/
theorem exclude_six (d : PointData action L Y₀ T Vα Vγ)
    (hmodels : SixModuleCase d.moved.toRepresentation (starImage H L)) : False := by
  have ha := strong_alpha action d.gamma_strong d.conjugator d.conjugate
  have hs : IsStrongOffender d.moved.toRepresentation (starImage H Vα) :=
    ⟨ha.1,(fixedCodim_subrepresentation_le action.representation d.moved _).trans_lt ha.2⟩
  apply hmodels.exclude _ _ (d.point action) _ _ hs
  · exact d.stabilizer.symm ▸ d.proper
  · exact d.stabilizer ▸ d.alpha_in_core
end Source

section SmallerOvergroup
variable {G : Type*} [Group G] [Finite G]

/-- Witnesses constructed locally for a smaller overgroup. In particular
its actor is K/O₂(K), with its own elementary section and its own source point. -/
structure BinaryOutsideWitness (K : Subgroup G) where
  U : Subgroup G
  Z : Subgroup G
  L : Subgroup G
  Y₀ : Subgroup G
  T : Subgroup G
  Vα : Subgroup G
  Vγ : Subgroup G
  elementary : IsElementaryAbelian 2 U
  action : @SectionAction G _ K U Z elementary
  data : @PointData G _ K U Z elementary action L Y₀ T Vα Vγ
  classification : BinaryModuleCase data.moved.toRepresentation (starImage K L)

/-- Local conclusions for K outside M now force containment. The actual
quotient equivalence is passed to their constructor; containment is proved
here and is not an earlier-result input. -/
theorem binary_overgroup_le (K M : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (construct : ¬ K ≤ M →
      (K ⧸ pCore 2 K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) →
      Nonempty (BinaryOutsideWitness K)) : K ≤ M := by
  by_contra hn
  obtain ⟨w⟩ := construct hn e
  let _ := w.elementary
  exact exclude_binary w.action w.data w.classification

/-- The published small-overgroup generation reduction with its L₃(2)
containment premise discharged by local point witnesses. -/
theorem exclude_small_overgroups_from_points {H M L Y₀ T : Subgroup G}
    (d : ReducedLocalData H M L Y₀ T)
    (hgen : H ≤ sSup (smallOvergroups H Y₀ T))
    (construct : ∀ K : Subgroup G, Y₀ ⊔ T ≤ K → K ≤ H → ¬ K ≤ M →
      (K ⧸ pCore 2 K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) →
      Nonempty (BinaryOutsideWitness K)) : False := by
  apply exclude_by_small_overgroups d hgen
  intro K hYK hKH hmodel
  obtain ⟨e⟩ := hmodel
  exact binary_overgroup_le K M e (construct K hYK hKH)
end SmallerOvergroup
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases
