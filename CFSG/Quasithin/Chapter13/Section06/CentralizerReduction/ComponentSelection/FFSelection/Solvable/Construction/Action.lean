module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Configuration
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Action
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement

/-!
# The actual offender actor for the solvable construction

The representation on the internal subgroup of G_v is intertwined with
`starRepresentation` on the original U_v. Fixed-space dimensions and all
best-offender comparisons agree. Consequently the image of J(T_v) belongs
to the latter's offender subgroup; the literal X-family commutator then
puts X in that same actor.

The B.5.3 application uses its genuine inverse-image SQTK cover. We also
expose the source-correct adequate classifier: its quasisimple branch uses
the projective-line convention, and its outer branch keeps the actual
A₆–C₃ extension without the disputed splitting of the module. No branch
is selected from solvability alone.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.2.4,
B.5.3–6, printed pp.75, 104–105, and 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
universe u
variable {G : Type u} [Group G]

private noncomputable def internalEquiv (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] [IsElementaryAbelian 2 (internalUv z v)] :
    Additive (internalUv z v) ≃ₗ[ZMod 2] Additive (Uv z v) :=
  let e : Additive (internalUv z v) ≃+ Additive (Uv z v) :=
    (subgroupOfEquivOfLe (Uv_le_Gv z v hz)).toAdditive
  e.toLinearEquiv (fun c w => ZMod.map_smul e.toAddMonoidHom c w)

private theorem internalEquiv_intertwines (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] [IsElementaryAbelian 2 (internalUv z v)]
    (g : Gstar z v) (w : Additive (internalUv z v)) :
    internalEquiv z v hz (uvRepresentation z v hz g w) =
      starRepresentation z v g (internalEquiv z v hz w) := by
  obtain ⟨a, rfl⟩ := starMk_surjective z v g
  apply Additive.toMul.injective
  apply Subtype.ext
  change (((uvRepresentation z v hz (starMk z v a) w).toMul : Gv v) : G) = _
  rw [uvRepresentation_apply, starRepresentation_mk_apply]
  rfl

private theorem offender_le_of_equiv {D V W : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D V) (ρ : Representation (ZMod 2) D W)
    (e : V ≃ₗ[ZMod 2] W) (he : ∀ g w, e (σ g w) = ρ g (e w)) :
    offenderSubgroup σ ≤ offenderSubgroup ρ := by
  have hw (A : Subgroup D) : weight σ A = weight ρ A := by
    have hm := fixedSpace_map_equivariant σ ρ (MonoidHom.id D) e he A
    simp only [Subgroup.map_id] at hm
    have hd := (Submodule.equivMapOfInjective e.toLinearMap e.injective
      (fixedSpace σ A)).finrank_eq
    rw [hm] at hd
    exact congrArg (rank A + ·) hd
  apply iSup_le
  intro A
  apply iSup_le
  rintro ⟨hA, _⟩
  have hB : IsBestOffender ρ A := ⟨hA.1, fun B hBA => by
    rw [← hw B, ← hw A]
    exact hA.2 B hBA⟩
  exact le_iSup_of_le A (le_iSup_of_le ⟨hB, le_top⟩ le_rfl)

/-- The literal Sylow Thompson image is contained in the offender actor on U_v.
The equivalence above preserves every best-offender weight. -/
theorem thompson_le_star_offender [Finite G] (T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v) :
    starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v)) ≤
      offenderSubgroup (starRepresentation z v) := by
  let : IsElementaryAbelian 2 (internalUv z v) :=
    IsElementaryAbelian.subgroupOf (Uv_le_Gv z v hz)
  exact (Subnormal.thompson_star_le_offender T z v hz S hS).trans
    (offender_le_of_equiv _ _ (internalEquiv z v hz) (internalEquiv_intertwines z v hz))


/-- Discharge the containment premise of `XFamily_le_offender` on its
original vector carrier and quotient map. -/
theorem XFamily_le_star_offender [Finite G] (L T : Subgroup G) (z v : G)
    (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : X ∈ XFamily L T z v) :
    X ≤ FFFactors.offenderActor (starRepresentation z v) :=
  XFamily_le_offender L T z v hX (thompson_le_star_offender T z v hz S hS)

/-- The residual convention in X₀ is exactly intrinsic two-perfectness. -/
theorem XFamily_isPPerfect (L T : Subgroup G) (z v : G)
    {X : Subgroup (Gstar z v)} (hX : X ∈ XFamily L T z v) : IsPPerfect 2 X := by
  apply (pResidual_eq_top_iff 2 X).mp
  apply map_injective X.subtype_injective
  simpa only [← MonoidHom.range_eq_map, range_subtype] using hX.1.2.1

/-- Restriction to the offender actor retains normality, nontriviality,
two-perfectness, solvability, and the full Thompson commutator. -/
theorem minimalSolvable_in_offender [Finite G] (L T : Subgroup G) (z v : G)
    (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let A := X.subgroupOf I
    A.Normal ∧ A ≠ ⊥ ∧ IsPPerfect 2 A ∧ Group.IsSolvable A ∧
      ⁅A, (starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))).subgroupOf I⁆ = A := by
  dsimp only
  let I := FFFactors.offenderActor (starRepresentation z v)
  let : X.Normal := hX.1.2
  let : Group.IsSolvable X := hX.2.1
  have hXI := XFamily_le_star_offender L T z v hz S hS hX.1
  have hJI := thompson_le_star_offender T z v hz S hS
  have e := subgroupOfEquivOfLe hXI
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · intro hb
    have hm := congrArg (Subgroup.map I.subtype) hb
    rw [map_subgroupOf_eq_of_le hXI, Subgroup.map_bot] at hm
    exact hX.1.1.2.2.1 hm
  · exact (XFamily_isPPerfect L T z v hX.1).of_surjective
      e.symm.toMonoidHom e.symm.surjective
  · exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  · apply map_injective I.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hXI,
      map_subgroupOf_eq_of_le hJI]
    exact hX.1.1.2.2.2

/-- Apply the corrected B.5.6 implication to the actual offender restriction.
The universal earlier theorem remains the assembly owner's explicit input. -/
theorem classify_star_offender_source [Finite G] (z v : G)
    [IsElementaryAbelian 2 (Uv z v)] {K : GroupClass.{u}}
    (classification : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} K)
    (hlocal : IsSQTK K (Gv v)) (hcore : pCore 2 (Gstar z v) = ⊥) :
    ChapterB.SourceInduction.AdequateAlternative
      (FFFactors.offenderRepresentation (starRepresentation z v)) := by
  let : Module.Finite (ZMod 2) (Additive (Uv z v)) := Module.Finite.of_finite
  have h := FFFactors.offender_hypothesis (starRepresentation z v)
    (starMk z v) (starMk_surjective z v) hlocal (starRepresentation_injective z v) hcore
  apply classification
  refine ⟨h.finite_module, h.faithful, h.twoCore, h.generated, ?_⟩
  obtain ⟨c⟩ := h.quotient
  let := c.coverGroup
  let := c.coverFinite
  let := c.kernelNormal
  exact ⟨{ Cover := c.Cover, kernel := c.kernel, sqtk := c.sqtk, equiv := c.equiv }⟩

/-- A genuine X-family member excludes the trivial classification branch.
The Sylow-central seed proves the two-core premise rather than assuming it. -/
theorem classify_XFamily_source [Finite G] (L T : Subgroup G) (z v : G)
    (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {K : GroupClass.{u}}
    (classification : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} K)
    (hlocal : IsSQTK K (Gv v))
    {X : Subgroup (Gstar z v)} (hX : X ∈ XFamily L T z v) :
    ChapterB.SourceInduction.NontrivialAdequateAlternative
      (FFFactors.offenderRepresentation (starRepresentation z v)) := by
  have hXI := XFamily_le_star_offender L T z v hz S hS hX
  let : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX.1.2.2.1
  let : Nontrivial (FFFactors.offenderActor (starRepresentation z v)) :=
    Function.Injective.nontrivial (inclusion_injective hXI)
  exact (classify_star_offender_source z v classification hlocal
    (Gstar_twoCore_eq_bot T z v ⟨S, hS⟩ hfix)).of_nontrivial _

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction
end
