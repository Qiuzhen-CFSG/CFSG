module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Ranks
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.SectionOffender

/-!
# Transport from the literal seed quotient to the original action

The quotient LA/C_LA(U) embeds in the action image of the stabilizer of U.
Its action is literally the seed action, and its offender image maps to
Aut_A(U). This identifies the ranks and fixed codimensions used on the two
sides of the comparison. In particular, a ratio-one conclusion on the
quotient gives the precise `SeedRankEquality` needed by B.1.5.

Faithfulness of L on U also reflects inner conjugation: containment of the
actual offender image in the component image makes A induce inner
automorphisms of the original L. No containment A ≤ L is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.107, the quotient (LA)⁺ and the cases with q((LA)⁺,U)=1.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)

/-- The canonical embedding of LA/C_LA(U) into the full stabilizer action
image on U. Its definition retains both literal action maps. -/
noncomputable def seedImageHom {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) :
    SeedQuotient ρ hLA →* subspaceActionImage ρ (naturalSeedSpace ρ L A) :=
  QuotientGroup.lift (seedSubrepresentation ρ hLA).toRepresentation.ker
    ((subspaceActionHom ρ (naturalSeedSpace ρ L A)).comp
      (Subgroup.inclusion (seedSpace_stable ρ hLA))) (by
        intro g hg
        apply subspaceImageRepresentation_injective ρ (naturalSeedSpace ρ L A)
        ext w
        exact congrArg Subtype.val (LinearMap.congr_fun (MonoidHom.mem_ker.mp hg) w))

@[simp] theorem seedImageHom_apply {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (g : (L ⊔ A : Subgroup G)) :
    seedImageHom ρ hLA (seedQuotientMap ρ hLA g) =
      subspaceActionHom ρ (naturalSeedSpace ρ L A)
        (Subgroup.inclusion (seedSpace_stable ρ hLA) g) := rfl

/-- The identity map on U intertwines the two faithful actions. -/
theorem seedImageHom_intertwines {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (g : SeedQuotient ρ hLA) (w : naturalSeedSpace ρ L A) :
    seedQuotientAction ρ hLA g w =
      subspaceImageRepresentation ρ (naturalSeedSpace ρ L A) (seedImageHom ρ hLA g) w := by
  obtain ⟨g, rfl⟩ := (QuotientGroup.mk'_surjective
    (seedSubrepresentation ρ hLA).toRepresentation.ker) g
  rfl

theorem seedImageHom_injective {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) :
    Function.Injective (seedImageHom ρ hLA) := by
  intro g h he
  apply seedQuotientAction_faithful ρ hLA
  apply LinearMap.ext
  intro w
  exact (seedImageHom_intertwines ρ hLA g w).trans
    ((congrArg (fun q => subspaceImageRepresentation ρ (naturalSeedSpace ρ L A) q w) he).trans
      (seedImageHom_intertwines ρ hLA h w).symm)

/-- The offender is transported as the image of the original A, with no
assumption that its action kernel is already trivial. -/
theorem seedOffenderImage_map {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) :
    (seedOffenderImage ρ hLA).map (seedImageHom ρ hLA) =
      restrictedSubgroup ρ (naturalSeedSpace ρ L A) A := by
  ext x
  constructor
  · rintro ⟨q, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨Subgroup.inclusion (seedSpace_stable ρ hLA) a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    let a₀ : (L ⊔ A : Subgroup G) := ⟨a, (le_sup_right : A ≤ L ⊔ A) ha⟩
    exact ⟨seedQuotientMap ρ hLA a₀, ⟨a₀, ha, rfl⟩, rfl⟩

/-- Equality of the two literal offender ranks, even before B=1 is proved. -/
theorem seedOffenderImage_rank {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) :
    rank (seedOffenderImage ρ hLA) =
      rank (restrictedSubgroup ρ (naturalSeedSpace ρ L A) A) := by
  rw [← seedOffenderImage_map ρ hLA]
  exact (rank_map_injective _ (seedImageHom_injective ρ hLA) _).symm

/-- Equality of the fixed codimensions uses the identity on the actual U. -/
theorem seedOffenderImage_fixedCodim {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) :
    fixedCodim (seedQuotientAction ρ hLA) (seedOffenderImage ρ hLA) =
      fixedCodim (subspaceImageRepresentation ρ (naturalSeedSpace ρ L A))
        (restrictedSubgroup ρ (naturalSeedSpace ρ L A) A) := by
  rw [← seedOffenderImage_map ρ hLA]
  exact fixedCodim_map_equivariant _ _ (seedImageHom ρ hLA)
    (LinearEquiv.refl (ZMod 2) _) (seedImageHom_intertwines ρ hLA) _

/-- The concrete ratio-one step consumed by the non-IV branches. -/
theorem seedRankEquality_of_quotient_ratio_one [Finite G] {K : GroupClass.{u}}
    {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (hq : quadraticRatio (seedQuotientAction ρ hLA) = 1) : SeedRankEquality ρ A L := by
  let := p.source.finite_module
  have he := ((p.minimal.1.isOffender _).best_and_codim_eq_of_quadraticRatio_eq_one _ hq).2
  rw [seedOffenderImage_fixedCodim, seedOffenderImage_rank] at he
  exact he.symm

/-- Faithful component restriction identifies the representation as well as
the group, using the identity intertwiner on the original seed space. -/
noncomputable def seedComponentActionEquiv [Finite G] {K : GroupClass.{u}}
    {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA) :
    ActionEquiv (seedComponentAction ρ hLA)
      ((seedQuotientAction ρ hLA).comp (seedComponentImage ρ hLA).subtype) where
  groupEquiv := seedComponentEquiv ρ hLA p
  linearEquiv := LinearEquiv.refl (ZMod 2) _
  intertwines _ _ := rfl

/-- Containment in L⁺ proves inner action on L; it does not assert A ≤ L. -/
theorem inducesInner_of_seedOffenderImage_le [Finite G] {K : GroupClass.{u}}
    {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (ha : seedOffenderImage ρ hLA ≤ seedComponentImage ρ hLA) : InducesInner A L := by
  intro a haA
  let a₀ : (L ⊔ A : Subgroup G) := ⟨a, (le_sup_right : A ≤ L ⊔ A) haA⟩
  obtain ⟨l, hl, he⟩ := ha (show seedQuotientMap ρ hLA a₀ ∈ seedOffenderImage ρ hLA from
    ⟨a₀, haA, rfl⟩)
  refine ⟨l, hl, ?_⟩
  intro x hx
  let x₀ : (L ⊔ A : Subgroup G) := ⟨x, (le_sup_left : L ≤ L ⊔ A) hx⟩
  have haL := p.component_normal.conj_mem x hx a
  have hlL := p.component_normal.conj_mem x hx l
  have heq : (⟨a * x * a⁻¹, haL⟩ : L) = ⟨l * x * l⁻¹, hlL⟩ := by
    apply (seedComponentEquiv ρ hLA p).injective
    apply Subtype.ext
    change seedQuotientMap ρ hLA (a₀ * x₀ * a₀⁻¹) =
      seedQuotientMap ρ hLA (l * x₀ * l⁻¹)
    simp only [map_mul, map_inv, he]
  exact congrArg Subtype.val heq

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
