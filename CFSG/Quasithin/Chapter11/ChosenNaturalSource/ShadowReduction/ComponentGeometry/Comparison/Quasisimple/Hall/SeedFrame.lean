module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.InnerRadical
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.SeedQuotient
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.UnipotentOvergroups
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry

/-!
# The original rank-one seed inside the three Hall models

The kernel of the literal seed action is solvable, so its PSL₂(q)
two-core quotient survives with the original representative formula.
The seed is perfect and nontrivial. Its fixed-and-moving vector makes
its normalizer proper in the quasisimple component image, while the
original Sylow action puts a full inner Sylow in that normalizer.
Concrete Sylow-overgroup geometry therefore gives a common parabolic
marking for the normalizer and its perfect seed in SL₃(q), Sp₄(q), or
G₂(q). The original radical acts trivially on the seed two-core quotient.
The SL₃ scalar center and the two-core maps are retained throughout.

Classification.lean applies the construction to the original chosen flag
and discharges the model, Sylow-invariance and fixed-space inputs. This
supplies the seed placement needed for the remaining inner-radical
argument; it does not yet identify the seed with the entire local group
or establish the final omega-center inequality. Those steps and final
11.4.2 assembly remain with qt-d-1222-shadow-component-comparison.
Earlier-source discharge remains with qt-d-1222-shadow-components.
Source: Aschbacher--Smith 11.4.2, printed p.777. Imported G₂ calculations
retain LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.SeedFrame
open Classification
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The original L₁ image, with the previously published action map unchanged. -/
abbrev seed := AlternatingSeven.seedImage E
/-- The literal projection of the original L₁ onto its action image. -/
abbrev seedMap := AlternatingSeven.seedProjection E
/-- The same image restricted to the point-component image. -/
abbrev innerSeed := (seed E).subgroupOf (componentImage E)

/-- The literal seed-action kernel is solvable in every quasisimple image row. -/
theorem seed_kernel_solvable (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) : Group.IsSolvable (seedMap E).ker := by
  let f := (projection E).subgroupMap (component E)
  let : IsQuasisimple (componentImage E) := (action_structure E h hf hne hstar hcent).2.2
  let : IsSimpleGroup (componentImage E ⧸ center (componentImage E)) := IsQuasisimple.simple
  let : Nontrivial (componentImage E) :=
    (QuotientGroup.mk'_surjective (center (componentImage E))).nontrivial
  have hproper : f.ker ≠ ⊤ := by
    intro ht
    obtain ⟨x,hx⟩ := exists_ne (1 : componentImage E)
    obtain ⟨k,rfl⟩ := (projection E).subgroupMap_surjective (component E) x
    exact hx (show k ∈ f.ker from ht.symm ▸ mem_top k)
  let : Group.IsSolvable f.ker := hstar.1.1.isSolvable_of_subnormal_lt_top
    (inferInstance : f.ker.Normal).isSubnormal hproper
  let j : (seedMap E).ker →* f.ker := {
    toFun := fun x => ⟨⟨⟨x.val.val,
      ((le_conjugateSpanBy _ _).trans le_sup_left) x.val.property⟩,
      (le_conjugateSpanBy _ _) x.val.property⟩, by
        apply Subtype.ext
        exact congrArg (fun k : seed E => (k : ActionQuotient E)) x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  exact Group.isSolvable_of_isSolvable_injective (f := j) (by
    intro x y hxy
    exact Subtype.ext (Subtype.ext
      (congrArg (fun k : f.ker => (((k : component E) : localGroup E) : G)) hxy)))

/-- The original rank-one quotient survives through the actual action map. -/
def seedQuotientEquiv (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier)) :
    (seed E ⧸ pCore 2 (seed E)) ≃* PSL(2,E.input.field.Carrier) := by
  have hlarge : 3 < Nat.card E.input.field.Carrier := by
    rw [E.input.field.card_eq]
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (show 2 ≤ E.input.field.degree from E.input.nonbinary)
    omega
  let : IsSimpleGroup PSL(2,E.input.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup (E.L₁ ⧸ pCore 2 E.L₁) := e.isSimpleGroup
  let : Group.IsPerfect E.L₁ := LocalGeometry.localResidual_perfect _
  let : Group.IsSolvable (seedMap E).ker := seed_kernel_solvable E h hf hne hstar hcent
  exact (PerfectCoreTwoExtension.solvableKernelQuotientEquiv
    (seedMap E) (AlternatingSeven.seedProjection_surjective E)).symm.trans e

@[simp] theorem seedQuotientEquiv_mk (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier)) (x : E.L₁) :
    seedQuotientEquiv E h hf hne hstar hcent e
      (QuotientGroup.mk' (pCore 2 (seed E)) (seedMap E x)) =
      e (QuotientGroup.mk' (pCore 2 E.L₁) x) := by
  have hlarge : 3 < Nat.card E.input.field.Carrier := by
    rw [E.input.field.card_eq]
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (show 2 ≤ E.input.field.degree from E.input.nonbinary)
    omega
  let : IsSimpleGroup PSL(2,E.input.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup (E.L₁ ⧸ pCore 2 E.L₁) := e.isSimpleGroup
  let : Group.IsPerfect E.L₁ := LocalGeometry.localResidual_perfect _
  let : Group.IsSolvable (seedMap E).ker := seed_kernel_solvable E h hf hne hstar hcent
  change e ((PerfectCoreTwoExtension.solvableKernelQuotientEquiv
    (seedMap E) (AlternatingSeven.seedProjection_surjective E)).symm
    (QuotientGroup.mk' (pCore 2 (seed E)) (seedMap E x))) = _
  rw [← PerfectCoreTwoExtension.solvableKernelQuotientEquiv_mk (seedMap E)
    (AlternatingSeven.seedProjection_surjective E), MulEquiv.symm_apply_apply]

/-- The specified fixed-and-moving vector distinguishes the two literal images. -/
theorem seed_ne_component (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) : seed E ≠ componentImage E := by
  obtain ⟨v,hv,hnv⟩ := AlternatingSeven.exists_fixed_not_component_fixed E h hf hne hstar hcent
  intro he
  change v ∈ Representation.BinaryOffender.fixedSpace (action E) (seed E) at hv
  change v ∉ Representation.BinaryOffender.fixedSpace (action E) (componentImage E) at hnv
  exact hnv (he ▸ hv)

/-- The full original quotient Sylow normalizes the marked seed. -/
theorem sylow_image_normalizes_seed (hT : (T : Subgroup G) ≤ E.G₁) :
    ((sylow E : Subgroup (localGroup E)).map (projection E)) ≤
      normalizer (seed E : Set (ActionQuotient E)) := by
  apply (map_mono (f := projection E) ?_).trans (le_normalizer_map _)
  have hn := LocalGeometry.sylow_normalizes_localResidual D E.V₁ hT
  intro t ht
  apply mem_normalizer_iff.mpr
  intro x
  change ((x : G) ∈ E.L₁) ↔ (t : G) * (x : G) * (t : G)⁻¹ ∈ E.L₁
  exact (mem_normalizer_iff.mp (hn ht)) x

/-- A full inner Sylow is available in the actual seed normalizer. -/
theorem exists_inner_sylow (h : EarlierGeometry E) (hT : (T : Subgroup G) ≤ E.G₁) :
    ∃ P : Sylow 2 (componentImage E),
      (P : Subgroup (componentImage E)) ≤ normalizer (innerSeed E : Set (componentImage E)) := by
  let := componentImage_normal E h
  let S := (sylow E).mapSurjective (f := projection E) (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal (componentImage E)
  refine ⟨P,?_⟩
  rw [hP]
  intro x hx
  apply mem_normalizer_iff.mpr
  intro y
  exact (mem_normalizer_iff.mp (sylow_image_normalizes_seed E hT hx)) y

/-- The original seed image is perfect and nontrivial; its actual quotient
is PSL₂ over the original field. -/
theorem seed_perfect_nontrivial (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier)) :
    Group.IsPerfect (seed E) ∧ Nontrivial (seed E) := by
  let : Group.IsPerfect E.L₁ := LocalGeometry.localResidual_perfect _
  have hlarge : 3 < Nat.card E.input.field.Carrier := by
    rw [E.input.field.card_eq]
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (show 2 ≤ E.input.field.degree from E.input.nonbinary)
    omega
  let : IsSimpleGroup PSL(2,E.input.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : Nontrivial (seed E ⧸ pCore 2 (seed E)) :=
    (seedQuotientEquiv E h hf hne hstar hcent e).toEquiv.nontrivial
  exact ⟨Group.IsPerfect.ofSurjective (AlternatingSeven.seedProjection_surjective E),
    (QuotientGroup.mk'_surjective (pCore 2 (seed E))).nontrivial⟩

/-- The normalizer of the literal seed is proper in the component image. -/
theorem inner_seed_normalizer_ne_top (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier)) :
    normalizer (innerSeed E : Set (componentImage E)) ≠ ⊤ := by
  let : IsQuasisimple (componentImage E) := (action_structure E h hf hne hstar hcent).2.2
  obtain ⟨hp,hn⟩ := seed_perfect_nontrivial E h hf hne hstar hcent e
  let := hp
  let := hn
  let ei := subgroupOfEquivOfLe (AlternatingSeven.seedImage_le_componentImage E)
  let : Group.IsPerfect (innerSeed E) := Group.IsPerfect.ofSurjective (f := ei.symm.toMonoidHom) ei.symm.surjective
  let : Nontrivial (innerSeed E) := ei.toEquiv.nontrivial
  intro ht
  let : (innerSeed E).Normal := normalizer_eq_top_iff.mp ht
  rcases IsQuasisimple.normal_le_center_or_eq_top (innerSeed E) with hc | he
  · exact Group.IsPerfect.not_isSolvable (innerSeed E)
      (Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp (hc b.property) a)))
  · exact seed_ne_component E h hf hne hstar hcent
      (le_antisymm (AlternatingSeven.seedImage_le_componentImage E)
        (subgroupOf_eq_top.mp he))

private theorem image_normalizer_ne_top {A B : Type*} [Group A] [Group B]
    (N : Subgroup A) (hN : N ≠ ⊤) (e : A ≃* B) : N.map e.toMonoidHom ≠ ⊤ := by
  intro he
  apply hN
  apply map_injective (f := e.toMonoidHom) e.injective
  rwa [map_top_of_surjective _ e.surjective]

/-- G₂: the actual seed normalizer lies in a concrete root parabolic. -/
theorem g2_seed_normalizer_parabolic (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (e₁ : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier))
    (hT : (T : Subgroup G) ≤ E.G₁)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : componentImage E ≃* Atlas.G2.Model F) :
    ∃ g : Atlas.G2.Model F,
      (normalizer (innerSeed E : Set (componentImage E))).map
        ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) ≤ Atlas.G2.LieParabolicSetup.parabolic₁ ∨
      (normalizer (innerSeed E : Set (componentImage E))).map
        ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) ≤ Atlas.G2.LieParabolicSetup.parabolic₂ := by
  obtain ⟨P,hP⟩ := exists_inner_sylow E h hT
  obtain ⟨g,hg⟩ := Atlas.G2.ProperSylowOvergroups.conjugate_le_parabolic
    (P.mapSurjective (f := e.toMonoidHom) e.surjective)
    ((normalizer (innerSeed E : Set (componentImage E))).map e.toMonoidHom)
    (map_mono hP) (image_normalizer_ne_top _
      (inner_seed_normalizer_ne_top E h hf hne hstar hcent e₁) e)
  exact ⟨g,by simpa only [map_map] using hg⟩

/-- Sp₄: the same original normalizer lies in a point or plane parabolic. -/
theorem sp4_seed_normalizer_parabolic (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (e₁ : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier))
    (hT : (T : Subgroup G) ≤ E.G₁)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : componentImage E ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    ∃ g : Theory.SpecificGroups.SymplecticFour.Sp F,
      (normalizer (innerSeed E : Set (componentImage E))).map
        ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) ≤
          Theory.SpecificGroups.SymplecticFour.pointParabolic ∨
      (normalizer (innerSeed E : Set (componentImage E))).map
        ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) ≤
          Theory.SpecificGroups.SymplecticFour.planeParabolic := by
  obtain ⟨P,hP⟩ := exists_inner_sylow E h hT
  obtain ⟨g,hg⟩ := Theory.SpecificGroups.SymplecticFour.ThreeResidualPlacement.proper_sylow_overgroup_parabolic_cover
    hF (P.mapSurjective (f := e.toMonoidHom) e.surjective)
    ((normalizer (innerSeed E : Set (componentImage E))).map e.toMonoidHom)
    (map_mono hP) (image_normalizer_ne_top _
      (inner_seed_normalizer_ne_top E h hf hne hstar hcent e₁) e)
  exact ⟨g,by simpa only [map_map] using hg⟩

/-- SL₃: the covering center is retained while the seed normalizer is
placed in a vector or covector parabolic. -/
theorem sl3_seed_normalizer_parabolic (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (e₁ : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier))
    (hT : (T : Subgroup G) ≤ E.G₁)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ E.input.field.degree)
    (e : componentImage E ≃* SL(3,F)) :
    ∃ a : componentImage E ≃* SL(3,F),
      (normalizer (innerSeed E : Set (componentImage E))).map a.toMonoidHom ≤
          Matrix.PSL3.LinearThree.pointParabolicSL F ∨
      (normalizer (innerSeed E : Set (componentImage E))).map a.toMonoidHom ≤
          Matrix.PSL3.LinearThree.lineParabolicSL F := by
  obtain ⟨P,hP⟩ := exists_inner_sylow E h hT
  obtain ⟨g,hg,_⟩ := Matrix.PSL3.CartanActions.BorelQuotient.sylowSL_normalizer_conjugate
    F E.input.field.degree_pos hF (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  simp only [Sylow.coe_mapSurjective] at hg
  let a := e.trans (MulAut.conj g).symm
  have hPa : (P : Subgroup (componentImage E)).map a.toMonoidHom =
      Matrix.PSL3.LinearThree.unipotentSL F := by
    change (P : Subgroup (componentImage E)).map
      ((MulAut.conj g).symm.toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map, ← hg, map_map]
    have hh : (MulAut.conj g).symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id SL(3,F) := MonoidHom.ext fun x => (MulAut.conj g).symm_apply_apply x
    rw [hh,map_id]
  exact ⟨a,Matrix.PSL3.LinearThree.UnipotentOvergroups.overgroup_unipotentSL F _
    (hPa ▸ map_mono hP) (image_normalizer_ne_top _
      (inner_seed_normalizer_ne_top E h hf hne hstar hcent e₁) a)⟩

/-- The original radical acts trivially on the actual seed quotient by
its two-core. Both normalizing actions are proved on the original carrier. -/
theorem radical_seed_commutator_le_core (hT : (T : Subgroup G) ≤ E.G₁) :
    ⁅(radical E).map (projection E), seed E⁆ ≤ (seed E).pCoreIn 2 := by
  have hR : IsPGroup 2 ((radical E).map (projection E)) :=
    ((isPGroup_pCoreIn 2 (E.L₁ ⊔ (T : Subgroup G))).comap_subtype).map _
  have hseedR : seed E ≤ normalizer ((radical E).map (projection E) : Set (ActionQuotient E)) := by
    apply (map_mono (f := projection E) ?_).trans (le_normalizer_map _)
    have hn : E.L₁ ≤ normalizer (E.R₁ : Set G) :=
      (le_sup_left.trans (E.L₁ ⊔ (T : Subgroup G)).le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
    apply le_normalizer_iff.mpr
    intro l hl r hr
    exact le_normalizer_iff.mp hn l hl r hr
  have hRseed : (radical E).map (projection E) ≤ normalizer (seed E : Set (ActionQuotient E)) :=
    (map_mono (show radical E ≤ (sylow E : Subgroup (localGroup E)) from
      fun _ hx => radical_le_sylow E hx)).trans (sylow_image_normalizes_seed E hT)
  exact le_pCoreIn_of_normalizes
    (hR.to_le (le_normalizer_iff_commutator_le_left.mp hseedR))
    (le_normalizer_iff_commutator_le_right.mp hRseed)
    (normalizer_commutator_ge_right _ _)

/-- A common marking of the component, its seed normalizer and the seed
itself, at the original field size. The normalizer lies in a full parabolic
and the perfect seed lies in that parabolic's actual rank-one local. -/
def ParabolicFrame : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ E.input.field.degree ∧
    ((∃ e : componentImage E ≃* SL(3,F),
      ((normalizer (innerSeed E : Set (componentImage E))).map e.toMonoidHom ≤
          Matrix.PSL3.LinearThree.pointParabolicSL F ∧
        (innerSeed E).map e.toMonoidHom ≤ Matrix.PSL3.LinearThree.pointLocalSL F) ∨
      ((normalizer (innerSeed E : Set (componentImage E))).map e.toMonoidHom ≤
          Matrix.PSL3.LinearThree.lineParabolicSL F ∧
        (innerSeed E).map e.toMonoidHom ≤ Matrix.PSL3.LinearThree.lineLocalSL F)) ∨
    (∃ e : componentImage E ≃* Theory.SpecificGroups.SymplecticFour.Sp F,
      ((normalizer (innerSeed E : Set (componentImage E))).map e.toMonoidHom ≤
          Theory.SpecificGroups.SymplecticFour.pointParabolic ∧
        (innerSeed E).map e.toMonoidHom ≤ Theory.SpecificGroups.SymplecticFour.pointLocal) ∨
      ((normalizer (innerSeed E : Set (componentImage E))).map e.toMonoidHom ≤
          Theory.SpecificGroups.SymplecticFour.planeParabolic ∧
        (innerSeed E).map e.toMonoidHom ≤ Theory.SpecificGroups.SymplecticFour.planeLocal)) ∨
    (∃ e : componentImage E ≃* Atlas.G2.Model F,
      ((normalizer (innerSeed E : Set (componentImage E))).map e.toMonoidHom ≤
          Atlas.G2.LieParabolicSetup.parabolic₁ ∧
        (innerSeed E).map e.toMonoidHom ≤ Atlas.G2.LieParabolicSetup.local₁) ∨
      ((normalizer (innerSeed E : Set (componentImage E))).map e.toMonoidHom ≤
          Atlas.G2.LieParabolicSetup.parabolic₂ ∧
        (innerSeed E).map e.toMonoidHom ≤ Atlas.G2.LieParabolicSetup.local₂)))

/-- The three surviving image rows all give a literal parabolic frame;
no seed placement, field-automorphism or inner-radical premise is supplied. -/
theorem parabolic_frame (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (e₁ : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier))
    (hT : (T : Subgroup G) ≤ E.G₁) (hm : RankTwoModel E) : ParabolicFrame E := by
  obtain ⟨hp,_⟩ := seed_perfect_nontrivial E h hf hne hstar hcent e₁
  let := hp
  let ei := subgroupOfEquivOfLe (AlternatingSeven.seedImage_le_componentImage E)
  let : Group.IsPerfect (innerSeed E) := Group.IsPerfect.ofSurjective (f := ei.symm.toMonoidHom) ei.symm.surjective
  rcases hm with hm | hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hlarge : 4 ≤ Nat.card F := by
      rw [hF]
      exact (show 2 ^ 2 ≤ 2 ^ E.input.field.degree from
        Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) E.input.nonbinary)
    obtain ⟨a,ha⟩ := sl3_seed_normalizer_parabolic E h hf hne hstar hcent e₁ hT hF e
    let : Group.IsPerfect ((innerSeed E).map a.toMonoidHom) := Group.IsPerfect.map _
    refine ⟨F,inferInstance,inferInstance,hF,Or.inl ⟨a,?_⟩⟩
    rcases ha with ha | ha
    · refine Or.inl ⟨ha,?_⟩
      rw [← Matrix.PSL3.LinearThree.pointParabolicSL_residual F hlarge]
      exact le_map_solvableResidual_of_isPerfect ((innerSeed E).map a.toMonoidHom) _ ((map_mono (f := a.toMonoidHom) (innerSeed E).le_normalizer).trans ha)
    · refine Or.inr ⟨ha,?_⟩
      rw [← Matrix.PSL3.LinearThree.lineParabolicSL_residual F hlarge]
      exact le_map_solvableResidual_of_isPerfect ((innerSeed E).map a.toMonoidHom) _ ((map_mono (f := a.toMonoidHom) (innerSeed E).le_normalizer).trans ha)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact (show 2 ^ 1 < 2 ^ E.input.field.degree from
        Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) E.input.nonbinary)
    obtain ⟨g,hg⟩ := sp4_seed_normalizer_parabolic E h hf hne hstar hcent e₁ hT hlarge e
    let a := e.trans (MulAut.conj g)
    let : Group.IsPerfect ((innerSeed E).map a.toMonoidHom) := Group.IsPerfect.map _
    refine ⟨F,inferInstance,inferInstance,hF,Or.inr (Or.inl ⟨a,?_⟩)⟩
    rcases hg with hg | hg
    · refine Or.inl ⟨hg,?_⟩
      exact (le_map_solvableResidual_of_isPerfect ((innerSeed E).map a.toMonoidHom) _
        ((map_mono (f := a.toMonoidHom) (innerSeed E).le_normalizer).trans hg)).trans
        (Theory.SpecificGroups.SymplecticFour.determinantKernel_solvableResidual_le _)
    · refine Or.inr ⟨hg,?_⟩
      exact (le_map_solvableResidual_of_isPerfect ((innerSeed E).map a.toMonoidHom) _
        ((map_mono (f := a.toMonoidHom) (innerSeed E).le_normalizer).trans hg)).trans
        (Theory.SpecificGroups.SymplecticFour.determinantKernel_solvableResidual_le _)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact (show 2 ^ 1 < 2 ^ E.input.field.degree from
        Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) E.input.nonbinary)
    obtain ⟨g,hg⟩ := g2_seed_normalizer_parabolic E h hf hne hstar hcent e₁ hT e
    let a := e.trans (MulAut.conj g)
    let : Group.IsPerfect ((innerSeed E).map a.toMonoidHom) := Group.IsPerfect.map _
    refine ⟨F,inferInstance,inferInstance,hF,Or.inr (Or.inr ⟨a,?_⟩)⟩
    rcases hg with hg | hg
    · refine Or.inl ⟨hg,?_⟩
      rw [← Atlas.G2.HigherFieldResiduals.parabolic₁_residual hlarge]
      exact le_map_solvableResidual_of_isPerfect ((innerSeed E).map a.toMonoidHom) _ ((map_mono (f := a.toMonoidHom) (innerSeed E).le_normalizer).trans hg)
    · refine Or.inr ⟨hg,?_⟩
      rw [← Atlas.G2.HigherFieldResiduals.parabolic₂_residual hlarge]
      exact le_map_solvableResidual_of_isPerfect ((innerSeed E).map a.toMonoidHom) _ ((map_mono (f := a.toMonoidHom) (innerSeed E).le_normalizer).trans hg)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.SeedFrame
