module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.CentralKernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.CubicPair
public import Theory.Representation.NormalElementaryQuotient.SubgroupSpaceTransport
public import Theory.Representation.BinaryOffender.QuadraticHomogeneousOrbit

/-!
# The small action on the original moved factor

Under the crossed geometry supplied by separated-seed analysis, the original
local cubic bound descends to the full local automizer of W = [V_M,L]. The
literal subspace coordinates identify the two permuted complementary moved
factors. A faithful action of the perfect simple component forces their
dimension above two, so `CubicPair` handles both preserved and exchanged
summands of a minimal cubic actor.

The stabilizer image is the action of (L₀T) ∩ N_G(W), with its exact centralizer
kernel. Its component image retains one L/O₂(L) marking and is simple; original
moved minimality gives irreducibility on that component. Thus the recognition
consumer has the actual faithful action and its cubic bound, rather than just
a bound on the component or a group-family label.

Separated-seed analysis and exhaustive B.4 recognition remain explicit source
obligations of the central Hall owner. The `MovedDomain` consumer supplies these proved small-action inputs to the
Chapter K source hypotheses and the existing Hall assembly.
Source: Aschbacher--Smith 3.2.6(3b), B.4.2/B.4.5 and 10.1.1,
printed pp.581,86--87,741.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.NormalElementaryQuotient
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

abbrev localCarrier := D.moduleSubgroup.subgroupOf (localJoin T L)
private theorem join_le_maximal : localJoin T L ≤ D.maximalLocal :=
  sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
local instance localCarrierNormal : (localCarrier D).Normal :=
  (source_parabolic_module_reduced D).normal
local instance localCarrierElementary : IsElementaryAbelian 2 (localCarrier D) :=
  (source_parabolic_module_reduced D).elementary
local instance movedCubicElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

local instance localCarrierFiniteDimensional : FiniteDimensional (ZMod 2) (Additive (localCarrier D)) :=
  Module.Finite.of_finite

abbrev localActor := localJoin T L ⧸ centralizer (localCarrier D : Set (localJoin T L))
def localAction : Representation (ZMod 2) (localActor D) (Additive (localCarrier D)) :=
  representation (localCarrier D) (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
def movedSpace : Submodule (ZMod 2) (Additive (localCarrier D)) :=
  subgroupSpace (localCarrier D) ((⁅D.fullModule,L⁆).subgroupOf (localJoin T L))

theorem moved_le_fullModule : ⁅D.fullModule,L⁆ ≤ D.fullModule :=
  le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
theorem moved_le_localJoin : ⁅D.fullModule,L⁆ ≤ localJoin T L :=
  (moved_le_fullModule D).trans (D.fullModule_le_orbit.trans le_sup_left)

def movedSpaceEquiv (geometry : ModuleGeometry D) : Additive (⁅D.fullModule,L⁆ : Subgroup G) ≃ₗ[ZMod 2] movedSpace D := by
  let W := ⁅D.fullModule,L⁆
  have hWM : W ≤ localJoin T L := by exact moved_le_localJoin D
  let e := (subgroupOfEquivOfLe hWM).symm
  let : IsElementaryAbelian 2 (W.subgroupOf (localJoin T L)) :=
    IsElementaryAbelian.subgroupOf hWM
  let E : Additive W ≃ₗ[ZMod 2] Additive (W.subgroupOf (localJoin T L)) :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  exact E.trans (subgroupSpaceEquiv (localCarrier D) _
    (by
      intro x hx
      change (x : G) ∈ D.moduleSubgroup
      rw [←geometry.full_eq_local]
      exact moved_le_fullModule D hx))

/-- The subspace coordinates retain the original element of W. -/
theorem movedSpaceEquiv_apply_coe (geometry : ModuleGeometry D)
    (w : Additive (⁅D.fullModule,L⁆ : Subgroup G)) :
    (((movedSpaceEquiv D geometry w).val.toMul : localJoin T L) : G) = (w.toMul : G) := by
  let : IsElementaryAbelian 2 ((⁅D.fullModule,L⁆).subgroupOf (localJoin T L)) :=
    IsElementaryAbelian.subgroupOf (moved_le_localJoin D)
  exact congrArg (localJoin T L).subtype
    (subgroupSpaceEquiv_apply_coe (localCarrier D) _ _ _)

theorem movedSpace_finrank_gt_two {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) :
    2 < Module.finrank (ZMod 2) (movedSpace D) := by
  let ρ := movedQuotientAction D c.nonnormal
  let Q := Additive ((⁅D.fullModule,L⁆ : Subgroup G) ⧸
    (sourceMovedFixed D).subgroupOf ⁅D.fullModule,L⁆)
  let : FiniteDimensional (ZMod 2) Q := Module.Finite.of_finite
  let := D.quasisimple
  let := component_simple D c.nonnormal
  let : Group.IsPerfect (L ⧸ pCore 2 L) := inferInstance
  have hQ : 2 < Module.finrank (ZMod 2) Q := by
    by_contra hn
    have htr := representation_eq_one_of_isPerfect_of_finrank_le_two ρ (Nat.le_of_not_gt hn)
    obtain ⟨g,hg⟩ := exists_ne (1 : L ⧸ pCore 2 L)
    exact hg (movedQuotientAction_faithful D c.nonnormal ((htr g).trans ρ.map_one.symm))
  let s := wholeMovedSection_of_central_hstar D c geometry
  have hinj : Function.Injective s.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [s.kernel_eq,bot_subgroupOf]
  let E : Additive (⁅D.fullModule,L⁆ : Subgroup G) ≃ₗ[ZMod 2] Q :=
    LinearEquiv.ofBijective (s.coordinates.toAdditiveLeft.toZModLinearMap 2)
      ⟨hinj,s.onto⟩
  rw [← (movedSpaceEquiv D geometry).finrank_eq,E.finrank_eq]
  exact hQ

theorem movedSpace_permuted_pair {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) :
    ∃ t : localActor D, IsCompl (movedSpace D) ((movedSpace D).map (localAction D t)) ∧
      ∀ a : localActor D, (movedSpace D).map (localAction D a) = movedSpace D ∨
        (movedSpace D).map (localAction D a) = (movedSpace D).map (localAction D t) := by
  obtain ⟨t,ht,htn,_,hp,hperm⟩ := source_nonnormal_fullModule_pair D c.nonnormal
  let M := localJoin T L
  let U := localCarrier D
  let W := ⁅D.fullModule,L⁆
  let tM : M := ⟨t,(show (T : Subgroup G) ≤ M from le_sup_right) ht⟩
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  have hW := moved_le_fullModule D
  have hWM := moved_le_localJoin D
  have hc : Disjoint W (W.map (MulAut.conj t).toMonoidHom) := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro w hw
    exact (movedFixed_eq_bot_of_central_hstar D c geometry).le
      ⟨hw.1,geometry.crossed t ht htn hw.2⟩
  have hmap (g : M) :
      (W.subgroupOf M).map (MulAut.conj g).toMonoidHom =
        (W.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf M := by
    ext x
    constructor
    · rintro ⟨a,ha,he⟩
      exact ⟨a,ha,congrArg Subtype.val he⟩
    · rintro ⟨a,ha,he⟩
      exact ⟨⟨a,hWM ha⟩,ha,Subtype.ext he⟩
  have hspace (g : M) : (movedSpace D).map (localAction D (q g)) =
      subgroupSpace U ((W.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf M) := by
    rw [movedSpace,localAction,subgroupSpace_map_conj,hmap]
  refine ⟨q tM,?_,?_⟩
  · rw [hspace]
    constructor
    · apply subgroupSpace_disjoint
      apply disjoint_iff.mpr
      apply bot_unique
      intro w hw
      exact mem_bot.mpr (Subtype.ext (mem_bot.mp (hc.eq_bot.le hw)))
    · apply codisjoint_iff.mpr
      have hWt : W.map (MulAut.conj t).toMonoidHom ≤ D.fullModule := by
        rw [hp]
        exact le_sup_right
      change subgroupSpace U (W.subgroupOf M) ⊔
        subgroupSpace U ((W.map (MulAut.conj t).toMonoidHom).subgroupOf M) = ⊤
      have hWU : W.subgroupOf M ≤ U := by
        intro x hx
        change (x : G) ∈ D.moduleSubgroup
        rw [←geometry.full_eq_local]
        exact hW hx
      have hWtU : (W.map (MulAut.conj t).toMonoidHom).subgroupOf M ≤ U :=
        by
          intro x hx
          change (x : G) ∈ D.moduleSubgroup
          rw [←geometry.full_eq_local]
          exact hWt hx
      rw [←subgroupSpace_sup U hWU hWtU,
        ←subgroupOf_sup hWM (hWt.trans (D.fullModule_le_orbit.trans le_sup_left)),
        ←hp]
      ext v
      exact iff_of_true ((le_componentOrbit D.moduleSubgroup D.maximalLocal) v.toMul.property) Submodule.mem_top
  · intro a
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (U : Set M)) a
    rw [hspace g]
    rcases hperm g (join_le_maximal D g.property) with he | he
    · left
      rw [he]
      rfl
    · right
      rw [he,hspace tM]

/-- The original local cubic bound descends to the actual stabilizer image on
W=[V_M,L], including actors that exchange its two crossed summands. -/
theorem movedSpace_cubic_bound {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D)
    (hbound : SourceLocalModuleCubicBound D) :
    cubicRatio (subspaceImageRepresentation (localAction D) (movedSpace D)) ≤ 2 := by
  obtain ⟨t,hpair,hperm⟩ := movedSpace_permuted_pair D c geometry
  have hb : cubicRatio (localAction D) ≤ 2 := hbound
  exact cubicRatio_le_two_of_permuted_pair (localAction D)
    (representation_injective (localCarrier D) (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))
    (movedSpace D) t hpair hperm (movedSpace_finrank_gt_two D c geometry) hb

abbrev movedActor := subspaceActionImage (localAction D) (movedSpace D)
abbrev movedAction := subspaceImageRepresentation (localAction D) (movedSpace D)
abbrev movedNormalizer := localJoin T L ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)

theorem movedSpace_stabilizer_iff (geometry : ModuleGeometry D) (g : localJoin T L) :
    QuotientGroup.mk' (centralizer (localCarrier D : Set (localJoin T L))) g ∈
      subspaceStabilizer (localAction D) (movedSpace D) ↔
      (g : G) ∈ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let P := localJoin T L
  let U := localCarrier D
  let W := ⁅D.fullModule,L⁆
  have hWV : W ≤ D.fullModule := moved_le_fullModule D
  have hWP : W ≤ P := moved_le_localJoin D
  have hWU : W.subgroupOf P ≤ U := by
    intro x hx
    change (x : G) ∈ D.moduleSubgroup
    rw [←geometry.full_eq_local]
    exact hWV hx
  have he := stabilizer_comap U (QuotientGroup.mk' (centralizer (U : Set P)))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) ((W.subgroupOf P).subgroupOf U)
  rw [map_subgroupOf_eq_of_le hWU,←subgroupOf_normalizer_eq hWP] at he
  exact (congrArg (fun J : Subgroup P => g ∈ J) he).to_iff

def movedNormalizerProjection (geometry : ModuleGeometry D) : movedNormalizer D →* movedActor D :=
  (subspaceActionHom (localAction D) (movedSpace D)).comp
    (((QuotientGroup.mk' (centralizer (localCarrier D : Set (localJoin T L)))).comp
      (inclusion (show movedNormalizer D ≤ localJoin T L from inf_le_left))).codRestrict _
      (fun g => (movedSpace_stabilizer_iff D geometry ⟨g,g.property.1⟩).mpr g.property.2))

theorem movedNormalizerProjection_surjective (geometry : ModuleGeometry D) : Function.Surjective (movedNormalizerProjection D geometry) := by
  intro a
  obtain ⟨b,rfl⟩ := (stabilizerRepresentation (localAction D) (movedSpace D)).asGroupHom.rangeRestrict_surjective a
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective
    (centralizer (localCarrier D : Set (localJoin T L))) b.val
  have hs : (g : G) ∈ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
    apply (movedSpace_stabilizer_iff D geometry g).mp
    rw [hg]
    exact b.property
  refine ⟨⟨g,g.property,hs⟩,?_⟩
  change subspaceActionHom (localAction D) (movedSpace D) _ =
    subspaceActionHom (localAction D) (movedSpace D) b
  congr 1
  exact Subtype.ext hg

def movedNormalizerSection (geometry : ModuleGeometry D) : BinaryConjugationSection (movedNormalizer D)
    ⁅D.fullModule,L⁆ ⊥ ((movedAction D).comp (movedNormalizerProjection D geometry)) where
  section_le := le_inf
    ((source_full_moved_le_component D).trans ((le_componentOrbit L T).trans le_sup_left))
    (⁅D.fullModule,L⁆ : Subgroup G).le_normalizer
  kernel_le := bot_le
  normalized := inf_le_right
  coordinates := {
    toFun w := Multiplicative.ofAdd (movedSpaceEquiv D geometry (Additive.ofMul w))
    map_one' := (movedSpaceEquiv D geometry).map_zero
    map_mul' w v := (movedSpaceEquiv D geometry).map_add (Additive.ofMul w) (Additive.ofMul v) }
  onto := by
    intro v
    obtain ⟨w,hw⟩ := (movedSpaceEquiv D geometry).surjective v.toAdd
    exact ⟨w.toMul,hw⟩
  kernel_eq := by
    ext w
    change movedSpaceEquiv D geometry (Additive.ofMul w) = 0 ↔ (w : G) ∈ (⊥ : Subgroup G)
    rw [(movedSpaceEquiv D geometry).map_eq_zero_iff,mem_bot]
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  equivariant := by
    intro g w
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (((movedSpaceEquiv D geometry (Additive.ofMul
      (⟨(g:G)*w*(g:G)⁻¹,_⟩ : (⁅D.fullModule,L⁆ : Subgroup G)))).val.toMul : localJoin T L) : G) =
      (((localAction D (QuotientGroup.mk' _ ⟨g,g.property.1⟩)
        (movedSpaceEquiv D geometry (Additive.ofMul w)).val).toMul : localJoin T L) : G)
    rw [movedSpaceEquiv_apply_coe]
    have he := congrArg (localJoin T L).subtype
      (representation_apply (localCarrier D)
        (QuotientGroup.mk' (centralizer (localCarrier D : Set (localJoin T L))))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
        ⟨g,g.property.1⟩ (movedSpaceEquiv D geometry (Additive.ofMul w)).val)
    change _ = (g:G) *
      (((movedSpaceEquiv D geometry (Additive.ofMul w)).val.toMul : localJoin T L):G) *
      (g:G)⁻¹ at he
    rw [movedSpaceEquiv_apply_coe] at he
    exact he.symm

/-- The small action is the faithful image of the literal local normalizer. -/
theorem movedAction_faithful : Function.Injective (movedAction D) :=
  subspaceImageRepresentation_injective (localAction D) (movedSpace D)

/-- The quotient map kills exactly the original local centralizer of W. -/
theorem movedNormalizerProjection_kernel (geometry : ModuleGeometry D) :
    (movedNormalizerProjection D geometry).ker.map (movedNormalizer D).subtype =
      movedNormalizer D ⊓ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  have he := (movedNormalizerSection D geometry).action_kernel_map
    (show movedNormalizer D ≤ normalizer (↑(⊥ : Subgroup G) : Set G) from le_normalizer_of_normal)
  rw [MonoidHom.ker_comp_of_injective _ _ (movedAction_faithful D)] at he
  rw [he]
  apply le_antisymm
  · exact le_inf (commutatorPreimage_le _ _ _)
      (commutator_eq_bot_iff_le_centralizer.mp (bot_unique
        (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)))
  · exact le_commutatorPreimage inf_le_left
      (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le

theorem component_le_movedNormalizer : L ≤ movedNormalizer D :=
  le_inf ((le_componentOrbit L T).trans le_sup_left) (normalizer_commutator_ge_right _ _)

def movedComponentProjection (geometry : ModuleGeometry D) : L →* movedActor D :=
  (movedNormalizerProjection D geometry).comp (inclusion (component_le_movedNormalizer D))

/-- The component restriction retains exactly the same W-coordinates. -/
def movedComponentSection (geometry : ModuleGeometry D) : BinaryConjugationSection L
    ⁅D.fullModule,L⁆ ⊥ ((movedAction D).comp (movedComponentProjection D geometry)) where
  section_le := source_full_moved_le_component D
  kernel_le := bot_le
  normalized := normalizer_commutator_ge_right _ _
  coordinates := (movedNormalizerSection D geometry).coordinates
  onto := (movedNormalizerSection D geometry).onto
  kernel_eq := (movedNormalizerSection D geometry).kernel_eq
  equivariant l w := (movedNormalizerSection D geometry).equivariant
    ⟨l,component_le_movedNormalizer D l.property⟩ w

/-- On the component, the original quotient kernel is precisely O₂(L). -/
theorem movedComponentProjection_kernel {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) :
    (movedComponentProjection D geometry).ker = pCore 2 L := by
  have he := (movedComponentSection D geometry).action_kernel_map
    (show L ≤ normalizer (↑(⊥ : Subgroup G) : Set G) from le_normalizer_of_normal)
  rw [MonoidHom.ker_comp_of_injective _ _ (movedAction_faithful D)] at he
  rw [←movedFixed_eq_bot_of_central_hstar D c geometry,
    moved_quotient_kernel D c.nonnormal] at he
  exact map_injective L.subtype_injective he

/-- The recognized layer keeps the original L/O₂(L) marking. -/
def movedComponentEquiv {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) :
    (L ⧸ pCore 2 L) ≃* (movedComponentProjection D geometry).range :=
  (QuotientGroup.quotientMulEquivOfEq (movedComponentProjection_kernel D c geometry).symm).trans
    (QuotientGroup.quotientKerEquivRange (movedComponentProjection D geometry))

theorem movedComponentEquiv_mk {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) (l : L) :
    movedComponentEquiv D c geometry (QuotientGroup.mk' (pCore 2 L) l) =
      (movedComponentProjection D geometry).rangeRestrict l := by
  rfl

theorem movedComponent_simple {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) :
    IsSimpleGroup (movedComponentProjection D geometry).range := by
  let := component_simple D c.nonnormal
  exact (movedComponentEquiv D c geometry).symm.isSimpleGroup

/-- Recognition sees irreducibility already on the original component. -/
theorem movedComponentAction_irreducible {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) (hmin : MovedMinimal D) :
    Representation.IsIrreducible ((movedAction D).comp (movedComponentProjection D geometry)) := by
  let : Nontrivial (movedSpace D) := Module.nontrivial_of_finrank_pos
    (lt_trans (by decide : 0 < 2) (movedSpace_finrank_gt_two D c geometry))
  apply (movedComponentSection D geometry).irreducible_of_subgroup_minimal
  intro J hJW hLJ
  rcases hmin J hJW hLJ with he | hc
  · exact Or.inl he
  · exact Or.inr ((le_inf hJW hc).trans (movedFixed_eq_bot_of_central_hstar D c geometry).le)

/-- Irreducibility on the literal component image used as the recognized layer. -/
theorem movedComponentImage_irreducible {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) (hmin : MovedMinimal D) :
    Representation.IsIrreducible ((movedAction D).comp (movedComponentProjection D geometry).range.subtype) := by
  apply (Representation.irreducible_comp_surjective_iff
    (movedComponentProjection D geometry).rangeRestrict
    (movedComponentProjection D geometry).rangeRestrict_surjective _).mp
  exact movedComponentAction_irreducible D c geometry hmin

/-- Original moved minimality proves irreducibility for the full local
stabilizer image, retaining its quotient map and all outer actors. -/
theorem movedAction_irreducible {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) (hmin : MovedMinimal D) :
    (movedAction D).IsIrreducible := by
  let : Nontrivial (movedSpace D) := Module.nontrivial_of_finrank_pos
    (lt_trans (by decide : 0 < 2) (movedSpace_finrank_gt_two D c geometry))
  apply (Representation.irreducible_comp_surjective_iff (movedNormalizerProjection D geometry)
    (movedNormalizerProjection_surjective D geometry) _).mp
  apply (movedNormalizerSection D geometry).irreducible_of_subgroup_minimal
  intro J hJW hNJ
  have hLN : L ≤ movedNormalizer D := le_inf
    ((le_componentOrbit L T).trans le_sup_left) (normalizer_commutator_ge_right _ _)
  rcases hmin J hJW (hLN.trans hNJ) with he | hc
  · exact Or.inl he
  · exact Or.inr ((le_inf hJW hc).trans (movedFixed_eq_bot_of_central_hstar D c geometry).le)

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
