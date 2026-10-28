module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.MovedCubic
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalGroups
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient

/-!
# The genuine recognition domain of the moved automizer

The component image is normal in the literal local automizer. The other
component centralizes W, so the quotient above this image is a two-group.
Faithful irreducibility kills the automizer's two-core, identifying its
simple component image with F*. Theorem A transports strong quasithinness
to this component section, and the two-group quotient transports it to the
whole automizer; the K-group hypothesis retains the complete catalogue.

Together with `MovedCubic`, this proves every Chapter K source hypothesis
for the actual action, its actual component and its L/O₂(L) marking. The
recognition adapter below discharges these group and cubic premises in the
original quotient-recognition contract. Exhaustive model recognition and
separated-seed analysis remain with the central Hall source owner.
Source: Aschbacher--Smith B.4.2/B.4.5, Chapter K introduction and 10.1.1,
printed pp.86--87,451,741.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : (localCarrier D).Normal := localCarrierNormal D
local instance : IsElementaryAbelian 2 (localCarrier D) := localCarrierElementary D
local instance : FiniteDimensional (ZMod 2) (Additive (localCarrier D)) := Module.Finite.of_finite

private theorem join_le_maximal : localJoin T L ≤ D.maximalLocal :=
  sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)

theorem movedNormalizer_le_componentNormalizer {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) :
    movedNormalizer D ≤ normalizer (L : Set G) := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  exact (le_inf (inf_le_left.trans (join_le_maximal D)) inf_le_right).trans
    (source_original_moved_stabilizer_le_component_normalizer D ht htn
      (geometry.crossed t ht htn))

private theorem movedComponent_map (geometry : ModuleGeometry D) :
    (L.subgroupOf (movedNormalizer D)).map (movedNormalizerProjection D geometry) =
      (movedComponentProjection D geometry).range := by
  ext a
  constructor
  · rintro ⟨l,hl,rfl⟩
    exact ⟨⟨l,hl⟩,rfl⟩
  · rintro ⟨l,rfl⟩
    exact ⟨⟨l,component_le_movedNormalizer D l.property⟩,l.property,rfl⟩

theorem movedComponent_normal {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) :
    (movedComponentProjection D geometry).range.Normal := by
  have hn : (L.subgroupOf (movedNormalizer D)).Normal :=
    normal_subgroupOf_of_le_normalizer (movedNormalizer_le_componentNormalizer D c geometry)
  rw [←movedComponent_map D geometry]
  exact Normal.map hn (movedNormalizerProjection D geometry)
    (movedNormalizerProjection_surjective D geometry)

theorem conjugateComponent_centralizes_moved (geometry : ModuleGeometry D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    L.map (MulAut.conj t).toMonoidHom ≤ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  have hi : t⁻¹ ∉ normalizer (L : Set G) := by simpa only [inv_mem_iff] using htn
  rintro x ⟨l,hl,rfl⟩ w hw
  have hc := geometry.crossed t⁻¹ ((T : Subgroup G).inv_mem ht) hi
    (mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hw) l hl
  have he := congrArg (fun z : G => t*z*t⁻¹) hc
  change t*(l*(t⁻¹*w*(t⁻¹)⁻¹))*t⁻¹ = t*((t⁻¹*w*(t⁻¹)⁻¹)*l)*t⁻¹ at he
  change w*(t*l*t⁻¹) = (t*l*t⁻¹)*w
  simpa only [inv_inv,mul_assoc,mul_inv_cancel_left,inv_mul_cancel_left,
    mul_inv_cancel_right,inv_mul_cancel_right,mul_inv_cancel,mul_one] using he.symm

theorem localOrbit_le_movedNormalizer {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) :
    localOrbit T L ≤ movedNormalizer D := by
  obtain ⟨t,ht,htn,hpair,_,_⟩ := source_nonnormal_fullModule_pair D c.nonnormal
  apply le_inf le_sup_left
  rw [hpair]
  exact sup_le (normalizer_commutator_ge_right _ _)
    ((conjugateComponent_centralizes_moved D geometry ht htn).trans (Subgroup.centralizer_le_normalizer _))

theorem movedActor_two_quotient {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) :
    letI := movedComponent_normal D c geometry
    IsPGroup 2 (movedActor D ⧸ (movedComponentProjection D geometry).range) := by
  let := movedComponent_normal D c geometry
  let P := localJoin T L
  let N := movedNormalizer D
  let X := (localOrbit T L).subgroupOf P
  let Y := (localOrbit T L).subgroupOf N
  let S := (movedComponentProjection D geometry).range
  have hPN : P ≤ normalizer (localOrbit T L : Set G) :=
    sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
  let : X.Normal := normal_subgroupOf_of_le_normalizer hPN
  let : Y.Normal := normal_subgroupOf_of_le_normalizer (inf_le_left.trans hPN)
  have hP : IsPGroup 2 (P ⧸ X) := by
    apply isPGroup_quotient_of_sup_eq_top X ((T : Subgroup G).subgroupOf P)
      T.isPGroup'.comap_subtype
    rw [←subgroupOf_sup (show localOrbit T L ≤ P from le_sup_left)
      (show (T : Subgroup G) ≤ P from le_sup_right)]
    exact subgroupOf_self _
  let f := (QuotientGroup.mk' X).comp (inclusion (show N ≤ P from inf_le_left))
  have hk : f.ker = Y := by
    ext n
    exact QuotientGroup.eq_one_iff (N := X) ((inclusion (show N ≤ P from inf_le_left)) n)
  have hY : IsPGroup 2 (N ⧸ Y) :=
    ((hP.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hk)
  have hx : Y ≤ S.comap (movedNormalizerProjection D geometry) := by
    apply (map_le_iff_le_comap).mp
    obtain ⟨t,ht,htn,hpair,_,_⟩ := source_nonnormal_fullModule_pair D c.nonnormal
    have hLt : L.map (MulAut.conj t).toMonoidHom ≤ N :=
      (le_sup_right.trans hpair.symm.le).trans (localOrbit_le_movedNormalizer D c geometry)
    have hLtker : (L.map (MulAut.conj t).toMonoidHom).subgroupOf N ≤
        (movedNormalizerProjection D geometry).ker := by
      intro x hx
      have hc := conjugateComponent_centralizes_moved D geometry ht htn hx
      obtain ⟨y,hy,he⟩ := (movedNormalizerProjection_kernel D geometry).ge ⟨x.property,hc⟩
      exact (Subtype.ext he : y=x) ▸ hy
    change ((localOrbit T L).subgroupOf N).map (movedNormalizerProjection D geometry) ≤ _
    rw [hpair,subgroupOf_sup (component_le_movedNormalizer D) hLt,Subgroup.map_sup,
      movedComponent_map D geometry]
    exact sup_le le_rfl (((Subgroup.map_eq_bot_iff (f := movedNormalizerProjection D geometry) _).mpr hLtker).le.trans bot_le)
  exact hY.of_surjective
    (QuotientGroup.map Y S (movedNormalizerProjection D geometry) hx)
    (QuotientGroup.map_surjective_of_surjective _ _ (movedNormalizerProjection D geometry)
      ((QuotientGroup.mk'_surjective _).comp (movedNormalizerProjection_surjective D geometry)) hx)

theorem movedActor_twoCore_eq_bot {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) (hmin : MovedMinimal D) :
    pCore 2 (movedActor D) = ⊥ := by
  let : (movedAction D).IsIrreducible := movedAction_irreducible D c geometry hmin
  have hk := normal_p_subgroup_le_ker (movedAction D) (pCore 2 (movedActor D)) pCore_isPGroup
  exact bot_unique (hk.trans ((movedAction D).ker_eq_bot_iff.mpr (movedAction_faithful D)).le)


theorem movedActor_fitting {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) (hmin : MovedMinimal D) :
    generalizedFitting (movedActor D) = (movedComponentProjection D geometry).range := by
  let := movedComponent_normal D c geometry
  let := D.quasisimple
  let : IsQuasisimple (movedComponentProjection D geometry).range :=
    IsQuasisimple.of_mulEquiv (movedComponentEquiv D c geometry)
  exact generalizedFitting_eq_of_quasisimple_two_quotient _
    (movedActor_two_quotient D c geometry) (movedActor_twoCore_eq_bot D c geometry hmin)


theorem movedActor_sqtk {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) :
    IsSQTK KnownSimple.IsKnownSimple (movedActor D) := by
  have hJ := (D.local_internal_module (source_module_nonsolvable_uniqueness D)).sqtk
  have hL : IsSQTK KnownSimple.IsKnownSimple L :=
    (IsSQTK.equiv (subgroupOfEquivOfLe
      ((le_componentOrbit L T).trans le_sup_left))).mp
      (hJ.subgroup (L.subgroupOf (localJoin T L)))
  have hN : IsSQTK KnownSimple.IsKnownSimple (movedNormalizer D) :=
    (IsSQTK.equiv (subgroupOfEquivOfLe
      (show movedNormalizer D ≤ localJoin T L from inf_le_left))).mp
      (hJ.subgroup ((movedNormalizer D).subgroupOf (localJoin T L)))
  let S := (movedComponentProjection D geometry).range
  let := movedComponent_normal D c geometry
  let := D.quasisimple
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv (movedComponentEquiv D c geometry)
  have hs : ChapterA.Section02.IsSemisimple S := by
    apply top_unique
    exact le_sSup (show IsComponent S ⊤ from
      ⟨Subgroup.IsSubnormal.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  have hS := (ChapterA.Section02.theoremA_knownSimple (G := L)).stronglyQuasithin_section
    hL.stronglyQuasithin hL.isKGroup
    (ChapterA.Section02.IsSectionOf.of_surjective
      (movedComponentProjection D geometry).rangeRestrict
      (movedComponentProjection D geometry).rangeRestrict_surjective) hs
  exact ⟨ChapterB.QuasisimpleSource.IrreducibleBranch.stronglyQuasithin_of_twoGroup_quotient
    S (movedActor_two_quotient D c geometry) hS,
    hN.isKGroup.of_surjective (movedNormalizerProjection D geometry)
      (movedNormalizerProjection_surjective D geometry)⟩

/-- The source domain of B.4/K, with every actor and quotient identified. -/
theorem movedAction_sourceHypotheses {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (geometry : ModuleGeometry D) (hmin : MovedMinimal D)
    (hlocal : SourceLocalModuleCubicBound D) :
    ChapterK.RankOne.SourceHypotheses (movedAction D)
      (movedComponentProjection D geometry).range := by
  let := D.quasisimple
  exact ⟨movedActor_sqtk D c geometry,movedActor_fitting D c geometry hmin,
    IsQuasisimple.of_mulEquiv (movedComponentEquiv D c geometry),movedAction_faithful D,
    movedComponentImage_irreducible D c geometry hmin,
    movedSpace_cubic_bound D c geometry hlocal⟩

attribute [local instance] localCarrierNormal localCarrierElementary localCarrierFiniteDimensional

/-- The remaining B.4 recognition after all Chapter K source hypotheses
have been proved for the actual local automizer. The output
still marks the literal moved central quotient. This source obligation
remains with qt-d-10-nona5-central-hall-orders. -/
def MovedSmallRecognitionAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H) (c : Context D H B),
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    Chapter1.Section02.NonnormalCComponentModel (L ⧸ pCore 2 L) →
    SourceLocalModuleCubicBound D → SourceFullModuleCubicBound D →
    ∀ geometry : ModuleGeometry D, MovedMinimal D →
    ChapterK.RankOne.SourceHypotheses (movedAction D)
      (movedComponentProjection D geometry).range →
      MovedQuotientRow D c.nonnormal

/-- The exact original hypotheses discharge all Chapter K domain premises,
including SQTK, F*, component irreducibility and the full local cubic bound. -/
theorem movedQuotientRecognition_of_smallRecognition (h : MovedSmallRecognitionAt T) :
    MovedQuotientRecognitionAt T := by
  intro L D H B c hnot hmodels hlocal hfull geometry hmin
  exact h L D H B c hnot hmodels hlocal hfull geometry hmin
    (movedAction_sourceHypotheses D c geometry hmin hlocal)

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
