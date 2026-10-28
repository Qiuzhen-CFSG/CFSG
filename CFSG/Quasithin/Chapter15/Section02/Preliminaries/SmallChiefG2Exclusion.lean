module
public import Theory.SpecificGroups.G2.CoverFixedNaturalSections.ElementaryDisplacement
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallChiefDisplacement

/-!
# Excluding the first G₂ local on the actual small chief factors

The original elementary H-span has nontrivial commutator with the embedded
O²(H) in the S₅ case, and with the actual C-component in the marked-five
wreath case. A central two-cover of the first G₂ local would centralize
that span: its abelian normal core subgroups are central, and two-perfect
commutator idempotence eliminates the displacement.

Both applications retain the original H and the original subgroup K,
using only subnormality inside H. The pair consumer retains Y₁Rc as its
first factor and H as its full second parabolic. These are specific model
exclusions in F.1.12, not an exhaustive recognition theorem. They do not
assert that chief factors survive the quotient by O₂(W). The remaining
mixed-pair recognition and final 15.2.1--8 assembly stay with
qt-e-152-small-parabolic.

Source: Aschbacher--Smith 15.2.4 and 15.2.8, printed pp.1105--1110,
and the first G₂ local in F.1.12(I)(3), pp.262--263.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_twoPerfect {D : Type*} [Group D] [Finite D]
    [Group.IsPerfect D] : IsPPerfect 2 D := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (D ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (D ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- Both literal S₅ chief factors exclude a central two-cover of the first
G₂ local on the embedded residual O²(H). -/
theorem ChosenSmallSource.symmetricFive_residual_no_g2_short_cover
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)))
    (F : Type*) [Field F] [CharP F 2] [Finite F] (hq : 2 < Nat.card F) :
    let K := (pResidual 2 H).map H.subtype
    ¬ ∃ f : K →* Atlas.G2.LieParabolicSetup.local₁ (F := F),
      Function.Surjective f ∧ f.ker ≤ center K ∧ IsPGroup 2 f.ker := by
  let := h.prepared.elementary
  let K := (pResidual 2 H).map H.subtype
  dsimp only
  rintro ⟨f,hf,hc,hk⟩
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  have hnorm : (K.subgroupOf H).Normal := by
    change ((pResidual 2 H).map H.subtype).comap H.subtype |>.Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  have hz := Atlas.G2.CoverFixedNaturalSections.abelian_pgroup_commutator_eq_bot_of_subnormal_cover
    hq H K (conjugateSpan H V) (map_subtype_le _) hUH hnorm.isSubnormal
    (isPPerfect_embedded_pResidual 2 H)
    (IsElementaryAbelian.isPGroup 2 (conjugateSpan H V))
    ((map_subtype_le _).trans (conjugateSpan_normalized H V)) f hf hc hk
  have hb := (h.symmetricFive_residual_displacement hprior hH he).1
  change 256 ≤ Nat.card (⁅conjugateSpan H V,K⁆ : Subgroup G) at hb
  rw [hz,card_bot] at hb
  omega

/-- The same exclusion on every actual wreath component, before choosing
either generated-core case or passing to W/O₂(W). -/
theorem ChosenSmallSource.marked_five_wreath_component_no_g2_short_cover
    {T : Sylow 2 G} {M Mc V H K : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    (hK : K ∈ Chapter1.cComponentsIn H)
    (F : Type*) [Field F] [CharP F 2] [Finite F] (hq : 2 < Nat.card F) :
    letI := h.prepared.elementary
    ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
    DihedralMarking l 5 2 →
      ¬ ∃ f : K →* Atlas.G2.LieParabolicSetup.local₁ (F := F),
        Function.Surjective f ∧ f.ker ≤ center K ∧ IsPGroup 2 f.ker := by
  let := h.prepared.elementary
  intro l hd
  rintro ⟨f,hf,hc,hk⟩
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  let : Group.IsPerfect (K.subgroupOf H) := hK.2.perfect
  have hp : IsPPerfect 2 K := perfect_twoPerfect.of_surjective
    (subgroupOfEquivOfLe hK.1).toMonoidHom (subgroupOfEquivOfLe hK.1).surjective
  have hz := Atlas.G2.CoverFixedNaturalSections.abelian_pgroup_commutator_eq_bot_of_subnormal_cover
    hq H K (conjugateSpan H V) hK.1 hUH hK.2.subnormal hp
    (IsElementaryAbelian.isPGroup 2 (conjugateSpan H V))
    (hK.1.trans (conjugateSpan_normalized H V)) f hf hc hk
  have hb := (h.marked_five_wreath_component_displacement hH he hK l hd).1
  rw [hz,card_bot] at hb
  omega

/-- The original F.1.1 pair excludes a central two-cover of the first G₂
local at its embedded second factor, while its full second parabolic is H. -/
theorem SmallResidualWitness.symmetricFive_pair_no_g2_short_cover
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)))
    (F : Type*) [Field F] [CharP F 2] [Finite F] (hq : 2 < Nat.card F) :
    let K := (pResidual 2 H).map H.subtype
    let L := ![Y₁ ⊔ (M ⊓ Mc).pCoreIn 2,K]
    ChapterF.Source.HypothesisF11 L (T : Subgroup G) ∧
      ChapterF.Source.parabolic L (T : Subgroup G) 1 = H ∧
      ¬ ∃ f : K →* Atlas.G2.LieParabolicSetup.local₁ (F := F),
        Function.Surjective f ∧ f.ker ≤ center K ∧ IsPGroup 2 f.ker := by
  have hp := hw.symmetricFive_pair hH he
  exact ⟨hp.1,hp.2.2.1,h.symmetricFive_residual_no_g2_short_cover hprior hH he F hq⟩

end CFSG.Quasithin.Chapter15.Section02
