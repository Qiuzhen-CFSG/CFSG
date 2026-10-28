module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.Classification
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Transport
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Transport

/-!
# The embedded point-local natural action

Transport the explicit symplectic point-local extension through the original
marking. Its center maps to the original long root. Self-centralization of
its two-core identifies the exact kernel of the restriction of N → N/C_N(U).
The induced isomorphism of its image with SL2 retains that quotient map.

The final identity identifies conjugation on the actual O2(J)/Z(J) with the
natural action of this image. Together with the center-to-root equality it
supplies the embedded O2(J)/root comparison required in the source argument;
it does not identify the larger K_Z image with J's image.

Source: Aschbacher–Smith 4.3.6, p.615; the point-local calculation F.1.12(I)(2).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (m : OrdinarySymplecticMarking c n)

def pointLocalMark (hn : 1 < n) : pointLocal (F := m.Field) ≃* m.second :=
  ((pointLocal (F := m.Field)).equivMapOfInjective m.modelEmbedding
    m.modelEmbedding_injective).trans (MulEquiv.subgroupCongr (m.pointLocal_image hn))

/-- The natural extension is transported along the original symplectic embedding. -/
def secondNaturalExtension (hn : 1 < n) :
    NaturalExtension (F := m.Field) (pCore 2 m.second) := by
  let d := (pointNaturalExtension m.card hn).comap (pointLocalMark m hn).symm
  have he : (pointRadical (F := m.Field)).comap (pointLocalMark m hn).symm.toMonoidHom =
      pCore 2 m.second := by
    rw [comap_equiv_eq_map_symm', ← pointLocal_core_eq m.card hn]
    exact pCore_map_iso 2 (pointLocalMark m hn)
  simpa only [he] using d

theorem second_center_eq_root (hn : 1 < n) :
    (center m.second).map m.second.subtype = m.root := by
  have he := PointRadicalAction.map_embedded_center (pointLocal (F := m.Field))
    m.modelEmbedding m.modelEmbedding_injective
  rw [m.pointLocal_image hn, PointRadicalAction.center_eq_root m.card hn, m.root_image] at he
  exact he.symm

/-- The embedded point local has precisely its two-core as action kernel. -/
theorem second_projection_kernel (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan) :
    (secondaryProjection m m.second m.second_le_rootNormalizer).ker = pCore 2 m.second := by
  let d := secondNaturalExtension m hn
  apply le_antisymm
  · intro j hj
    have hker : (inclusion m.second_le_rootNormalizer j) ∈ (projection m).ker :=
      congrArg Subtype.val hj
    rw [projection_kernel m hUN] at hker
    rw [←d.centralizer_eq]
    intro r hr'
    exact Subtype.ext (hker r (hcore (mem_map_of_mem m.second.subtype hr')))
  · intro j hj
    apply Subtype.ext
    have hm : projection m (inclusion m.second_le_rootNormalizer j) ∈ image m m.rootCore :=
      mem_map_of_mem _ (hcore.trans (span_le_core m hr hUN)
        (mem_map_of_mem m.second.subtype hj))
    exact (core_image_eq_bot m hr ▸ hm : _ ∈ (⊥ : Subgroup (Actor m)))

/-- The actual point-local action image, marked by its original quotient map. -/
def secondImageEquiv (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan) :
    image m m.second ≃* Matrix.SpecialLinearGroup (Fin 2) m.Field :=
  (QuotientGroup.liftEquiv (pCore 2 m.second)
    (secondaryProjection_surjective m m.second m.second_le_rootNormalizer)
    (second_projection_kernel m hn hr hUN hcore).symm).symm.trans
  (QuotientGroup.liftEquiv (pCore 2 m.second) (secondNaturalExtension m hn).surjective
    (secondNaturalExtension m hn).kernel.symm)

theorem secondImageEquiv_apply (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (j : m.second) :
    secondImageEquiv m hn hr hUN hcore
      (secondaryProjection m m.second m.second_le_rootNormalizer j) =
      (secondNaturalExtension m hn).projection j := by
  let e := QuotientGroup.liftEquiv (pCore 2 m.second)
    (secondaryProjection_surjective m m.second m.second_le_rootNormalizer)
    (second_projection_kernel m hn hr hUN hcore).symm
  change (QuotientGroup.liftEquiv (pCore 2 m.second) (secondNaturalExtension m hn).surjective
    (secondNaturalExtension m hn).kernel.symm)
    (e.symm (e (QuotientGroup.mk' (pCore 2 m.second) j))) = _
  rw [e.symm_apply_apply]
  rfl

/-- Conjugation on the literal two-core modulo its center is the natural
module for the actual action image. The preceding center identity identifies
this central subgroup with the original root. -/
theorem second_image_natural_action (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (j : m.second) (u : pCore 2 m.second) :
    let d := secondNaturalExtension m hn
    (d.moduleIso (QuotientGroup.mk' ((center m.second).subgroupOf (pCore 2 m.second))
      (extensionConjugate (pCore 2 m.second) j u))).toAdd =
    Matrix.mulVec (secondImageEquiv m hn hr hUN hcore
      (secondaryProjection m m.second m.second_le_rootNormalizer j)).val
      (d.moduleIso (QuotientGroup.mk' ((center m.second).subgroupOf (pCore 2 m.second)) u)).toAdd := by
  dsimp only
  rw [secondImageEquiv_apply]
  exact (secondNaturalExtension m hn).intertwining j u

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
