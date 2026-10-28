module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneComparison
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeAlignmentModel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeAlignment
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadius
public import Theory.Representation.BinaryPermutation.SixCoreEightHyperplane

/-!
# Radius escape in the original cubic plane branch

The original selected endpoint chart gives a nonzero fixed-kernel displacement
H = [F,P], where F is the fixed space of the original critical transposition.
Its residual rotation J satisfies [F,J] = [U,J] = H. The retained selector's
full-seed escape rules out control of [U,P] by H and the critical line.

Apply the shared six-letter alignment/control theorem to this literal chart.
The remaining alternative places H in the critical line plus the full fixed
central attachment. Mapping to the natural quotient kills that attachment.
The natural symplectic pairing then forces the image of J into the original
critical transposition group, so J fixes F on the entire cover. This contradicts
H ≠ 0. The argument applies to both full covers, of orders sixteen and
thirty-two, with the original projection kernel E and its nontrivial odd E/Q.
Only representation calculations from the natural branch are reused; its
replacement graph and two-core projection kernel are never identified with
the original cubic graph.

Thus no plane radius is trapped. The actual backward walks, all overlap
vertices, reverse prefixes and forward eligibility now hold on every original
critical path, with no large-image or strict-slice premise. Whole-core and
literal C.1.32 consumers remove the finite-cover obstruction. They retain the
Borel branch and terminal plane configurations: eligibility does not assert
an index greater than two, and uniformly small slices are not a trapped-radius
witness. The remaining source (5.9)--(5.12) calculations and both final core
exhaustions are still required.

The internal imports reuse the existing model exclusion proof, cover quotient
and path-iteration lemmas without changing their public boundaries.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.0), (3.3), (5.8), printed pp.859,866--867,919--920;
Aschbacher--Smith, C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
private theorem cubic_cover_aligned_fixed_eq_bot (t : S) (ht : t.IsSwap) (J : Subgroup S)
    (halign : subspaceCommutator (coverAction h e hz hk) ⊤ J ≤
      subspaceCommutator (coverAction h e hz hk) ⊤ (zpowers t) ⊔
        fixedSpace (coverAction h e hz hk) ⊤) :
    subspaceCommutator (coverAction h e hz hk)
      (fixedSpace (coverAction h e hz hk) (zpowers t)) J = ⊥ := by
  let σ := coverAction h e hz hk
  let f := coverMap h e hz hk
  have hm (B : Subgroup S) :
      (subspaceCommutator σ ⊤ B).map f =
        subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ B := by
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6)) σ
      (MonoidHom.id S) f (fun g v => (coverMap_equivariant h e hz hk g v).symm) B ⊤
    have hfr : f.range = ⊤ := LinearMap.range_eq_top.mpr (coverMap_surjective h e hz hk)
    simpa only [Submodule.map_top,hfr,map_id] using hh.symm
  have hcentral : (fixedSpace σ ⊤).map f = ⊥ := by
    apply le_bot_iff.mp
    rintro _ ⟨v,hv,rfl⟩
    have hf : Function.Injective (alternatingNaturalRepresentation (Fin 6)) := by
      intro g k he
      exact Subtype.ext (naturalRepresentation_injective (Fin 6) (by decide) he)
    apply (invariants_eq_bot_of_faithful_irreducible _ hf
      (alternatingNatural_isIrreducible (by decide : 5 ≤ Fintype.card (Fin 6)))).le
    intro g
    change naturalRepresentation (Fin 6) g.val (f v)=f v
    have hfix : σ g.val v = v := hv ⟨g.val,mem_top _⟩
    exact (coverMap_equivariant h e hz hk g.val v).symm.trans (congrArg f hfix)
  have hmove : subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ J ≤
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (zpowers t) := by
    have hh := Submodule.map_mono (f := f) halign
    rwa [Submodule.map_sup,hm,hm,hcentral,sup_bot_eq] at hh
  have hsmall : fixedCodim (naturalRepresentation (Fin 6)) (zpowers t) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coreRepresentation (Fin 6))
      (naturalRepresentation (Fin 6)) (coreToNatural (Fin 6)) coreToNatural_surjective
      (fun g v => coreToNatural_equivariant g v) (zpowers t)).trans
        (SixCoreWeightFour.swap_fixedCodim_le_one t ht)
  have hn : zpowers t ≠ ⊥ := by
    intro he
    have htone : t = 1 := mem_bot.mp (he ▸ mem_zpowers t)
    have hh := ht.orderOf
    rw [htone,orderOf_one] at hh
    cases hh
  have hJ := Natural.Exhaustion.LargeDistance.SectionFive.small_image_le_of_moved_le
    (zpowers t) J hn hsmall hmove
  exact (subspaceCommutator_eq_bot_iff σ _ J).mpr (fixedSpace_antitone σ hJ)

include h e hz hk in
/-- The finite obstruction from the original paired selector is impossible
on either permitted full cover, including its entire fixed attachment. -/
theorem not_planeCoverObstruction (u : S) : ¬ PlaneCoverObstruction h e hz hk u := by
  rintro ⟨hm,t,P,J,ht,hs,hP,_hJ,hne,hfixed,hfull,hcontrol⟩
  have hd := Natural.Exhaustion.LargeDistance.SectionFive.CubeAlignmentModel.model_dichotomy
    (coverAction h e hz hk) hm u t P
    (by simpa only [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] using hP)
    (by simpa only [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] using ht) hs
  have halign := hd.resolve_right hcontrol
  rw [←hfull] at halign
  have hh := cubic_cover_aligned_fixed_eq_bot h e hz hk t hs J halign
  exact hne (hfixed.symm.trans hh)

include h e hz hk in
/-- Every critical pair in the original plane branch has an escaping
whole radius. No strict slice is assumed. -/
theorem plane_radius_escape (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    ¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  exact not_planeCoverObstruction h e hz hk u
    (plane_radius_failure_cover_obstruction_at h e hz hk u hR p hbad)

include h e hz hk in
/-- Every original plane critical path extends backward with its entire
retained overlap. Its reverse prefix also gives forward eligibility. -/
theorem plane_critical_paths (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    (¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∧
    (∃ d, ∃ w : (cosetGraph Rg).Walk d a,
      ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
        w.length = 2 ∧ q.walk = w.append (p.walk.take (p.walk.length-2)) ∧
        ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
    (∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) d,
      q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = a) ∧
    ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
  have hb := distance_gt_two h e hz hk
  have escape := fun a z (p : CriticalPath Rg (sourceGeometry h) a z) =>
    plane_radius_escape h e hz hk u hR p
  have hprefix := reverse_prefix_of_radius_escape h e hb escape p
  refine ⟨escape _ _ p,backward_path_of_radius_escape h p (escape _ _ p) hb,hprefix,?_⟩
  obtain ⟨d,q,_,hqa⟩ := hprefix
  have hh := critical_start_not_le_second_slice h e hz hb q
  rwa [hqa] at hh

omit hk in
include h e hz in
/-- Whole-core reduction with radius trapping excluded in the original
plane branch. The Borel and the terminal path configurations remain. -/
theorem coreExhaustion_or_cubic_plane_paths :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
          (¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∧
          (∃ d, ∃ w : (cosetGraph Rg).Walk d a,
            ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
              w.length = 2 ∧ q.walk = w.append (p.walk.take (p.walk.length-2)) ∧
              ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          (∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) d,
            q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = a) ∧
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _))) := by
  rcases coreExhaustion_or_cubic_plane_cover_obstruction h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,hpaths | hobs⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,hpaths⟩⟩
  · exact False.elim (not_planeCoverObstruction h e hz hk u hobs)

omit hk in
include h e hz in
/-- Literal C.1.32 consumer retaining both full covers, the full extension
kernel, the Borel alternative and the original nontrapped plane paths. -/
theorem rankTwo_or_cubic_plane_paths :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
          (¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∧
          (∃ d, ∃ w : (cosetGraph Rg).Walk d a,
            ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
              w.length = 2 ∧ q.walk = w.append (p.walk.take (p.walk.length-2)) ∧
              ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          (∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) d,
            q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = a) ∧
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _))) :=
  (coreExhaustion_or_cubic_plane_paths h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
