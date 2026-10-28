module
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneComparison
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneEscape
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelThompson
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeAlignment
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.PredecessorResidual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePredecessor

/-!
# The Borel comparison at two small end slices

A residual-shifted path has its reversed second predecessor at the original
base. The forward Baumann bound therefore forces both shifted images to have
order two. Its full reverse-kernel commutator is the same noncentral moving
line at the old endpoint. Paired selectors supply a nonzero commutator from
eligibility, without assuming failure of central generation.

For equal starting Thompson movers, the reverse-kernel commutator lies in
the starting seed. On the literal endpoint cover the selected seed image is
elementary abelian and commutes with the critical transposition. A small
Borel certificate puts both in either the plane core or point core. The
plane alignment/control theorem and the natural point-core displacement
bound exclude the residual rotation in both cases. The unrestricted Borel
alignment/control claim would be false; the actual elementary seed and
commutation hypotheses are essential here.

Thus a trapped neighbor has endpoint commutator in the starting seed under
the two small end-slice bounds and equal starting movers. Eligible paired
selectors cannot both be trapped under those same hypotheses. Both full
moving covers, all central attachments, the original graph and its cubic
kernel E are retained. The literal OriginalSylowExceptional applications
use these results on c.L,d.S.

Central-generation escape without these local slice/mover assumptions,
strict forward estimates and terminal distance exclusions remain necessary
for whole-core exhaustion. No final reconstruction is asserted here.

The internal imports reuse exact cover calculations, charts and subgroup
transport from the neighboring exceptional development. The natural branch
contributes only its model calculation; no replacement graph is identified
with the original graph.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the predecessor and residual comparison of (5.8), printed p.920;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R


include h e hz hk in
/-- Both literal end-slice bounds force the residual shift to have image
order two in both directions. The same full kernel gives its moving line. -/
theorem two_slice_residual_line
    {a z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hforward : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    (hpre : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≠ ⊥) :
    ∃ k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)),
      act Rg k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3) ∧
    ∃ q : CriticalPath Rg (sourceGeometry h) c (act Rg k z),
      q.walk.getVert 1 = t ∧
      (∀ i ≤ p.walk.length-3, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      (Q Rg (act Rg k z)).relIndex (Z Rg c) = 2 ∧
      (Q Rg c).relIndex (Z Rg (act Rg k z)) = 2 ∧
      Nat.card (⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅Z Rg z ⊓ Q Rg a,Z Rg (act Rg k⁻¹ c)⁆ = ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ∧
      ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ = ⁅U Rg z,Z Rg (act Rg k⁻¹ c)⁆ ∧
      ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≤
        centralizer (Ltilde Rg (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam Rg)) ∧
      ¬ ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≤
        centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
  obtain ⟨k,hkm,hkt,q,hq1,hqverts,htransport,hcentral,halt⟩ :=
    predecessor_nonzero_residual_shift h e hz hk p hpre hat hct hbad hne
  have hb := distance_gt_two h e hz hk
  have hq2 : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hqverts 0 (Nat.zero_le _)
  let qr : CriticalPath Rg (sourceGeometry h) (act Rg k z) c :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      c q.start_color (by
        rw [(sourceGeometry h).distance_constant c q.start_color]
        exact sourceDistance_pos h) (act Rg k z) q.end_color q.critical⟩
  have hqrpre : qr.walk.getVert (qr.walk.length-2) = a := by
    change q.walk.reverse.getVert (q.walk.reverse.length-2) = a
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,
      show q.walk.length-(q.walk.length-2)=2 by
        have hh : q.walk.length = sourceDistance h := q.length_eq_b
        omega,hq2]
  have hs := critical_predecessor_small_slice h e hz hk hb qr
    (by simpa only [hqrpre] using hforward)
  have hsmall : (Q Rg (act Rg k z)).relIndex (Z Rg c) = 2 := hs.2.1
  rcases halt with hlarge | ⟨hcard,hmove,hnon⟩
  · omega
  exact ⟨k,hkm,hkt,q,hq1,hqverts,hsmall,hs.2.2,hcard,htransport,hmove,hcentral,hnon⟩

open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- Eligible paired Borel selectors force an escaping full endpoint
commutator, using their proper index-two mover. -/
theorem borel_paired_eligible_endpoint_escape
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hel : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    ¬ ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg (alpha Rg) ∨
      ¬ ⁅Z Rg c,Z Rg z'⁆ ≤ Z Rg (alpha Rg) := by
  by_contra! hboth
  obtain ⟨hcomm,hcomm'⟩ := hboth
  have hb := distance_gt_two h e hz hk
  have hd : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    have hh := (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := alpha Rg)
    omega
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hd)
  let Y := Z Rg c ⊔ Z Rg (alpha Rg)
  have hmove {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hm : ⁅Z Rg c,Z Rg w⁆ ≤ Z Rg (alpha Rg)) :
      ⁅Y,Z Rg w⁆ ≤ Z Rg (alpha Rg) := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      (Z Rg c) (Z Rg (alpha Rg)) (Z Rg w) (Z Rg (alpha Rg))
      (Z_normalized Rg _) (hZV.trans ((sourceGeometry h).V_local _ rfl hb))
      (Z_le_stabilizer Rg _) hm
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
        (sourceDistance_pos h) r.critical).trans (Z_normalized Rg _))
  have hpY := hmove p hcomm
  have hqY := hmove q hcomm'
  have hYN : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ (le_normalizer_iff_commutator_le_left.mpr
      (hpY.trans le_sup_right))) (le_normalizer_iff_commutator_le_left.mpr
        (hqY.trans le_sup_right))
    apply le_trans (remaining_edge_thompson h e hz hk u (Or.inr hR) rfl hat).2.2.1
    exact (le_inf ((show Q Rg t ≤ stabilizer Rg c from
      fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg c))
      ((show Q Rg t ≤ stabilizer Rg (alpha Rg) from
        fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hUB : U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    (DistanceEight.U_le_Z Rg c).trans (le_sup_left.trans
      (normalized_radius_le_slice_of_critical_commutator h e hz hb p Y
        (sup_le hZV (Z_le_VBall Rg _ 2)) hYN hpY))
  exact hel hUB

include h e hz hk in
/-- A trapped Borel paired selector with small forward and predecessor
slices produces a noncentral residual line on one actual selected path.
No central-generation or mover-comparison assumption is used. -/
theorem borel_paired_two_slice_line
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hel : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (hforward : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    (hpre : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2)
    (hpre' : (B Rg (q.walk.getVert (q.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z') ≤ 2)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))) :
    ∃ w, ∃ r : CriticalPath Rg (sourceGeometry h) (alpha Rg) w,
      ((∀ i, r.walk.getVert i = p.walk.getVert i) ∨
        (∀ i, r.walk.getVert i = q.walk.getVert i)) ∧
      ¬ ⁅Z Rg c,Z Rg w⁆ ≤ Z Rg (alpha Rg) ∧
      ∃ k ∈ Ltilde Rg (r.walk.getVert (r.walk.length-2)),
        act Rg k (r.walk.getVert (r.walk.length-1)) = r.walk.getVert (r.walk.length-3) ∧
      ∃ b : CriticalPath Rg (sourceGeometry h) c (act Rg k w),
        b.walk.getVert 1 = t ∧
        (∀ i ≤ r.walk.length-3, b.walk.getVert (i+2) = r.walk.getVert i) ∧
        (Q Rg (act Rg k w)).relIndex (Z Rg c) = 2 ∧
        (Q Rg c).relIndex (Z Rg (act Rg k w)) = 2 ∧
        Nat.card (⁅Z Rg w ⊓ Q Rg (alpha Rg),Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
        ⁅Z Rg w ⊓ Q Rg (alpha Rg),Z Rg (act Rg k⁻¹ c)⁆ = ⁅Z Rg w ⊓ Q Rg (alpha Rg),Z Rg c⁆ ∧
        ⁅Z Rg w ⊓ Q Rg (alpha Rg),Z Rg c⁆ = ⁅U Rg w,Z Rg (act Rg k⁻¹ c)⁆ ∧
        ⁅Z Rg w ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
          centralizer (Ltilde Rg (r.walk.getVert (r.walk.length-2)) : Set (FreeAmalgam Rg)) ∧
        ¬ ⁅Z Rg w ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
          centralizer (stabilizer Rg w : Set (FreeAmalgam Rg)) := by
  have hb := distance_gt_two h e hz hk
  have finish {w : Vertex Rg} (r : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hpre : (B Rg (r.walk.getVert (r.walk.length-2))
        ((sourceGeometry h).Z_normal _)).relIndex (U Rg w) ≤ 2)
      (hbad : Z Rg c ≤ Q Rg (r.walk.getVert (r.walk.length-2)))
      (hn : ¬ ⁅Z Rg c,Z Rg w⁆ ≤ Z Rg (alpha Rg)) :
      ⁅Z Rg w ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≠ ⊥ := by
    intro he
    have hs : (Q Rg w).relIndex (Z Rg (alpha Rg)) < 4 := by
      rw [(critical_predecessor_small_slice h e hz hk hb r hpre).2.2]
      decide
    rw [commutator_comm] at he
    exact hn (small_critical_predecessor_commutator h e hz hk hb r hs
      (Z Rg c) hbad (commutator_eq_bot_iff_le_centralizer.mp he))
  rcases borel_paired_eligible_endpoint_escape h e hz hk u hR p q hat hct hgen hel with hn | hn
  · exact ⟨z,p,Or.inl (fun _ => rfl),hn,
      two_slice_residual_line h e hz hk p hforward hpre hat hct hbad (finish p hpre hbad hn)⟩
  · exact ⟨z',q,Or.inr (fun _ => rfl),hn,
      two_slice_residual_line h e hz hk q hforward hpre' hat hct hbad' (finish q hpre' hbad' hn)⟩


open Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative
local notation "borel" => Theory.SpecificGroups.SymmetricSix.borel
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders.Six

private def pointWord (j : Fin 8) : S :=
  PointCoreGeneration.coreWords.get ⟨j.val,by change j.val < 8; exact j.isLt⟩

private theorem borel_elementary_pair (P : Subgroup S)
    (hP : P ≤ borel) (h2 : ∀ g ∈ P, g^2=1)
    (hab : ∀ g ∈ P, ∀ k ∈ P, Commute g k)
    (t : S) (ht : t ∈ borel) (hs : t.IsSwap)
    (hc : ∀ g ∈ P, Commute t g) :
    (P ≤ D ∧ t ∈ D) ∨
      (P ≤ pointCore.map (MulAut.conj flagRelabel).toMonoidHom ∧
        t ∈ pointCore.map (MulAut.conj flagRelabel).toMonoidHom) := by
  have cert : ∀ i j : Fin 16,
      (BorelCalculation.words i)^2=1 →
      (∀ k : Fin 8, dWords k ≠ BorelCalculation.words i) →
      (BorelCalculation.words j)^2=1 →
      Commute (BorelCalculation.words i) (BorelCalculation.words j) →
      ∃ k : Fin 8, (MulAut.conj flagRelabel) (pointWord k) = BorelCalculation.words j := by
    unfold Commute SemiconjBy
    decide +kernel
  have swap_plane : ∀ i : Fin 16, (BorelCalculation.words i).cycleType={2} →
      ∃ k : Fin 8, dWords k = BorelCalculation.words i := by decide +kernel
  have wordD (j : Fin 8) : dWords j ∈ D := by
    rw [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq]
    exact (CFSG.Quasithin.ChapterB.Offenders.Six.mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨j,rfl⟩
  by_cases hD : P ≤ D
  · left
    obtain ⟨i,rfl⟩ := BorelCalculation.words_complete t ht
    obtain ⟨j,hj⟩ := swap_plane i (Equiv.Perm.isSwap_iff_cycleType.mp hs)
    exact ⟨hD,hj ▸ wordD j⟩
  right
  obtain ⟨g,hg,hgn⟩ := SetLike.not_le_iff_exists.mp hD
  obtain ⟨i,hi⟩ := BorelCalculation.words_complete g (hP hg)
  have hi2 : (BorelCalculation.words i)^2=1 := hi ▸ h2 g hg
  have hin : ∀ k : Fin 8, dWords k ≠ BorelCalculation.words i := by
    intro k he
    exact hgn (hi ▸ he ▸ wordD k)
  have hpoint (k : S) (hk : k ∈ borel) (hk2 : k^2=1) (hcomm : Commute g k) :
      k ∈ pointCore.map (MulAut.conj flagRelabel).toMonoidHom := by
    obtain ⟨j,hj⟩ := BorelCalculation.words_complete k hk
    obtain ⟨v,he⟩ := cert i j hi2 hin (hj ▸ hk2) (by rwa [hi,hj])
    exact ⟨pointWord v,PointCoreGeneration.core_word_mem (List.get_mem _ _),he.trans hj⟩
  refine ⟨fun k hk => hpoint k (hP hk) (h2 k hk) (hab g hg k hk),?_⟩
  exact hpoint t ht (by obtain ⟨i,j,hij,rfl⟩ := hs; rw [pow_two,Equiv.swap_mul_self]) (hc g hg).symm

local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
private theorem point_fixed_displacement_excludes_rotation
    (u t : S) (hs : t.IsSwap)
    (ht : t ∈ pointCore.map (MulAut.conj u).toMonoidHom)
    (P J : Subgroup S) (hP : P ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hne : subspaceCommutator (coverAction h e hz hk)
      (fixedSpace (coverAction h e hz hk) (zpowers t)) P ≠ ⊥)
    (hfixed : subspaceCommutator (coverAction h e hz hk)
        (fixedSpace (coverAction h e hz hk) (zpowers t)) J =
      subspaceCommutator (coverAction h e hz hk)
        (fixedSpace (coverAction h e hz hk) (zpowers t)) P)
    (hfull : subspaceCommutator (coverAction h e hz hk) ⊤ J =
      subspaceCommutator (coverAction h e hz hk)
        (fixedSpace (coverAction h e hz hk) (zpowers t)) P) : False := by
  let σ := coverAction h e hz hk
  let f := coverMap h e hz hk
  let F := fixedSpace σ (zpowers t)
  let H := subspaceCommutator σ F P
  have hm (A : Subgroup S) :
      (subspaceCommutator σ ⊤ A).map f =
        subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A := by
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6)) σ
      (MonoidHom.id S) f (fun g v => (coverMap_equivariant h e hz hk g v).symm) A ⊤
    have hfr : f.range = ⊤ := LinearMap.range_eq_top.mpr (coverMap_surjective h e hz hk)
    simpa only [Submodule.map_top,hfr,map_id] using hh.symm
  have hF : F.map f ≤ fixedSpace (naturalRepresentation (Fin 6)) (zpowers t) := by
    rintro _ ⟨v,hv,rfl⟩
    intro g
    change naturalRepresentation (Fin 6) g.val (f v) = f v
    rw [←coverMap_equivariant h e hz hk]
    exact congrArg f (hv g)
  have hH : H.map f ≤ subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (zpowers t) := by
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6)) σ
      (MonoidHom.id S) f (fun g v => (coverMap_equivariant h e hz hk g v).symm) P F
    have he : H.map f = subspaceCommutator (naturalRepresentation (Fin 6)) (F.map f) P := by
      simpa only [map_id] using hh.symm
    rw [he]
    apply le_trans _ (PointCoreTranspositionFixed.fixed_displacement_le u t ht hs)
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact Submodule.subset_span ⟨g,hP hg,v,hF hv,rfl⟩
  have hmove : subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ J ≤
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (zpowers t) := by
    rw [←hm J,hfull]
    exact hH
  have hsmall : fixedCodim (naturalRepresentation (Fin 6)) (zpowers t) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coreRepresentation (Fin 6))
      (naturalRepresentation (Fin 6)) (coreToNatural (Fin 6)) coreToNatural_surjective
      (fun g v => coreToNatural_equivariant g v) (zpowers t)).trans
        (SixCoreWeightFour.swap_fixedCodim_le_one t hs)
  have hn : zpowers t ≠ ⊥ := by
    intro he
    have htone : t = 1 := mem_bot.mp (he ▸ mem_zpowers t)
    have hh := hs.orderOf
    rw [htone,orderOf_one] at hh
    cases hh
  have hJ := Natural.Exhaustion.LargeDistance.SectionFive.small_image_le_of_moved_le
    (zpowers t) J hn hsmall hmove
  have hzJ : subspaceCommutator σ F J = ⊥ :=
    (subspaceCommutator_eq_bot_iff σ F J).mpr (fixedSpace_antitone σ hJ)
  exact hne (hfixed.symm.trans hzJ)

include h e hz hk in
/-- The Borel comparison retains the elementary seed actor and its
commutation with the original critical transposition. These source facts
exclude the unrestricted Borel counterexample. -/
private theorem borel_cover_rotation_false
    (u t : S) (ht : t ∈ borel.map (MulAut.conj u).toMonoidHom) (hs : t.IsSwap)
    (P J : Subgroup S) (hP : P ≤ borel.map (MulAut.conj u).toMonoidHom)
    (h2 : ∀ g ∈ P, g^2=1) (hab : ∀ g ∈ P, ∀ k ∈ P, Commute g k)
    (hc : ∀ g ∈ P, Commute t g)
    (hne : subspaceCommutator (coverAction h e hz hk)
      (fixedSpace (coverAction h e hz hk) (zpowers t)) P ≠ ⊥)
    (hfixed : subspaceCommutator (coverAction h e hz hk)
        (fixedSpace (coverAction h e hz hk) (zpowers t)) J =
      subspaceCommutator (coverAction h e hz hk)
        (fixedSpace (coverAction h e hz hk) (zpowers t)) P)
    (hfull : subspaceCommutator (coverAction h e hz hk) ⊤ J =
      subspaceCommutator (coverAction h e hz hk)
        (fixedSpace (coverAction h e hz hk) (zpowers t)) P)
    (hcontrol : ¬ subspaceCommutator (coverAction h e hz hk) ⊤ P ≤
      subspaceCommutator (coverAction h e hz hk)
        (fixedSpace (coverAction h e hz hk) (zpowers t)) P ⊔
      subspaceCommutator (coverAction h e hz hk) ⊤ (zpowers t)) : False := by
  let f := (MulAut.conj u).toMonoidHom
  obtain ⟨t₀,ht₀,rfl⟩ := ht
  have hs₀ : t₀.IsSwap := by
    have hh : IsConj t₀ ((MulAut.conj u) t₀) := isConj_iff.mpr ⟨u,rfl⟩
    exact Equiv.Perm.isSwap_iff_cycleType.mpr
      ((Equiv.Perm.isConj_iff_cycleType_eq.mp hh).trans (Equiv.Perm.isSwap_iff_cycleType.mp hs))
  let P₀ := P.comap f
  have hm : P₀.map f = P := map_comap_eq_self_of_surjective (MulAut.conj u).surjective P
  have hP₀ : P₀ ≤ borel := by
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj u).injective).mp
    rw [hm]
    exact hP
  have hi : Function.Injective f := (MulAut.conj u).injective
  have h2₀ : ∀ g ∈ P₀, g^2=1 := by
    intro g hg
    apply hi
    simpa only [map_pow,map_one] using h2 (f g) hg
  have hab₀ : ∀ g ∈ P₀, ∀ k ∈ P₀, Commute g k := by
    intro g hg k hk
    change _ * _ = _ * _
    apply hi
    simpa only [map_mul] using (hab (f g) hg (f k) hk).eq
  have hc₀ : ∀ g ∈ P₀, Commute t₀ g := by
    intro g hg
    change _ * _ = _ * _
    apply hi
    simpa only [map_mul] using (hc (f g) hg).eq
  rcases borel_elementary_pair P₀ hP₀ h2₀ hab₀ t₀ ht₀ hs₀ hc₀ with ⟨hD,htD⟩ | ⟨hpoint,htpoint⟩
  · have hDP : P ≤ D.map f := hm ▸ map_mono hD
    have htD' : (MulAut.conj u) t₀ ∈ D.map f := mem_map_of_mem f htD
    have hd := Natural.Exhaustion.LargeDistance.SectionFive.CubeAlignmentModel.model_dichotomy
      (coverAction h e hz hk) (moved_subgroup_cover_model h e hz hk) u ((MulAut.conj u) t₀) P
      (by simpa only [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] using hDP)
      (by simpa only [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] using htD') hs
    have ha := hd.resolve_right hcontrol
    have halign : subspaceCommutator (coverAction h e hz hk) ⊤ J ≤
        subspaceCommutator (coverAction h e hz hk) ⊤ (zpowers ((MulAut.conj u) t₀)) ⊔
          fixedSpace (coverAction h e hz hk) ⊤ := hfull.trans_le ha
    exact hne (hfixed.symm.trans (cubic_cover_aligned_fixed_eq_bot h e hz hk _ hs J halign))
  · have he : (pointCore.map (MulAut.conj flagRelabel).toMonoidHom).map f =
        pointCore.map (MulAut.conj (u*flagRelabel)).toMonoidHom := by
      rw [map_map]
      apply congrArg (Subgroup.map · pointCore)
      apply MonoidHom.ext
      intro g
      change u*(flagRelabel*g*flagRelabel⁻¹)*u⁻¹ = (u*flagRelabel)*g*(u*flagRelabel)⁻¹
      group
    exact point_fixed_displacement_excludes_rotation h e hz hk (u*flagRelabel) _ hs
      (he ▸ mem_map_of_mem f htpoint) P J (he ▸ hm ▸ map_mono hpoint) hne hfixed hfull

open Representation.NormalElementaryQuotient
open scoped commutatorElement Pointwise

include h e hz hk in
private theorem borel_predecessor_cover_chart
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (T : Subgroup (FreeAmalgam Rg))
    (hT : T ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (k : FreeAmalgam Rg) (hkm : k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2))) :
    let := h.relative_normal
    ∃ i : M →* FreeAmalgam Rg, Function.Injective i ∧
      i.range = stabilizer Rg z ∧
      (Rg).map i = Q Rg (p.walk.getVert (p.walk.length-1)) ∧
      (pCore 2 M).map i = Q Rg z ∧ (W₀).map i = U Rg z ∧
      let A := (Z Rg a).comap i
      let P := T.comap i
      let J := (T.map (MulAut.conj k).toMonoidHom).comap i
      A.map i = Z Rg a ∧ P.map i = T ∧
      J.map i = T.map (MulAut.conj k).toMonoidHom ∧
      A ≤ Rg ∧ P ≤ Rg ∧ J ≤ Rg ∧
      A.map π ≤ borel.map (MulAut.conj u).toMonoidHom ∧
      P.map π ≤ borel.map (MulAut.conj u).toMonoidHom ∧
      J.map π ≤ borel.map (MulAut.conj u).toMonoidHom ∧
      (W₀ ⊓ centralizer (A : Set M)).map i = U Rg z ⊓ Q Rg a ∧
      ∀ v : Additive W₀,
        v ∈ fixedSpace (NormalElementaryQuotient.representation W₀ π
          (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)) (A.map π) ↔
          i v.toMul ∈ Q Rg a := by
  let := h.relative_normal
  have hb := distance_gt_two h e hz hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let t := p.walk.getVert (p.walk.length-1)
  have hzt : Adjacent Rg z t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hpre : Adjacent Rg (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hpred := Q_le_adjacent_h Rg ht hpre
  have hAt : Z Rg a ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-1 < sourceDistance h
    omega
  have hJ : T.map (MulAut.conj k).toMonoidHom ≤
      Q Rg (p.walk.getVert (p.walk.length-2)) := by
    apply (map_mono hT).trans_eq
    exact mem_normalizer_iff_map_conj_eq.mp
      ((Q_normalized Rg _) (Ltilde_le_stabilizer _ hkm))
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := remaining_edge_coordinates h e hz p.end_color hzt
  have inside (B : Subgroup (FreeAmalgam Rg)) (hB : B ≤ Q Rg t) :
      (B.comap i).map i = B ∧ B.comap i ≤ Rg := by
    have hmap : (B.comap i).map i = B :=
      map_comap_eq_self (hB.trans (hiR ▸ map_le_range i _))
    refine ⟨hmap,?_⟩
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmap,hiR]
  obtain ⟨hA,hAr⟩ := inside _ hAt
  obtain ⟨hP,hPr⟩ := inside _ (hT.trans hpred)
  obtain ⟨hJmap,hJr⟩ := inside _ (hJ.trans hpred)
  have hfixed : (W₀ ⊓ centralizer ((Z Rg a).comap i : Set M)).map i = U Rg z ⊓ Q Rg a := by
    rw [←map_inf_centralizer_of_injective i hi,hiU,hA,
      ←critical_moving_kernel_eq_fixed h e p]
  refine ⟨i,hi,hir,hiR,hiQ,hiU,hA,hP,hJmap,hAr,hPr,hJr,
    (map_mono hAr).trans_eq hR,(map_mono hPr).trans_eq hR,
    (map_mono hJr).trans_eq hR,hfixed,?_⟩
  intro v
  rw [NormalElementaryQuotient.mem_fixedSpace_image W₀ π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)]
  constructor
  · intro hv
    have hh : i v.toMul ∈ (W₀ ⊓ centralizer ((Z Rg a).comap i : Set M)).map i :=
      mem_map_of_mem i (show (v.toMul : M) ∈ W₀ ⊓ centralizer ((Z Rg a).comap i : Set M) from ⟨v.toMul.property,hv⟩)
    rw [hfixed] at hh
    exact hh.2
  · intro hv
    have hU : i v.toMul ∈ U Rg z := hiU ▸ mem_map_of_mem i v.toMul.property
    have hh : i v.toMul ∈ (W₀ ⊓ centralizer ((Z Rg a).comap i : Set M)).map i :=
      hfixed ▸ ⟨hU,hv⟩
    obtain ⟨w,hw,he⟩ := hh
    exact (hi he) ▸ hw.2

include h e hz hk in
/-- With equal starting movers, both small end slices force a trapped
neighbor's full endpoint commutator into the starting seed. The proper
Borel mover, full kernels and both moving covers are retained. -/
theorem borel_equal_mover_two_slice_endpoint_control
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (heq : edgeOffenderJoin a t = edgeOffenderJoin c t)
    (hforward : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    (hpre : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg a := by
  by_contra hescape
  have hb := distance_gt_two h e hz hk
  have hs : (Q Rg z).relIndex (Z Rg a) < 4 := by
    rw [(critical_predecessor_small_slice h e hz hk hb p hpre).2.2]
    decide
  have hc : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    rw [p.start_color] at h1
    cases hh : color Rg c <;> cases hh' : color Rg t <;> simp_all
  have hH : ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≤ Z Rg a := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans
      ((borel_equal_thompson_core_commutator h e hz hk u hR p hs hc hat hct heq).1.trans inf_le_left)
  have hne : ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≠ ⊥ := by
    intro hh
    rw [commutator_comm] at hh
    exact hescape (small_critical_predecessor_commutator h e hz hk hb p hs
      (Z Rg c) hbad (commutator_eq_bot_iff_le_centralizer.mp hh))
  obtain ⟨k,hkm,hkt,q,hq1,hqverts,hqi,hqir,hcard,htrans,hmove,hcentral,hnon⟩ :=
    two_slice_residual_line h e hz hk p hforward hpre hat hct hbad hne
  have hJ : Z Rg (act Rg k⁻¹ c) ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    rw [Z_act,inv_inv]
    apply (map_mono hbad).trans_eq
    exact mem_normalizer_iff_map_conj_eq.mp
      ((Q_normalized Rg _) (Ltilde_le_stabilizer _ hkm))
  have hfixed : ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),Z Rg c⁆ =
      ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ := by
    rw [←critical_moving_kernel_eq_fixed h e p]
    exact ((critical_kernel_predecessor_moving h e hz hb p).2.2 _ hbad).symm
  have hfixedJ : ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),Z Rg (act Rg k⁻¹ c)⁆ =
      ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ := by
    rw [←critical_moving_kernel_eq_fixed h e p]
    exact ((critical_kernel_predecessor_moving h e hz hb p).2.2 _ hJ).symm.trans htrans
  have hcontrol : ¬ ⁅U Rg z,Z Rg c⁆ ≤
      ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),Z Rg c⁆ ⊔ ⁅U Rg z,Z Rg a⁆ := by
    intro hh
    apply hescape
    rw [commutator_comm,critical_predecessor_seed_movement h e hz hb p _ hbad]
    rw [hfixed] at hh
    exact hh.trans (sup_le hH (by
      rw [commutator_comm]
      exact (commutator_mono le_rfl (DistanceEight.U_le_Z Rg z)).trans
        (critical_seed_commutator_le h p)))
  let := h.relative_normal
  obtain ⟨i,hi,hir,hiR,hiQ,hiU,hA,hP,hJmap,hAr,hPr,hJr,hApi,hPpi,hJpi,hFi,hfix⟩ :=
    borel_predecessor_cover_chart h e hz hk u hR p (Z Rg c) hbad k hkm
  have hZ : (Z Rg c).map (MulAut.conj k).toMonoidHom = Z Rg (act Rg k⁻¹ c) := by
    rw [Z_act,inv_inv]
  rw [hZ] at hJmap
  obtain ⟨⟨τ,hτ,hτswap,hτeq⟩,hcrit⟩ :=
    plane_small_critical_chart_actor h e hz hk p hs i hi hiQ hiU hA hAr
  have hobs := plane_cover_commutator_obstruction h e hz hk k i hi hiU hA hP hJmap
    hne hfixed hfixedJ hmove.symm hcontrol
  let A := (Z Rg a).comap i
  let P := (Z Rg c).comap i
  let J := (Z Rg (act Rg k⁻¹ c)).comap i
  have hZcX := (sourceGeometry h).omega_bound c hc (by
    rw [(sourceGeometry h).distance_constant c hc]
    exact sourceDistance_pos h)
  have h2 : ∀ g ∈ P.map π, g^2=1 := by
    rintro _ ⟨g,hg,rfl⟩
    rw [←map_pow]
    have hg2 : g^2=1 := by
      apply hi
      simpa only [map_pow,map_one] using (mem_omegaCenter_iff.mp (hZcX hg)).2.1
    rw [hg2,map_one]
  have hab : ∀ g ∈ P.map π, ∀ k ∈ P.map π, Commute g k := by
    rintro _ ⟨g,hg,rfl⟩ _ ⟨j,hj,rfl⟩
    change _ * _ = _ * _
    rw [←map_mul,←map_mul]
    congr 1
    apply hi
    simp only [map_mul]
    exact ((mem_omegaCenter_iff.mp (hZcX hg)).2.2 (i j)
      (omegaCenter_le _ (hZcX hj))).symm
  have hPcQ : Z Rg c ≤ Q Rg a :=
    ((Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct))).trans
        ((sourceGeometry h).V_le_Q hb a p.start_color)
  have hcomm : ∀ g ∈ P.map π, Commute τ g := by
    obtain ⟨j,hj,hje⟩ := hτ
    rintro _ ⟨g,hg,rfl⟩
    rw [←hje]
    change _ * _ = _ * _
    rw [←map_mul,←map_mul]
    congr 1
    apply hi
    simp only [map_mul]
    exact (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)
      hj (i g) (hPcQ hg)).symm
  obtain ⟨hobs1,hobs2,hobs3,hobs4⟩ := hobs
  apply borel_cover_rotation_false h e hz hk u τ (hApi hτ) hτswap
    (P.map π) (J.map π) hPpi h2 hab hcomm
  · simpa only [hτeq] using hobs1
  · simpa only [hτeq] using hobs2
  · simpa only [hτeq] using hobs3
  · simpa only [hτeq] using hobs4


include h e hz hk in
/-- Eligible paired endpoints with a common Borel mover cannot both be
trapped when their actual forward and predecessor slices are small. -/
theorem borel_equal_mover_paired_two_slice_escape
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (heq : edgeOffenderJoin (alpha Rg) t = edgeOffenderJoin c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hel : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (hforward : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    (hpre : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2)
    (hpre' : (B Rg (q.walk.getVert (q.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z') ≤ 2) :
    ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) ∨
      ¬ Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)) := by
  by_contra! hboth
  rcases borel_paired_eligible_endpoint_escape h e hz hk u hR p q hat hct hgen hel with hn | hn
  · exact hn (borel_equal_mover_two_slice_endpoint_control h e hz hk u hR p
      hat hct heq hforward hpre hboth.1)
  · exact hn (borel_equal_mover_two_slice_endpoint_control h e hz hk u hR q
      hat hct heq hforward hpre' hboth.2)

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
