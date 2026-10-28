module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourOpposedSpans

/-!
# The literal Baumann quotient in the original Borel terminal comparison

The unique noncentral factor of the radius modulo its full seed implies
that any normal radius subgroup centralizing the moving radius lies in
Baumann. The other alternative would make the moving radius abelian,
contradicting the proved nonzero derived radius. Conversely, the
three-subgroups lemma and residual-fixed derived radius show that Baumann
centralizes the moving radius. Thus B = V ∩ C(V°), and B ∩ V° is exactly
Z(V°).

The selected span contains V° modulo the full starting seed. Its center
therefore centralizes V° and lies in B. This connects its central quotient
to the actual Baumann quotient without asserting that those quotients are
equal. The opposed-span cross-kernel bound then supplies fixed index at
most four for the whole opposite actor modulo B, through the literal
original embedding. OriginalSylowExceptional applies all four comparisons
to c.L,d.S.

Both full moving covers, central attachments and the cubic kernel E/Q
remain. Whole-radius/core residual fixedness and the terminal module
contradiction still have to be established before CoreExhaustion and
whole exceptional reconstruction.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.10), printed pp.879--881, and (5.12)(2), printed pp.925--926;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk


include h e hz hk in
private theorem borel_four_normal_centralizing_moving_le_B
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (Y : Subgroup (FreeAmalgam Rg))
    (hYN : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)))
    (hYV : Y ≤ V Rg (alpha Rg))
    (hYC : Y ≤ centralizer (Vcirc Rg (alpha Rg) : Set (FreeAmalgam Rg))) :
    Y ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  let a := alpha Rg
  let Y₀ := Y.comap (embedM Rg)
  have hb := distance_gt_two h e hz hk
  have hVG := (sourceGeometry h).V_local a rfl hb
  have hYm : Y₀.map (embedM Rg) = Y :=
    map_comap_eq_self ((hYV.trans hVG).trans_eq (stabilizer_m_base Rg))
  let : Y₀.Normal := ⟨by
    intro y hy g
    change embedM Rg (g*y*g⁻¹) ∈ Y
    rw [map_mul,map_mul,map_inv]
    have hg : embedM Rg g ∈ stabilizer Rg a := by
      rw [show a = mVertex Rg 1 from rfl,stabilizer_m_base]
      exact ⟨g,rfl⟩
    exact (mem_normalizer_iff.mp (hYN hg) (embedM Rg y)).mp hy⟩
  have hLm : (L.subgroupOf (L ⊔ R)).map (embedM Rg) = Ltilde Rg a := by
    rw [Ltilde_alpha,h.relative_residual]
  have hZm : (radiusSeed L R).map (embedM Rg) = Z Rg a :=
    map_comap_eq_self ((Z_le_stabilizer Rg _).trans_eq (stabilizer_m_base Rg))
  obtain ⟨z,p,hp⟩ := borel_four_exists_large_critical h e hz hk u hR
  rcases critical_radius_normal_subgroup_dichotomy h e hz hk hb p hp Y₀
      (comap_mono hYV) with hf | hc
  · have hf' := map_mono (f := embedM Rg) hf
    rw [map_commutator,hYm,hLm,hZm,commutator_comm] at hf'
    intro y hy
    apply (mem_B_iff Rg a _ hVG y).mpr
    exact ⟨hYV hy,fun l hl => hf' (commutator_mem_commutator hl hy)⟩
  · have hc' := map_mono (f := embedM Rg) hc
    rw [map_commutator,radius_comap_map (h := h) hb,hLm,Subgroup.map_sup,hYm,hZm] at hc'
    have hmQ : Vcirc Rg a ≤ Q Rg a :=
      (le_normalizer_iff_commutator_le_left.mp
        ((Ltilde_le_stabilizer a).trans (V_normalized a))).trans
        ((sourceGeometry h).V_le_Q hb a rfl)
    have hZC : Z Rg a ≤ centralizer (Vcirc Rg a : Set (FreeAmalgam Rg)) :=
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a rfl)).trans
        (centralizer_le hmQ)
    have hm : ⁅Vcirc Rg a,Vcirc Rg a⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (hc'.trans (sup_le hYC hZC))
    have hv : ⁅V Rg a,V Rg a⁆ = ⊥ := by
      rw [radius_derived_eq_moving_derived_original h (sourceGeometry h) hb a (beta Rg)
        rfl (base_adjacent Rg) (borel_four_radius_derived_fixed_base h e hz hk u hR),hm]
    exact ((borel_four_radius_derived_configuration h e hz hk u hR).2.2.2
      (hv ▸ bot_le)).elim

include h e hz hk in
/-- The literal Baumann subgroup is the centralizer of the moving radius
inside the whole original radius. -/
theorem borel_four_baumann_eq_radius_centralizer
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) =
      V Rg (alpha Rg) ⊓ centralizer (Vcirc Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  let a := alpha Rg
  let D := B Rg a ((sourceGeometry h).Z_normal _)
  have hb := distance_gt_two h e hz hk
  have hVG := (sourceGeometry h).V_local a rfl hb
  have hDV : D ≤ V Rg a := fun x hx => (mem_B_iff Rg a _ hVG x).mp hx |>.1
  have hDZ : ⁅D,Ltilde Rg a⁆ ≤ Z Rg a := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff Rg a _ hVG x).mp hx).2 l hl
  have hZC : Z Rg a ≤ centralizer (V Rg a : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a rfl)).trans
      (centralizer_le ((sourceGeometry h).V_le_Q hb a rfl))
  have hDC : D ≤ centralizer (Vcirc Rg a : Set (FreeAmalgam Rg)) :=
    (commutator_centralizes_iff_centralizes_moved (V Rg a) (Ltilde Rg a) D hDV
      ((borel_four_radius_derived_fixed_base h e hz hk u hR).trans inf_le_right)).mp
      (hDZ.trans hZC)
  apply le_antisymm (le_inf hDV hDC)
  apply borel_four_normal_centralizing_moving_le_B h e hz hk u hR _ _ inf_le_left inf_le_right
  exact (le_inf (V_normalized a)
    ((Vcirc_normalized a).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf



include h e hz hk in
/-- Baumann cuts out exactly the intrinsic center of the full moving radius. -/
theorem borel_four_moving_baumann_eq_center
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).subgroupOf
      (Vcirc Rg (alpha Rg)) = center (Vcirc Rg (alpha Rg)) := by
  rw [borel_four_baumann_eq_radius_centralizer h e hz hk u hR]
  have hmV : Vcirc Rg (alpha Rg) ≤ V Rg (alpha Rg) :=
    le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer _).trans (V_normalized _))
  ext x
  constructor
  · rintro ⟨_,hc⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hc y y.property)
  · intro hx
    refine ⟨hmV x.property,?_⟩
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)

include h e hz hk in
/-- The center of the whole selected span lies in the literal Baumann subgroup,
including the full starting central attachment. -/
theorem borel_four_span_center_le_baumann
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
    (center P).map P.subtype ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  let a := alpha Rg
  let P := localZSpan Rg (p.walk.getVert 2) a
  let C := (center P).map P.subtype
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
  have hPV : P ≤ V Rg a := localZSpan_le_V Rg (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  have hCP : C ≤ P := map_subtype_le _
  have hCC : C ≤ centralizer (P : Set (FreeAmalgam Rg)) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  have hZC : C ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (hCP.trans (hPV.trans ((sourceGeometry h).V_le_Q hb a rfl))).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a rfl)))
  change C ≤ _
  rw [borel_four_baumann_eq_radius_centralizer h e hz hk u hR]
  refine le_inf (hCP.trans hPV) ?_
  have hc : C ≤ centralizer ((P ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set _) :=
    le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hCC) (le_centralizer_iff.mp hZC))
  exact hc.trans (centralizer_le (borel_four_moving_radius_le_span_seed h e hz hk u hR p))


/-- Normality of the original Baumann preimage, relative to the original vertex group. -/
theorem baumann_preimage_normal (hb : 2 < sourceDistance h) :
    ((B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).comap (embedM Rg)).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  apply le_normalizer_comap (embedM Rg)
  apply Escape.Propagation.Rigidity.B_normalized
    (geometry := sourceGeometry h) hb (alpha Rg) rfl
  rw [show alpha Rg = mVertex Rg 1 from rfl,stabilizer_m_base]
  exact ⟨g,rfl⟩

include h e hz hk in
/-- The whole opposite span fixes an index-at-most-four subgroup on the
forward span modulo the actual Baumann subgroup, through the original embedM. -/
theorem borel_four_opposed_span_baumann_fixed_index
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    let a := alpha Rg
    let c := p.walk.getVert 2
    let P := (localZSpan Rg c a).comap (embedM Rg)
    let A := (localZSpan Rg a c).comap (embedM Rg)
    let D := (B Rg a ((sourceGeometry h).Z_normal _)).comap (embedM Rg)
    let := baumann_preimage_normal h (distance_gt_two h e hz hk)
    (centralizerModulo P A D).relIndex P ≤ 4 := by
  let a := alpha Rg
  let c := p.walk.getVert 2
  let P := (localZSpan Rg c a).comap (embedM Rg)
  let A := (localZSpan Rg a c).comap (embedM Rg)
  let D := (B Rg a ((sourceGeometry h).Z_normal _)).comap (embedM Rg)
  let C := (Q Rg c).comap (embedM Rg)
  let := baumann_preimage_normal h (distance_gt_two h e hz hk)
  change (centralizerModulo P A D).relIndex P ≤ 4
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
  have hPG : localZSpan Rg c a ≤ stabilizer Rg a :=
    (localZSpan_le_V Rg (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])).trans
      ((sourceGeometry h).V_local a rfl hb)
  have hPm : P.map (embedM Rg) = localZSpan Rg c a :=
    map_comap_eq_self (hPG.trans_eq (stabilizer_m_base Rg))
  have hCG : Q Rg c ≤ stabilizer Rg a :=
    Q_le_stabilizer_of_dist_le_two c a
      ((p.vertex_color (by omega)).mpr (by decide)) rfl
      (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  have hCm : C.map (embedM Rg) = Q Rg c :=
    map_comap_eq_self (hCG.trans_eq (stabilizer_m_base Rg))
  have hZB : Z Rg a ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
    intro x hx
    apply (mem_B_iff Rg a _ ((sourceGeometry h).V_local a rfl hb) x).mpr
    refine ⟨Z_le_VBall Rg a 2 hx,?_⟩
    intro l hl
    apply le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer a).trans (Z_normalized Rg a))
    rw [commutator_comm]
    exact commutator_mem_commutator hl hx
  have hcomm : ⁅P ⊓ C,A⁆ ≤ D := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,Subgroup.map_inf _ _ _ (embedM_injective Rg),hPm,hCm]
    exact ((commutator_mono le_rfl (map_comap_le _ _)).trans
      (borel_four_opposed_spans h e hz hk u hR p).2.2.2.2.1).trans hZB
  have hi : C.relIndex P = 4 := by
    rw [←relIndex_map_map_of_injective _ _ (embedM_injective Rg),hCm,hPm]
    exact borel_four_span_core_index h e hz hk u hR p
  exact (NoncentralChiefRefinement.SymmetricSixBudget.centralizerModulo_relIndex_le_of_commutator
    P A D C hcomm).trans_eq hi

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
