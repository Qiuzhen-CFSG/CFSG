module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.ChiefBudget
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.Action
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Paths

/-!
# The original two-core on the moving central quotient

The critical endpoint has image of order four. Its midpoint-kernel
intersection has index at most four and commutators central in the moving
radius. The A₆ chief budget therefore applies to that actual moving group
modulo its center. Fixed derived radius and full residual movement give the
normal-layer dichotomy; nilpotent saturation makes the original two-core
act trivially on the central quotient. No splitting or elementary whole
radius is used.

Source: MS93 (3.8), printed p.878. This discharges the two-core descent
needed for the remaining natural-module commutator contradiction.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open NoncentralChiefRefinement.SymmetricSixBudget
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (m : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h m hz)
  (r : Replacement L R)

omit [Finite G] in
private theorem normalized_comap_normal (N : Subgroup (FreeAmalgam r.radical))
    (hN : stabilizer r.radical (alpha r.radical) ≤ normalizer (N : Set _)) :
    (N.comap (embedM r.radical)).Normal := by
  constructor
  intro x hx g
  change embedM r.radical (g*x*g⁻¹) ∈ N
  rw [map_mul,map_mul,map_inv]
  exact le_normalizer_iff.mp hN _
    (by rw [show alpha r.radical = mVertex r.radical 1 from rfl,stabilizer_m_base]; exact ⟨g,rfl⟩) _ hx

omit [Finite G] in
instance moving_preimage_normal :
    ((Vcirc r.radical (alpha r.radical)).comap (embedM r.radical)).Normal :=
  normalized_comap_normal r _ (Vcirc_normalized _)

/-- The exact A₆ projection, fixed-index budget and residual hypotheses
for the original moving group, pulled back through the original embedM. -/
theorem moving_budget_data
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r)
    (b : Vertex r.radical)
    (hc : CriticalPair r.radical (alpha r.radical) b
      ((replacementGeometry h r).exists_critical (alpha r.radical) rfl))
    (c : Vertex r.radical) (hcColor : color r.radical c = false)
    (hac : (cosetGraph r.radical).dist (alpha r.radical) c = 2)
    (hcb : (cosetGraph r.radical).dist c b = 2) :
    let P := (Vcirc r.radical (alpha r.radical)).comap (embedM r.radical)
    ∃ q : r.overgroup →* alternatingGroup (Fin 6),
      Function.Surjective q ∧ q.ker = pCore 2 r.overgroup ∧ P.Normal ∧ P ≤ q.ker ∧
      ⁅P,pResidual 2 r.overgroup⁆ = P ∧
      ⁅⁅P,P⁆,pResidual 2 r.overgroup⁆ = ⊥ ∧
      ∃ (A : Subgroup r.overgroup) (a : alternatingGroup (Fin 6)),
        orderOf a = 2 ∧ a ∈ A.map q ∧
        (centralizerModulo P A (P ⊓ centralizer (P : Set r.overgroup))).relIndex P ≤ 8 := by
  let f := embedM r.radical
  let a₀ := alpha r.radical
  let P := (Vcirc r.radical a₀).comap f
  let A := (X r.radical b).comap f
  let K := (Q r.radical c).comap f
  let C := P ⊓ centralizer (P : Set r.overgroup)
  let π := projection h m hz hn r
  let q := π.codRestrict (alternatingGroup (Fin 6)) (fun g => by rw [←himage]; exact ⟨g,rfl⟩)
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨g,hg⟩ := show (a : Equiv.Perm (Fin 6)) ∈ π.range from (by rw [himage]; exact a.property)
    exact ⟨g,Subtype.ext hg⟩
  have hk : q.ker = pCore 2 r.overgroup := by
    calc q.ker = π.ker := by ext g; exact Subtype.ext_iff
         _ = pCore 2 r.overgroup := projection_kernel h m hz hn r
  let := normalized_comap_normal r _ (Vcirc_normalized a₀)
  have hb : 2 < replacementDistance h r := by rw [fg.distance]; decide
  have hPV : Vcirc r.radical a₀ ≤ V r.radical a₀ :=
    le_normalizer_iff_commutator_le_left.mp ((Ltilde_le_stabilizer a₀).trans (V_normalized a₀))
  have hPQ := hPV.trans ((replacementGeometry h r).V_le_Q hb a₀ rfl)
  have hPrange := (hPQ.trans (fun _ hx => hx.1)).trans_eq (stabilizer_m_base r.radical)
  have hPm : P.map f = Vcirc r.radical a₀ := map_comap_eq_self hPrange
  have hQm : (pCore 2 r.overgroup).map f = Q r.radical a₀ :=
    (Q_alpha r.radical (replacement_radical_isPGroup h r) (replacement_core_le_radical h r)).symm
  have hLm : (pResidual 2 r.overgroup).map f = Ltilde r.radical a₀ := (Ltilde_alpha r.radical).symm
  have hPk : P ≤ q.ker := by
    rw [hk]
    apply (map_le_map_iff_of_injective (embedM_injective r.radical)).mp
    rwa [hPm,hQm]
  have hfull : ⁅P,pResidual 2 r.overgroup⁆ = P := by
    apply (map_injective (embedM_injective r.radical))
    rw [map_commutator,hPm,hLm]
    exact moving_full_commutation h r hb a₀ rfl
  have hfixed : ⁅⁅P,P⁆,pResidual 2 r.overgroup⁆ = ⊥ := by
    apply (map_injective (embedM_injective r.radical))
    rw [map_commutator,map_commutator,hPm,hLm,Subgroup.map_bot]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (commutator_mono hPV hPV).trans
      ((radius_derived_le_fixed h m hz hn r himage fg a₀ rfl).trans inf_le_right)
  obtain ⟨t,hat,ht⟩ := exists_adjacent_dist_sub_one r.radical a₀ b (by
    rw [hc.1,(replacementGeometry h r).distance_constant a₀ rfl]
    exact replacementDistance_pos h r)
  have hAS : X r.radical b ≤ stabilizer r.radical a₀ :=
    (Estimates.critical_edge_data h m hz hn r himage a₀ rfl b hc t hat ht).1.trans
      (CriticalCriterion.edge_le_stabilizer r.radical rfl hat)
  have hAm : A.map f = X r.radical b :=
    map_comap_eq_self (hAS.trans_eq (stabilizer_m_base r.radical))
  have hfour : Nat.card (A.map q) = 4 := by
    rw [←card_map_of_injective (f := (alternatingGroup (Fin 6)).subtype) Subtype.val_injective,
      map_map]
    exact (Estimates.critical_image_structure h m hz hn r himage b hc t hat ht).1
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := A.map q) 2 (by rw [hfour]; decide)
  have haorder : orderOf (a : alternatingGroup (Fin 6)) = 2 :=
    (orderOf_injective (A.map q).subtype Subtype.val_injective a).trans ha
  have hcomm : ⁅P ⊓ K,A⁆ ≤ C := by
    apply le_inf (le_trans (commutator_mono inf_le_left le_rfl) (commutator_le_left P A))
    intro x hx y hy
    apply embedM_injective r.radical
    rw [map_mul,map_mul]
    have hxmap : f x ∈ X r.radical a₀ := by
      have hmap := mem_map_of_mem f hx
      rw [map_commutator,map_inf _ _ _ (embedM_injective r.radical),hPm,hAm] at hmap
      exact ((commutator_mono
        (inf_le_inf hPV (map_comap_le _ _)) le_rfl).trans
          ((radius_intersection_X h m hz hn r himage fg a₀ rfl b hc c hcb).trans
            ((Estimates.critical_X_commutator h r m hz hn himage a₀ rfl b hc).1.trans inf_le_left))) hmap
    exact ((le_centralizer_iff.mp (Q_le_centralizer_X r.radical a₀)).trans
      (centralizer_le hPQ)) hxmap (f y) hy
  have hindex : (centralizerModulo P A C).relIndex P ≤ 8 := by
    apply (centralizerModulo_relIndex_le_of_commutator P A C K hcomm).trans
    have hi : K.relIndex P ≤ 4 := by
      rw [relIndex_comap,hPm]
      exact (relIndex_le_of_le_right hPV (by
        let := finite_stabilizer r.radical a₀
        let : Finite (V r.radical a₀) := Finite.of_injective
          (inclusion (((replacementGeometry h r).V_le_Q hb a₀ rfl).trans (fun _ hx => hx.1)))
          (inclusion_injective _)
        exact index_ne_zero_of_finite)).trans
        (radius_index_le_four h m hz hn r himage fg a₀ rfl b hc c hcColor hac hcb)
    omega
  exact ⟨q,hq,hk,inferInstance,hPk,hfull,hfixed,A,a,haorder,a.property,hindex⟩

/-- Actual source application: the original two-core centralizes the moving
radius modulo its center, with all chief-budget premises discharged. -/
theorem moving_kernel_commutator_central_alpha
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r)
    (b : Vertex r.radical)
    (hc : CriticalPair r.radical (alpha r.radical) b
      ((replacementGeometry h r).exists_critical (alpha r.radical) rfl))
    (c : Vertex r.radical) (hcColor : color r.radical c = false)
    (hac : (cosetGraph r.radical).dist (alpha r.radical) c = 2)
    (hcb : (cosetGraph r.radical).dist c b = 2) :
    ⁅Vcirc r.radical (alpha r.radical),Q r.radical (alpha r.radical)⁆ ≤
      centralizer (Vcirc r.radical (alpha r.radical) : Set (FreeAmalgam r.radical)) := by
  obtain ⟨q,hq,hk,hP,hPk,hfull,hfixed,A,a,ha,haA,hi⟩ :=
    moving_budget_data h m hz hn r himage fg b hc c hcColor hac hcb
  let P := (Vcirc r.radical (alpha r.radical)).comap (embedM r.radical)
  let := hP
  have hp : IsPGroup 2 q.ker := by rw [hk]; exact pCore_isPGroup
  have hh := AlternatingBudget.kernel_commutator_le_center q hq hp P hPk A a ha haA hi hfull hfixed
  have hPm : P.map (embedM r.radical) = Vcirc r.radical (alpha r.radical) :=
    map_comap_eq_self (((le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer (alpha r.radical)).trans (V_normalized (alpha r.radical)))).trans
      ((replacementGeometry h r).V_le_Q (by change 2 < replacementDistance h r; rw [fg.distance]; decide) (alpha r.radical) rfl)).trans
        (fun _ hx => hx.1) |>.trans_eq (stabilizer_m_base r.radical))
  have hm := map_mono (f := embedM r.radical) (hh.trans inf_le_right)
  rw [map_commutator,hPm,hk,←Q_alpha r.radical (replacement_radical_isPGroup h r)
    (replacement_core_le_radical h r)] at hm
  exact hm.trans (by rw [←hPm]; exact map_centralizer_le_centralizer_image _ _)

/-- The two-core centralizes the actual moving group modulo its center at
every original-group vertex. Critical pairs and midpoints are constructed. -/
theorem moving_kernel_commutator_central
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) (a : Vertex r.radical) (ha : color r.radical a = false) :
    ⁅Vcirc r.radical a,Q r.radical a⁆ ≤
      centralizer (Vcirc r.radical a : Set (FreeAmalgam r.radical)) := by
  have hbase : ⁅Vcirc r.radical (alpha r.radical),Q r.radical (alpha r.radical)⁆ ≤
      centralizer (Vcirc r.radical (alpha r.radical) : Set (FreeAmalgam r.radical)) := by
    obtain ⟨b,hcrit⟩ := criticalPair_exists r.radical (alpha r.radical)
      ((replacementGeometry h r).exists_critical (alpha r.radical) rfl)
    let p := CriticalPath.ofPair (geometry := replacementGeometry h r) rfl hcrit
    have hl : p.walk.length = 4 := p.length_eq_b.trans fg.distance
    have hle : 2 ≤ p.walk.length := by omega
    exact moving_kernel_commutator_central_alpha h m hz hn r himage fg b hcrit
      (p.walk.getVert 2) ((p.vertex_color hle).mpr (by decide)) (p.dist_start hle)
      (by rw [p.dist_end,hl])
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color r.radical ha
  have hv : Vcirc r.radical (mVertex r.radical g) =
      (Vcirc r.radical (alpha r.radical)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using Vcirc_act r.radical g (alpha r.radical)
  have hq : Q r.radical (mVertex r.radical g) =
      (Q r.radical (alpha r.radical)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using Q_act r.radical g (alpha r.radical)
  rw [hv,hq,←map_commutator]
  exact (map_mono hbase).trans (map_centralizer_le_centralizer_image _ _)

private theorem quotient_kernel_of_central
    {M : Type*} [Group M] {T : Subgroup M} (a : Vertex T)
    (hc : ⁅Vcirc T a,Q T a⁆ ≤ centralizer (Vcirc T a : Set (FreeAmalgam T))) :
    (Q T a).subgroupOf (stabilizer T a) ≤ (movingQuotientAction a).ker := by
  intro g hg
  apply MulEquiv.ext
  intro v
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center (Vcirc T a)) v
  rw [movingQuotientAction_apply]
  apply QuotientGroup.eq_iff_div_mem.mpr
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  change (y : FreeAmalgam T) * ((g : FreeAmalgam T) * (x : FreeAmalgam T) *
    (g : FreeAmalgam T)⁻¹ / (x : FreeAmalgam T)) = _
  rw [commutator_comm] at hc
  simpa only [commutatorElement_def,div_eq_mul_inv,Subgroup.coe_mul,
    Subgroup.coe_inv,movingAction_apply,Subgroup.subtype_apply] using
    hc (commutator_mem_commutator hg x.property) y y.property

/-- Literal action descent: every element of the vertex two-core acts as
identity on the existing movingQuotientAction, using the same quotient map. -/
theorem moving_quotient_core_le_kernel
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) (a : Vertex r.radical) (ha : color r.radical a = false) :
    (Q r.radical a).subgroupOf (stabilizer r.radical a) ≤ (movingQuotientAction a).ker :=
  quotient_kernel_of_central a (moving_kernel_commutator_central h m hz hn r himage fg a ha)

/-- The actual consumer with the critical estimates already discharged. -/
theorem moving_quotient_core_le_kernel_of_alternating
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (hb : 2 < replacementDistance h r) (a : Vertex r.radical)
    (ha : color r.radical a = false) :
    (Q r.radical a).subgroupOf (stabilizer r.radical a) ≤ (movingQuotientAction a).ker :=
  moving_quotient_core_le_kernel h m hz hn r himage
    (Estimates.fourGeometry_of_alternating h m hz hn r himage hb) a ha

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
