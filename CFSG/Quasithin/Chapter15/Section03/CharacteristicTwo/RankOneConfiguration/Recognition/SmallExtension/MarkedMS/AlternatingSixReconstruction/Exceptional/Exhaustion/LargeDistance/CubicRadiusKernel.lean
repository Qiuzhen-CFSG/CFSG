module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRadiusFactors

/-!
# The whole-radius critical-kernel line in the point-core branch

The previously proved two-factor obstruction forces fixed index at least
sixteen for an even involution actor on the literal radius quotient. Two
conjugates of a transposition actor contain such an even involution, while
their fixed index is at most the square of the original index. Thus every
transposition actor has fixed index at least four.

At a critical four-edge path, the full radius has image at most two at the
midpoint. Consequently its midpoint kernel cannot commute with the reverse
critical seed modulo the starting seed. The small-kernel centralizer theorem
then proves a nontrivial commutator with the reverse critical kernel. The
existing predecessor-core upper bound identifies this commutator with the
entire midpoint-core commutator, of order two. It centralizes both radii.
The full and moving reverse kernels give the same subgroup, by the actual
last-edge seed decomposition, and the graph action transports all assertions
to every critical path.

The whole-core and literal C.1.32 applications retain the projection kernel
E, its odd quotient over Q, both moving covers and the plane/Sylow branches.
This is a whole-radius obstruction to exclude, not the shifted-seed R1 of
MS93 (5.12)(1): that comparison also involves X at its endpoint. No equality
between X, the seed orbit, or a radius center is used. The remaining shifted
commutator comparison, plane/Sylow exclusions and natural exhaustion are
still required for both final reconstruction outcomes.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the radius estimate in (5.2), printed pp.914--915, and the shifted
commutator comparison in (5.12), printed pp.924--927; Aschbacher--Smith
C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.NaturalSixControl
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

private theorem swap_even_product (t : S) (ht : t.IsSwap) :
    ∃ s : S, orderOf (t * (s*t*s⁻¹)) = 2 ∧
      t * (s*t*s⁻¹) ∈ alternatingGroup (Fin 6) := by
  obtain ⟨i,j,hij,rfl⟩ := ht
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (Equiv.Perm.isConj_swap (w := (0 : Fin 6)) (x := 1) (by decide) hij)
  let c : S := Equiv.swap 0 2 * Equiv.swap 1 3
  have hc : c * swap01 * c⁻¹ = swap23 := by decide
  have he : Equiv.swap i j * (g*c*g⁻¹ * Equiv.swap i j * (g*c*g⁻¹)⁻¹) =
      (MulAut.conj g) (swap01 * swap23) := by
    change g * swap01 * g⁻¹ = Equiv.swap i j at hg
    rw [←hg,←hc]
    simp only [MulAut.conj_apply]
    group
  refine ⟨g*c*g⁻¹,?_,?_⟩
  · rw [he,(MulAut.conj g).orderOf_eq]
    exact orderOf_eq_prime (by decide) (by decide)
  · rw [he]
    exact Subgroup.Normal.conj_mem inferInstance _ (by decide) g

private theorem conjugate_centralizer_index {F : Type*} [Group F]
    (N A : Subgroup F) [N.Normal] (g : F) :
    (centralizer (A.map (MulAut.conj g).toMonoidHom : Set F)).relIndex N =
      (centralizer (A : Set F)).relIndex N := by
  have he : (centralizer (A : Set F)).map (MulAut.conj g).toMonoidHom =
      centralizer (A.map (MulAut.conj g).toMonoidHom : Set F) := by
    apply le_antisymm
    · exact map_centralizer_le_centralizer_image _ _
    · intro x hx
      refine ⟨(MulAut.conj g).symm x,?_,(MulAut.conj g).apply_symm_apply x⟩
      intro a ha
      apply (MulAut.conj g).injective
      simpa only [map_mul,MulEquiv.apply_symm_apply] using
        hx ((MulAut.conj g) a) (mem_map_of_mem _ ha)
  have hi := relIndex_map_map_of_injective (centralizer (A : Set F)) N
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [he] at hi
  simpa only [MulEquiv.toMonoidHom_eq_coe,Subgroup.Normal.map_conj_eq] using hi

include h e hz hk in
/-- A transposition actor has fixed index at least four on the full radius
quotient. Two conjugates contain an even involution; their fixed-index
product is bounded below by sixteen, independently of the cubic kernel. -/
theorem point_radius_transposition_actor_index
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (t : S) (ht : t.IsSwap) (htA : t ∈ A.map π) :
    4 ≤ (centralizer (A.map (QuotientGroup.mk' (radiusSeed L R)) :
      Set (M ⧸ radiusSeed L R))).relIndex (radiusQuotient L R) := by
  let q := QuotientGroup.mk' (radiusSeed L R)
  obtain ⟨s,hs,heven⟩ := swap_even_product t ht
  obtain ⟨g,hg⟩ := CubicEven.projection_surjective h e hz hk s
  let A' := A.map (MulAut.conj g).toMonoidHom
  have hmem : t * (s*t*s⁻¹) ∈ (A ⊔ A').map π := by
    apply mul_mem (map_mono le_sup_left htA)
    apply map_mono le_sup_right
    obtain ⟨a,ha,rfl⟩ := htA
    refine ⟨(MulAut.conj g) a,mem_map_of_mem _ ha,?_⟩
    simp only [MulAut.conj_apply,map_mul,map_inv,hg]
  have hlower := point_radius_even_actor_index h e hz hk u hR
    (A ⊔ A') (t*(s*t*s⁻¹)) hs heven hmem
  have hAq : A'.map q = (A.map q).map (MulAut.conj (q g)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
  have hsame : (centralizer (A'.map q : Set (M ⧸ radiusSeed L R))).relIndex
      (radiusQuotient L R) =
      (centralizer (A.map q : Set (M ⧸ radiusSeed L R))).relIndex
      (radiusQuotient L R) := by
    rw [hAq]
    exact conjugate_centralizer_index _ _ _
  have hcentral : centralizer ((A ⊔ A').map q : Set (M ⧸ radiusSeed L R)) =
      centralizer (A.map q : Set (M ⧸ radiusSeed L R)) ⊓
      centralizer (A'.map q : Set (M ⧸ radiusSeed L R)) := by
    rw [Subgroup.map_sup]
    apply le_antisymm
    · exact le_inf (centralizer_le (show A.map q ≤ A.map q ⊔ A'.map q from le_sup_left))
        (centralizer_le (show A'.map q ≤ A.map q ⊔ A'.map q from le_sup_right))
    exact le_centralizer_iff.mpr (sup_le
      (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right))
  change 16 ≤ (centralizer ((A ⊔ A').map q : Set (M ⧸ radiusSeed L R))).relIndex
    (radiusQuotient L R) at hlower
  rw [hcentral] at hlower
  have hupper := (relIndex_inf_le (H := centralizer (A.map q : Set (M ⧸ radiusSeed L R)))
    (K := centralizer (A'.map q : Set (M ⧸ radiusSeed L R))) (L := radiusQuotient L R))
  rw [hsame] at hupper
  have hbound := hlower.trans hupper
  change 4 ≤ (centralizer (A.map q : Set (M ⧸ radiusSeed L R))).relIndex
    (radiusQuotient L R)
  nlinarith

include h e hz hk in
/-- The entire radius kernel at the midpoint is not controlled modulo the
starting seed by the opposite full critical seed. This is stronger than
noncommutativity of the selected span: it exhibits the missing whole-radius
premise on the same path. -/
theorem point_critical_radius_kernel_not_le_seed
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    ¬ ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert 2),Z Rg a'⁆ ≤ Z Rg (alpha Rg) := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans (point_image_distance_eq_four h e hz hk u hR)
  have hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR p).1]
    decide
  obtain ⟨t,ht,htA⟩ := small_critical_image_eq_swap h e hz hk p hsmall
  let f := embedM Rg
  let A := (Z Rg a').comap f
  let K := (Q Rg (p.walk.getVert 2)).comap f
  let q := QuotientGroup.mk' (radiusSeed L R)
  have hmA : A.map f = Z Rg a' := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  have hlo := point_radius_transposition_actor_index h e hz hk u hR A t ht
    (by change t ∈ ((Z Rg a').comap (embedM Rg)).map π; rw [htA]; exact mem_zpowers t)
  intro hcomm
  have hcomm₀ : ⁅radiusPreimage L R ⊓ K,A⁆ ≤ radiusSeed L R := by
    apply (map_le_map_iff_of_injective (embedM_injective Rg)).mp
    rw [map_commutator,Subgroup.map_inf _ _ _ (embedM_injective Rg),
      radius_comap_map (h := h) hb,hmA]
    exact ((commutator_mono (inf_le_inf_left _ (map_comap_le _ _)) le_rfl).trans
      hcomm).trans (map_comap_eq_self ((Z_le_stabilizer Rg _).trans_eq
        (stabilizer_m_base Rg))).ge
  have hindex : K.relIndex (radiusPreimage L R) ≤ 2 := by
    rw [relIndex_comap,radius_comap_map (h := h) hb]
    apply point_radius_index_le_two h e hz hk u hR rfl
      ((p.vertex_color (by omega)).mpr (by decide))
    · simpa only [SimpleGraph.Walk.getVert_zero] using
        (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
    · exact adjacent_symm Rg
        ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hfixed := (SymmetricSixBudget.centralizerModulo_relIndex_le_of_commutator
    (radiusPreimage L R) A (radiusSeed L R) K hcomm₀).trans hindex
  rw [SymmetricSixBudget.centralizerModulo_relIndex_eq] at hfixed
  change (centralizer (A.map q : Set (M ⧸ radiusSeed L R))).relIndex
    (radiusQuotient L R) ≤ 2 at hfixed
  change 4 ≤ (centralizer (A.map q : Set (M ⧸ radiusSeed L R))).relIndex
    (radiusQuotient L R) at hlo
  omega

include h e hz hk in
/-- The full reverse critical kernel acts nontrivially on the whole-radius
midpoint kernel. The previously proved centralization of the midpoint
radius by this seed kernel does not extend to the starting radius. -/
theorem point_critical_radius_cross_kernel_ne_bot
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert 2),Z Rg a' ⊓ Q Rg (alpha Rg)⁆ ≠ ⊥ := by
  intro hzcomm
  apply point_critical_radius_kernel_not_le_seed h e hz hk u hR p
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans (point_image_distance_eq_four h e hz hk u hR)
  apply small_critical_predecessor_commutator h e hz hk hb p
    (by rw [(point_image_critical_indices_two h e hz hk u hR p).1]; decide)
    (V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert 2))
  · simpa only [hl] using (inf_le_right : V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert 2) ≤ _)
  · exact commutator_eq_bot_iff_le_centralizer.mp hzcomm

include h e hz hk in
/-- The whole midpoint-core commutator is a line of order two and is already
realized on the starting-radius kernel. It centralizes both original radii.
This retains the full-radius subgroup needed before the shifted-seed
comparison in source (5.12); no identification with its R1 is asserted. -/
theorem point_critical_radius_cross_kernel_line
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    let c := p.walk.getVert 2
    let H := ⁅Z Rg a' ⊓ Q Rg (alpha Rg),Q Rg c⁆
    Nat.card H = 2 ∧
      ⁅V Rg (alpha Rg) ⊓ Q Rg c,Z Rg a' ⊓ Q Rg (alpha Rg)⁆ = H ∧
      ⁅V Rg (alpha Rg) ⊓ Q Rg c,U Rg a' ⊓ Q Rg (alpha Rg)⁆ = H ∧
      H ≤ centralizer (V Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      H ≤ centralizer (V Rg c : Set (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let K := Z Rg a' ⊓ Q Rg (alpha Rg)
  let H := ⁅K,Q Rg c⁆
  let W := ⁅V Rg (alpha Rg) ⊓ Q Rg c,K⁆
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans (point_image_distance_eq_four h e hz hk u hR)
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hKQ : K ≤ Q Rg c := by
    apply inf_le_left.trans
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,hl,(sourceGeometry h).distance_constant _ p.end_color]
    have hb4 := point_image_distance_eq_four h e hz hk u hR
    change 4 - 2 < sourceDistance h
    omega
  have hHQ : H ≤ Q Rg c :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le hKQ le_rfl)
  let := finite_stabilizer Rg c
  let : Finite H := Finite.of_injective
    (inclusion (hHQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hWH : W ≤ H := by
    calc W = ⁅K,V Rg (alpha Rg) ⊓ Q Rg c⁆ := commutator_comm _ _
         _ ≤ H := commutator_mono le_rfl inf_le_right
  let : Finite W := Finite.of_injective (inclusion hWH) (inclusion_injective _)
  have hupper : Nat.card H ≤ 2 := by
    have hh := small_critical_kernel_predecessor_card h e hz hk hb u hR p
      (by rw [(point_image_critical_indices_two h e hz hk u hR p).1]; decide)
    simpa only [hl,Nat.reduceSub] using hh
  have hlower : 1 < Nat.card W := (one_lt_card_iff_ne_bot _).mpr
    (point_critical_radius_cross_kernel_ne_bot h e hz hk u hR p)
  have hcard : Nat.card H = 2 := by have hi := card_le_of_le hWH; omega
  have heq : W = H := eq_of_le_of_card_ge hWH (by omega)
  have hmove := (critical_kernel_predecessor_moving h e hz hb p).2.2
    (V Rg (alpha Rg) ⊓ Q Rg c) (by
      simpa only [hl,Nat.reduceSub] using
        (inf_le_right : V Rg (alpha Rg) ⊓ Q Rg c ≤ Q Rg c))
  have hmoveeq : ⁅V Rg (alpha Rg) ⊓ Q Rg c,U Rg a' ⊓ Q Rg (alpha Rg)⁆ = H := by
    calc
      _ = ⁅U Rg a' ⊓ Q Rg (alpha Rg),V Rg (alpha Rg) ⊓ Q Rg c⁆ := commutator_comm _ _
      _ = ⁅K,V Rg (alpha Rg) ⊓ Q Rg c⁆ := hmove.symm
      _ = W := commutator_comm _ _
      _ = H := heq
  refine ⟨hcard,heq,hmoveeq,?_,?_⟩
  · change H ≤ centralizer (V Rg (alpha Rg) : Set (FreeAmalgam Rg))
    rw [←heq]
    exact (commutator_mono inf_le_left inf_le_right).trans
      (radius_bounds_at h e hz hk (alpha Rg) rfl a' c).1
  · have hQcN : Q Rg c ≤ normalizer (K : Set (FreeAmalgam Rg)) := by
      apply (le_inf ?_ ?_).trans inf_normalizer_le_normalizer_inf
      · exact (Q_le_stabilizer_of_dist_le_two c a' hc p.end_color
          (by rw [p.dist_end,hl])).trans (Z_normalized Rg a')
      · exact (Q_le_stabilizer_of_dist_le_two c (alpha Rg) hc rfl
          (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])).trans
          (Q_normalized Rg (alpha Rg))
    exact (le_normalizer_iff_commutator_le_left.mp hQcN).trans
      (point_critical_kernels_centralize_midpoint_radius h e hz hk u hR p).2

include h e hz hk in
/-- The order-two whole-radius kernel commutator at every critical path,
transported by the literal original graph action. -/
theorem point_critical_radius_cross_kernel_line_at
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a') :
    let c := p.walk.getVert 2
    let H := ⁅Z Rg a' ⊓ Q Rg a,Q Rg c⁆
    Nat.card H = 2 ∧
      ⁅V Rg a ⊓ Q Rg c,Z Rg a' ⊓ Q Rg a⁆ = H ∧
      ⁅V Rg a ⊓ Q Rg c,U Rg a' ⊓ Q Rg a⁆ = H ∧
      H ≤ centralizer (V Rg a : Set (FreeAmalgam Rg)) ∧
      H ≤ centralizer (V Rg c : Set (FreeAmalgam Rg)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := point_critical_radius_cross_kernel_line h e hz hk u hR
    (a' := act Rg g⁻¹ a')
  rw [←hbase] at base
  have hh := base (p.act g⁻¹)
  dsimp only at hh ⊢
  simp only [←commutator_eq_bot_iff_le_centralizer] at hh ⊢
  simpa only [CriticalPath.act,actWalk_getVert,V_act,Q_act,Z_act,U_act,inv_inv,
    ←Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    ←map_commutator,
    card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
    (Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).eq_iff,
    map_eq_bot_iff_of_injective _ (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective] using hh

omit hk in
include h e hz in
/-- Whole-core application: every critical path in the remaining point-core
branch has the literal nontrivial cross-kernel line. Plane and Sylow images,
the cubic projection and both central covers are retained. -/
theorem coreExhaustion_or_cubic_radius_kernel_line :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          ∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
            let c := p.walk.getVert 2
            let H := ⁅Z Rg a' ⊓ Q Rg a,Q Rg c⁆
            Nat.card H = 2 ∧
              ⁅V Rg a ⊓ Q Rg c,Z Rg a' ⊓ Q Rg a⁆ = H ∧
              ⁅V Rg a ⊓ Q Rg c,U Rg a' ⊓ Q Rg a⁆ = H ∧
              H ≤ centralizer (V Rg a : Set (FreeAmalgam Rg)) ∧
              H ≤ centralizer (V Rg c : Set (FreeAmalgam Rg))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_radical_cases h e hz with
    hx | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint.2,hpoint.1,
      fun _ _ p => point_critical_radius_cross_kernel_line_at h e hz hk u hpoint.2.le p⟩⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- The same whole-radius kernel line in the literal C.1.32 application. -/
theorem rankTwo_or_cubic_radius_kernel_line :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          ∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
            let c := p.walk.getVert 2
            let H := ⁅Z Rg a' ⊓ Q Rg a,Q Rg c⁆
            Nat.card H = 2 ∧
              ⁅V Rg a ⊓ Q Rg c,Z Rg a' ⊓ Q Rg a⁆ = H ∧
              ⁅V Rg a ⊓ Q Rg c,U Rg a' ⊓ Q Rg a⁆ = H ∧
              H ≤ centralizer (V Rg a : Set (FreeAmalgam Rg)) ∧
              H ≤ centralizer (V Rg c : Set (FreeAmalgam Rg))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_radius_kernel_line h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
