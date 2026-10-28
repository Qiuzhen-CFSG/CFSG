module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRadiusKernel

/-!
# Full omega layers on the original cubic critical configuration

At a small critical pair, the pointwise fixer of the seed kernel bounds
X at the opposite endpoint. Thus X and Z have the same image modulo the
actual local kernel E. Since E centralizes X, replacing both seeds by the
full omega layers preserves the critical commutator. The odd quotient E/Q
contributes no index on a two-subgroup, so the opposite full X-image modulo
the literal Q also has order two. The pointwise fixer of its kernel still
retains E, and fixes that kernel only if its displacement on X lies in the
original critical line.

In the point-core branch the full midpoint-radius supplements now show
that both full omega kernels centralize that radius, and that the radius
induces the original critical line on each X. Conjugating under the same
selected stabilizer proves that the full omega orbit has the same radius
commutator as the original seed span P. The derived-order assertion remains
about P: P' has order two and is central at the original vertex. On that
same path the full reverse X-kernel acts nontrivially on the starting-radius
kernel, by the new pointwise-fixer control and the established radius-index
obstruction.

The whole-core and literal C.1.32 applications retain the original graph,
projection kernel E, odd quotient E/Q, both covers of orders 16 and 32, and
the plane and Sylow alternatives. This supplies full-X comparisons needed
for the shifted commutators of MS93 (5.12). The equality of that shifted
commutator with the prior seed line, the opposite-core bounds and terminal
contradiction, the remaining radical branches and natural exhaustion are
still required for the final two-branch reconstruction.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3), printed pp.866--867, and (5.12)(1), pp.924--925;
Aschbacher--Smith C.1.31--32, printed pp.135--136. The kernel calculations
adapt Natural.Exhaustion.LargeDistance.SectionFive.FullKernel to the
original cubic projection, preserving E rather than identifying it with Q.
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

include h in
private theorem omega_seed_le {a : Vertex Rg} (ha : color Rg a = false) :
    Z Rg a ≤ X Rg a := by
  apply (sourceGeometry h).omega_bound a ha
  rw [(sourceGeometry h).distance_constant a ha]
  exact sourceDistance_pos h

include h e in
private theorem omega_reverse {a z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z) :
    CriticalPair Rg z a ((sourceGeometry h).exists_critical z p.end_color) :=
  critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) a p.start_color
    (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
    z p.end_color p.critical

include h e hz hk in
/-- The full omega layer and the seed have the same image modulo E.
The cubic quotient E/Q is retained. -/
theorem small_critical_omega_join
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4) :
    (stabilizer Rg a ⊓ centralizer (X Rg a : Set (FreeAmalgam Rg))) ⊔ X Rg z =
      (stabilizer Rg a ⊓ centralizer (X Rg a : Set (FreeAmalgam Rg))) ⊔ Z Rg z := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply le_trans _ (small_critical_kernel_centralizer h e hz hk p hsmall)
    exact le_inf (critical_X_le_vertex h e z p.end_color a (omega_reverse h e p))
      (le_centralizer_iff.mp (inf_le_right.trans (Q_le_centralizer_X Rg z)))
  · exact sup_le_sup_left (omega_seed_le h p.end_color) _

include h e hz hk in
/-- Enlarging both critical seeds to their full omega layers preserves the
literal commutator; this does not identify the layers themselves. -/
theorem small_critical_omega_commutator
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4) :
    ⁅X Rg a,X Rg z⁆ = ⁅Z Rg a,Z Rg z⁆ := by
  let q : CriticalPath Rg (sourceGeometry h) z a :=
    CriticalPath.ofPair p.end_color (omega_reverse h e p)
  have hs : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(small_critical_indices h e hz hk p hsmall).2]
    decide
  have ha := critical_X_le_vertex h e a p.start_color z p.critical
  have hz' := critical_X_le_vertex h e z p.end_color a q.critical
  have he₁ : ⁅X Rg a,X Rg z⁆ = ⁅X Rg a,Z Rg z⁆ := by
    rw [commutator_eq_of_centralizing_sup rfl
      (show stabilizer Rg a ⊓ centralizer (X Rg a : Set (FreeAmalgam Rg)) ≤
        centralizer (X Rg a : Set (FreeAmalgam Rg)) from inf_le_right)
      (hz'.trans (X_normalized Rg a)),small_critical_omega_join h e hz hk p hsmall]
    exact (commutator_eq_of_centralizing_sup rfl inf_le_right
      (((omega_seed_le h p.end_color).trans hz').trans (X_normalized Rg a))).symm
  rw [he₁,commutator_comm (X Rg a),commutator_comm (Z Rg a)]
  have hE : stabilizer Rg z ⊓ centralizer (X Rg z : Set (FreeAmalgam Rg)) ≤
      centralizer (Z Rg z : Set (FreeAmalgam Rg)) :=
    inf_le_right.trans (centralizer_le (omega_seed_le h p.end_color))
  rw [commutator_eq_of_centralizing_sup rfl hE (ha.trans (Z_normalized Rg z)),
    small_critical_omega_join h e hz hk q hs]
  exact (commutator_eq_of_centralizing_sup rfl hE
    (((omega_seed_le h p.start_color).trans ha).trans (Z_normalized Rg z))).symm

include h e hz hk in
/-- The pointwise fixer of the full omega kernel is the same E-supplement
as for the seed kernel, including the odd central covering kernel. -/
theorem small_critical_omega_kernel_centralizer
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4) :
    stabilizer Rg a ⊓ centralizer (X Rg a ⊓ Q Rg z : Set (FreeAmalgam Rg)) =
      (stabilizer Rg a ⊓ centralizer (X Rg a : Set (FreeAmalgam Rg))) ⊔ Z Rg z := by
  apply le_antisymm
  · exact (inf_le_inf_left _ (centralizer_le
      (inf_le_inf_right _ (omega_seed_le h p.start_color)))).trans
        (small_critical_kernel_centralizer h e hz hk p hsmall)
  · apply sup_le
    · exact inf_le_inf_left _ (centralizer_le inf_le_left)
    · exact le_inf
        ((omega_seed_le h p.end_color).trans
          (critical_X_le_vertex h e z p.end_color a (omega_reverse h e p)))
        (((omega_seed_le h p.end_color).trans
          (le_centralizer_iff.mp (Q_le_centralizer_X Rg z))).trans
            (centralizer_le inf_le_right))

include h e hz hk in
/-- Full omega kernels, rather than only seed kernels, centralize the
whole midpoint radius on the original critical four-edge path. -/
theorem point_critical_omega_kernels_centralize_midpoint_radius
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    X Rg a ⊓ Q Rg z ≤ centralizer (V Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) ∧
      X Rg z ⊓ Q Rg a ≤ centralizer (V Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  have hs := point_critical_midpoint_radius_supplements h e hz hk u hR p
  constructor
  · apply le_centralizer_iff.mpr
    rw [←hs.1]
    exact sup_le ((inf_le_right.trans (Q_le_centralizer_X Rg a)).trans
      (centralizer_le inf_le_left))
      ((commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg z p.end_color)).trans (centralizer_le inf_le_right))
  · apply le_centralizer_iff.mpr
    rw [←hs.2]
    exact sup_le ((inf_le_right.trans (Q_le_centralizer_X Rg z)).trans
      (centralizer_le inf_le_left))
      ((commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a p.start_color)).trans (centralizer_le inf_le_right))

include h e hz hk in
/-- The full midpoint radius induces the critical seed line on each full
omega layer. No central-generation or X = Z hypothesis is needed. -/
theorem point_critical_omega_midpoint_radius_commutators
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    ⁅X Rg a,V Rg (p.walk.getVert 2)⁆ = ⁅Z Rg a,Z Rg z⁆ ∧
      ⁅X Rg z,V Rg (p.walk.getVert 2)⁆ = ⁅Z Rg a,Z Rg z⁆ := by
  have hs := point_critical_midpoint_radius_supplements h e hz hk u hR p
  have hsmall : (Q Rg z).relIndex (Z Rg a) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR p).1]
    decide
  have ha := critical_X_le_vertex h e a p.start_color z p.critical
  have hz' := critical_X_le_vertex h e z p.end_color a (omega_reverse h e p)
  have hX := small_critical_omega_commutator h e hz hk p hsmall
  have hAX : ⁅X Rg a,Z Rg z⁆ = ⁅Z Rg a,Z Rg z⁆ :=
    le_antisymm ((commutator_mono le_rfl (omega_seed_le h p.end_color)).trans_eq hX)
      (commutator_mono (omega_seed_le h p.start_color) le_rfl)
  have hZX : ⁅X Rg z,Z Rg a⁆ = ⁅Z Rg a,Z Rg z⁆ := by
    rw [commutator_comm (X Rg z)]
    exact le_antisymm ((commutator_mono (omega_seed_le h p.start_color) le_rfl).trans_eq hX)
      (commutator_mono le_rfl (omega_seed_le h p.end_color))
  constructor
  · exact (commutator_eq_of_centralizing_sup hs.1
      (inf_le_right.trans (Q_le_centralizer_X Rg a))
      (((omega_seed_le h p.end_color).trans hz').trans (X_normalized Rg a))).symm.trans hAX
  · exact (commutator_eq_of_centralizing_sup hs.2
      (inf_le_right.trans (Q_le_centralizer_X Rg z))
      (((omega_seed_le h p.start_color).trans ha).trans (X_normalized Rg z))).symm.trans hZX

include h e hz hk in
/-- Fixing the full omega kernel controls the entire opposite omega layer
by the original seed line, with the actual cubic local kernel retained. -/
theorem small_critical_omega_kernel_control
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4)
    (Y : Subgroup (FreeAmalgam Rg)) (hY : Y ≤ stabilizer Rg z)
    (hfix : Y ≤ centralizer (X Rg z ⊓ Q Rg a : Set (FreeAmalgam Rg))) :
    ⁅Y,X Rg z⁆ ≤ ⁅Z Rg a,Z Rg z⁆ := by
  let q : CriticalPath Rg (sourceGeometry h) z a :=
    CriticalPath.ofPair p.end_color (omega_reverse h e p)
  have hs : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(small_critical_indices h e hz hk p hsmall).2]
    decide
  have hj : Y ≤ (stabilizer Rg z ⊓ centralizer (X Rg z : Set (FreeAmalgam Rg))) ⊔ Z Rg a := by
    rw [←small_critical_omega_kernel_centralizer h e hz hk q hs]
    exact le_inf hY hfix
  have hAX : ⁅X Rg z,Z Rg a⁆ ≤ ⁅Z Rg a,Z Rg z⁆ := by
    rw [commutator_comm (X Rg z)]
    exact (commutator_mono (omega_seed_le h p.start_color) le_rfl).trans_eq
      (small_critical_omega_commutator h e hz hk p hsmall)
  rw [commutator_comm Y]
  exact ((commutator_mono le_rfl hj).trans_eq
    (commutator_eq_of_centralizing_sup rfl inf_le_right
      (((omega_seed_le h p.start_color).trans
        (critical_X_le_vertex h e a p.start_color z p.critical)).trans
          (X_normalized Rg z))).symm).trans hAX

include h e hz hk in
/-- On the same original critical path, the full reverse omega kernel
acts nontrivially on the starting radius kernel. This is the literal
X-kernel term; its equality with the previously found seed line is not assumed. -/
theorem point_critical_omega_radius_cross_kernel_ne_bot
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg (alpha Rg)⁆ ≠ ⊥ := by
  let c := p.walk.getVert 2
  have hl : p.walk.length = 4 := p.length_eq_b.trans
    (point_image_distance_eq_four h e hz hk u hR)
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hYG : V Rg (alpha Rg) ⊓ Q Rg c ≤ stabilizer Rg z :=
    inf_le_right.trans (Q_le_stabilizer_of_dist_le_two c z hc p.end_color
      (by rw [p.dist_end,hl]))
  have hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR p).1]
    decide
  intro he
  have hcontrol := small_critical_omega_kernel_control h e hz hk p hsmall
    (V Rg (alpha Rg) ⊓ Q Rg c) hYG (commutator_eq_bot_iff_le_centralizer.mp he)
  apply point_critical_radius_kernel_not_le_seed h e hz hk u hR p
  exact ((commutator_mono le_rfl (omega_seed_le h p.end_color)).trans hcontrol).trans
    (le_normalizer_iff_commutator_le_left.mp
      (((omega_seed_le h p.end_color).trans
        (critical_X_le_vertex h e z p.end_color (alpha Rg) (omega_reverse h e p))).trans
          (Z_normalized Rg (alpha Rg))))

include h e hz hk in
/-- Enlarging the selected seed to its full omega layer preserves its
commutator with the whole radius, even after taking the same stabilizer orbit. -/
theorem point_selected_omega_span_radius_commutator
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {c d : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) c d)
    (hq : q.walk.getVert 2 = alpha Rg)
    (hcentral : ⁅Z Rg c,Z Rg d⁆ ≤
      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) :
    ⁅⨆ g : stabilizer Rg (alpha Rg),
        (X Rg c).map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom,
      V Rg (alpha Rg)⁆ = ⁅Z Rg c,Z Rg d⁆ := by
  let D₀ := ⁅Z Rg c,Z Rg d⁆
  let P := ⨆ g : stabilizer Rg (alpha Rg),
    (X Rg c).map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  have hXQ : X Rg c ≤ Q Rg (alpha Rg) := by
    apply X_le_Q_of_dist_lt Rg (sourceGeometry h) (sourceEdgeCentralizer h e) c q.start_color
    rw [(sourceGeometry h).distance_constant c q.start_color]
    change (cosetGraph Rg).dist c (alpha Rg) < sourceDistance h
    rw [←hq,q.dist_start (by omega),hb]
    decide
  have hXG : X Rg c ≤ stabilizer Rg (alpha Rg) := hXQ.trans (fun _ hx => hx.1)
  have hDN : stabilizer Rg (alpha Rg) ≤ normalizer (D₀ : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _)
  have hXV := (point_critical_omega_midpoint_radius_commutators h e hz hk u hR q).1
  rw [hq] at hXV
  apply le_antisymm
  · change ⁅P,V Rg (alpha Rg)⁆ ≤ D₀
    dsimp only [P]
    apply commutator_iSup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      (V Rg (alpha Rg)) D₀ _ hDN
    · intro g x hx
      obtain ⟨y,hy,rfl⟩ := hx
      exact (stabilizer Rg (alpha Rg)).mul_mem
        ((stabilizer Rg (alpha Rg)).mul_mem
          ((stabilizer Rg (alpha Rg)).inv_mem g.property) (hXG hy))
        ((stabilizer Rg (alpha Rg)).inv_mem
          ((stabilizer Rg (alpha Rg)).inv_mem g.property))
    · intro g
      have hh := map_mono (f := (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom) hXV.le
      have hV : (V Rg (alpha Rg)).map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom =
          V Rg (alpha Rg) := mem_normalizer_iff_map_conj_eq.mp
            (V_normalized (alpha Rg) ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      have hD : D₀.map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = D₀ :=
        mem_normalizer_iff_map_conj_eq.mp (hDN ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      rwa [map_commutator,hV,hD] at hh
  · rw [←hXV]
    apply commutator_mono _ le_rfl
    have hh := le_iSup (fun g : stabilizer Rg (alpha Rg) =>
      (X Rg c).map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom) 1
    intro x hx
    apply hh
    exact ⟨x,hx,by simp⟩

include h e hz hk in
/-- Point-core containment supplies a nonabelian selected span whose entire
radius commutator and derived subgroup are the same central order-two line.
The full omega orbit on this same selected path has exactly that radius commutator. -/
theorem point_image_selected_omega_span_radius_line
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
      let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
      Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
      ⁅⨆ g : stabilizer Rg (alpha Rg),
          (X Rg (p.walk.getVert 2)).map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom,
        V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
      ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert 2),
        X Rg a' ⊓ Q Rg (alpha Rg)⁆ ≠ ⊥ := by
  obtain ⟨hb,a',p,_,c,t,x,hx,hxc,_,_,_,q,_,hover,_,_,hcard,hcentral⟩ :=
    point_image_small_central_generating_configuration h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hq2 : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  let qr : CriticalPath Rg (sourceGeometry h) (p.walk.getVert (p.walk.length-2)) c :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) c q.start_color
        (by rw [(sourceGeometry h).distance_constant _ q.start_color]; exact sourceDistance_pos h)
        _ q.end_color q.critical⟩
  have hqr2 : qr.walk.getVert 2 = alpha Rg := by
    change q.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,show q.walk.length = 4 from q.length_eq_b.trans hb]
    exact hq2
  have hc : c ∈ Set.range (fun g : stabilizer Rg (alpha Rg) =>
      act Rg g (p.walk.getVert (p.walk.length-2))) := by
    refine ⟨⟨x,hx⟩,?_⟩
    simpa only [hl,Nat.reduceSub] using hxc
  have hcent : ⁅Z Rg (p.walk.getVert (p.walk.length-2)),Z Rg c⁆ ≤
      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    rwa [commutator_comm]
  have hs := point_selected_span_radius_commutator h e hz hk u hR qr hqr2 hc hcent
  have hω := point_selected_omega_span_radius_commutator h e hz hk u hR qr hqr2 hcent
  rw [commutator_comm (Z Rg (p.walk.getVert (p.walk.length-2))) (Z Rg c)] at hs hω
  have hcardP : Nat.card (⁅localZSpan Rg (p.walk.getVert (p.walk.length-2)) (alpha Rg),
      localZSpan Rg (p.walk.getVert (p.walk.length-2)) (alpha Rg)⁆ : Subgroup (FreeAmalgam Rg)) = 2 := by
    rw [hs.2]
    exact hcard
  refine ⟨a',p,?_⟩
  simpa only [hl,Nat.reduceSub] using
    And.intro hcardP (And.intro (hs.2.trans_le hcentral)
      (And.intro (hs.1.trans hs.2.symm) (And.intro (hω.trans hs.2.symm)
        (show ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),
          X Rg a' ⊓ Q Rg (alpha Rg)⁆ ≠ ⊥ from by
          simpa only [hl,Nat.reduceSub] using
            point_critical_omega_radius_cross_kernel_ne_bot h e hz hk u hR p))))
include h e hz hk in
/-- The full omega layer and the seed also have the same image order
modulo the actual two-core: the odd quotient E/Q contributes no two-group
index. This equality does not replace E by Q as a projection kernel. -/
theorem small_critical_omega_core_index
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4) :
    (Q Rg a).relIndex (X Rg z) = 2 := by
  obtain ⟨i,hi,hir,hiQ,hiE,_,_⟩ := graph_cover h e hz hk a p.start_color
  let A := (X Rg z).comap i
  let B₀ := (Z Rg z).comap i
  have hmA : A.map i = X Rg z := map_comap_eq_self
    ((critical_X_le_vertex h e z p.end_color a (omega_reverse h e p)).trans_eq hir.symm)
  have hmB : B₀.map i = Z Rg z := map_comap_eq_self
    (((omega_seed_le h p.end_color).trans
      (critical_X_le_vertex h e z p.end_color a (omega_reverse h e p))).trans_eq hir.symm)
  have hj : extensionKernel h ⊔ A = extensionKernel h ⊔ B₀ := by
    apply map_injective hi
    rw [Subgroup.map_sup,Subgroup.map_sup,hiE,hmA,hmB]
    exact small_critical_omega_join h e hz hk p hsmall
  let : IsElementaryAbelian 2 (X Rg z) := omegaCenter_elementary _
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hA : IsPGroup 2 A :=
    (IsElementaryAbelian.isPGroup 2 (X Rg z)).comap_of_injective _ hi
  have hB : IsPGroup 2 B₀ :=
    (IsElementaryAbelian.isPGroup 2 (Z Rg z)).comap_of_injective _ hi
  have he : (pCore 2 M).relIndex A = (pCore 2 M).relIndex B₀ := by
    rw [←CubicAction.permutation_image_card_of_two h e hz hk A hA,
      ←CubicAction.permutation_image_card_of_two h e hz hk B₀ hB,
      ←relIndex_ker,←relIndex_ker,CubicAction.projection_kernel,
      ←relIndex_sup_left A (extensionKernel h),hj,relIndex_sup_left]
  have he' : (Q Rg a).relIndex (X Rg z) = (Q Rg a).relIndex (Z Rg z) := by
    rw [←hiQ,←hmA,←hmB,relIndex_map_map_of_injective _ _ hi,
      relIndex_map_map_of_injective _ _ hi]
    exact he
  exact he'.trans (small_critical_indices h e hz hk p hsmall).2

omit hk in
include h e hz in
/-- The literal whole-core application retains both covers, the cubic
projection and the original selected span. Its full omega orbit has the
same central order-two radius commutator. At every critical path, the
full omega image has order two and both full omega kernels fix the midpoint
radius. Plane and Sylow images remain independent alternatives. -/
theorem coreExhaustion_or_cubic_omega_radius_line :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ (a z : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg a).relIndex (X Rg z) = 2 ∧
            ⁅X Rg a,X Rg z⁆ = ⁅Z Rg a,Z Rg z⁆ ∧
            X Rg a ⊓ Q Rg z ≤ centralizer (V Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) ∧
            X Rg z ⊓ Q Rg a ≤ centralizer (V Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) ∧
          ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
            let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
            Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
            ⁅⨆ g : stabilizer Rg (alpha Rg),
                (X Rg (p.walk.getVert 2)).map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom,
              V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
            ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert 2),
              X Rg a' ⊓ Q Rg (alpha Rg)⁆ ≠ ⊥) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_radical_cases h e hz with
    hx | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint.2,hpoint.1,?_,
      point_image_selected_omega_span_radius_line h e hz hk u hpoint.2.le⟩⟩
    intro a z p
    have hsmall : (Q Rg z).relIndex (Z Rg a) < 4 := by
      rw [(point_image_critical_indices_two h e hz hk u hpoint.2.le p).1]
      decide
    exact ⟨small_critical_omega_core_index h e hz hk p hsmall,
      small_critical_omega_commutator h e hz hk p hsmall,
      point_critical_omega_kernels_centralize_midpoint_radius h e hz hk u hpoint.2.le p⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- The same full omega comparison in the literal C.1.32 application. -/
theorem rankTwo_or_cubic_omega_radius_line :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ (a z : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg a).relIndex (X Rg z) = 2 ∧
            ⁅X Rg a,X Rg z⁆ = ⁅Z Rg a,Z Rg z⁆ ∧
            X Rg a ⊓ Q Rg z ≤ centralizer (V Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) ∧
            X Rg z ⊓ Q Rg a ≤ centralizer (V Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) ∧
          ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
            let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
            Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
            ⁅⨆ g : stabilizer Rg (alpha Rg),
                (X Rg (p.walk.getVert 2)).map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom,
              V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
            ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert 2),
              X Rg a' ⊓ Q Rg (alpha Rg)⁆ ≠ ⊥) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_omega_radius_line h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
