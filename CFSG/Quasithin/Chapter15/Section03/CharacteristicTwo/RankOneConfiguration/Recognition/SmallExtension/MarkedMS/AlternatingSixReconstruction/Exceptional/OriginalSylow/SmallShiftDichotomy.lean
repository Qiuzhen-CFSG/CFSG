module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistinctShifts
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistinctShifts
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration
/-!
# Small Borel shifts without a core-containment assumption

For any two component vertices on a common edge, the starting two-core
normalizes the neighboring seed: it lies in the edge kernel, which fixes
both vertices. This does not require containment in the opposite Thompson
mover. If the full omega layer is not centrally generated, reverse critical
omega control therefore makes a trapped endpoint normalize the two-seed span.

For distinct Borel movers, the paired critical actors make that span normal
in the starting stabilizer. Its quotient over the starting seed has order
dividing eight, so the existing alternating-six action bound places the span
in the Baumann slice. A strict slice excludes simultaneous trapping and gives
one of the compatible backward critical paths. Combining this with the
previous equal-mover result covers every mover comparison, including movers
omitting the starting core.

The remaining alternative is central generation of the entire omega layer
at every component vertex, together with X = Z. The strict-slice premise
is retained. Neither this alternative nor the terminal distance exclusions
is discharged here, and X = Z does not assert whole-core exhaustion.
Both full moving covers, of orders sixteen and thirty-two, and the original
cubic kernel E are retained. No replacement graph is used.

The private imports share the full-omega transport, seed index and small
normal-section argument within the existing reconstruction package.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.7), printed p.919; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement IsMulCommutative Pointwise
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

local notation "M" => (L ⊔ R : Subgroup G)

include h e hz hk in
/-- Reverse full-omega control normalizes a trapped two-seed span whenever
central generation fails. Common-edge containment supplies normalization by
the starting core, without a Thompson-mover containment hypothesis. -/
theorem small_trapped_span_normalized_of_not_central_generation
    {a c t z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hn : X Rg a ≠ U Rg a ⊔
      (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    X Rg z ≤ normalizer ((Z Rg c ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  have hb := distance_gt_two h e hz hk
  have hdist : (cosetGraph Rg).dist c a ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    have hh := (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := a)
    omega
  have hZQ : Z Rg c ≤ Q Rg a :=
    ((Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)).trans
      ((sourceGeometry h).V_le_Q hb a p.start_color)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let last := p.walk.getVert (p.walk.length-1)
  have hzlast : Adjacent Rg z last := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hlast : color Rg last = true := by
    have hh := adjacent_color_ne Rg hzlast
    rw [p.end_color] at hh
    cases he : color Rg last <;> simp_all
  have hprevlast : Adjacent Rg (p.walk.getVert (p.walk.length-2)) last := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hlocal : Z Rg c ≤ stabilizer Rg z :=
    (hbad.trans (Q_le_adjacent_h Rg hlast hprevlast)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hzlast))
  have hrev := critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
    a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
    z p.end_color p.critical
  let q : CriticalPath Rg (sourceGeometry h) z a := CriticalPath.ofPair p.end_color hrev
  have hs : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(small_critical_indices h e hz hk p hp).2]
    decide
  have hXN : X Rg z ≤ normalizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (critical_X_le_vertex h e z p.end_color a hrev).trans (Z_normalized Rg a)
  have hRZ : ⁅X Rg z,Z Rg a⁆ ≤ Z Rg a := le_normalizer_iff_commutator_le_right.mp hXN
  have hfix : Z Rg c ≤ centralizer
      ((⁅X Rg z,Z Rg a⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
    (hZQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a p.start_color)))).trans (centralizer_le hRZ)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.start_color] at hh
    cases he : color Rg t <;> simp_all
  have hQN : Q Rg a ≤ normalizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    ((Q_le_adjacent_h Rg ht hat).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))).trans (Z_normalized Rg c)
  have hcontrol : ∀ Y : Subgroup (FreeAmalgam Rg),
      Y ≤ stabilizer Rg z → Y ≤ centralizer
        ((⁅X Rg z,Z Rg a⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) →
      ⁅Y,X Rg z⁆ ≤ ⁅X Rg z,Z Rg a⁆ ⊔ ⁅Y,X Rg z ⊓ Q Rg a⁆ := by
    rcases small_critical_omega_generation_or_control_at h e hz hk q hs with hgen | hcontrol
    · exact (hn (omega_generation_transport p.end_color p.start_color hgen)).elim
    · exact hcontrol
  have hcom : ⁅X Rg z,Z Rg c⁆ ≤ Z Rg c ⊔ Z Rg a := by
    rw [commutator_comm]
    exact (hcontrol _ hlocal hfix).trans
      (sup_le (hRZ.trans le_sup_right)
        ((le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hQN)).trans le_sup_left))
  apply le_normalizer_iff.mpr
  intro x hx v hv
  have hm : (Z Rg c ⊔ Z Rg a).map (MulAut.conj x).toMonoidHom ≤ Z Rg c ⊔ Z Rg a := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hXN hx)).le.trans le_sup_right)
    rintro _ ⟨y,hy,rfl⟩
    have hh := (Z Rg c ⊔ Z Rg a).mul_mem
      (hcom (commutator_mem_commutator hx hy)) (mem_sup_left hy)
    simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
  exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hv)

include h e hz hk in
/-- For distinct movers, a trapped pair lies in the Baumann slice when the
full omega layer is not centrally generated. The opposite mover may omit the
starting core. -/
theorem borel_distinct_trapped_slice_of_not_central_generation
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hne : edgeOffenderJoin (alpha Rg) t ≠ edgeOffenderJoin c t)
    (hn : X Rg (alpha Rg) ≠ U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))) :
    Z Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  have hb := distance_gt_two h e hz hk
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hdist : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    have hh := (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := alpha Rg)
    omega
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)
  let Y := Z Rg c ⊔ Z Rg (alpha Rg)
  have hseed (v : Vertex Rg) (hv : color Rg v = false) : Z Rg v ≤ X Rg v :=
    (sourceGeometry h).omega_bound v hv (by
      rw [(sourceGeometry h).distance_constant v hv]
      exact sourceDistance_pos h)
  have hTNa : Q Rg t ≤ normalizer (Z Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    (show Q Rg t ≤ stabilizer Rg (alpha Rg) from
      fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _)
  have hTNc : Q Rg t ≤ normalizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    (show Q Rg t ≤ stabilizer Rg c from
      fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg _)
  have hYN : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact ((remaining_edge_thompson h e hz hk u (Or.inr hR) rfl hat).2.2.1.trans
        (le_inf hTNc hTNa)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (hseed z p.end_color).trans
        (small_trapped_span_normalized_of_not_central_generation h e hz hk p hp hat hct hn hbad)
    · exact (hseed z' q.end_color).trans
        (small_trapped_span_normalized_of_not_central_generation h e hz hk q hq hat hct hn hbad')
  have hZaT : Z Rg (alpha Rg) ≤ Q Rg t :=
    ((hseed _ rfl).trans (omegaCenter_le _)).trans (Q_le_adjacent_h Rg ht hat)
  let := finite_Z Rg (alpha Rg)
  have hsmall : (Z Rg (alpha Rg)).relIndex Y ∣ 8 := by
    change (Z Rg (alpha Rg)).relIndex (Z Rg c ⊔ Z Rg (alpha Rg)) ∣ 8
    rw [relIndex_sup_of_normalizes (Z Rg c) (Z Rg (alpha Rg)) (hZaT.trans hTNc)]
    have hd := relIndex_dvd_of_le_left (Z Rg c) (adjacent_Z_le Rg rfl hat)
    rw [borel_seed_edge_index h e hz hk u hR rfl hc hat hct hne] at hd
    exact hd
  exact le_sup_left.trans (small_normal_radius_le_slice h e hz hk Y
    (sup_le hZV (Z_le_VBall Rg _ 2)) hYN hsmall)

include h e hz hk in
/-- Every small-image Borel path at a strict forward slice either has full
omega central generation or a compatible backward critical path. This covers
equal and distinct movers without a starting-core containment assumption. -/
theorem borel_small_shift_or_central_generation
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hd : Adjacent Rg delta (p.walk.getVert 1))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta)) :
    (∀ a : Vertex Rg, color Rg a = false →
      (X Rg a = U Rg a ⊔
        (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) ∧
      X Rg a = Z Rg a) ∨
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 ∧
        (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let c := act Rg g delta
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ∧
          ((∃ b : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ p.walk.length-2, b.walk.getVert (i+2) = p.walk.getVert i) ∨
           (∃ b : CriticalPath Rg (sourceGeometry h) c (q.walk.getVert (q.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ q.walk.length-2, b.walk.getVert (i+2) = q.walk.getVert i)) := by
  by_cases heq : edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) =
      edgeOffenderJoin delta (p.walk.getVert 1)
  · exact borel_equal_thompson_small_shift_or_central_generation h e hz hk u hR p hp hd heq hs
  by_cases hn : X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)))
  · apply Or.inl
    intro a ha
    have hh := omega_generation_transport (show color Rg (alpha Rg) = false from rfl) ha hn
    exact ⟨hh,omega_eq_seed_of_central_generation h a ha hh⟩
  apply Or.inr
  obtain ⟨t,hat,r,hr,hgen,hpair,_,_,_,_,_,_,hnorm,hinside,_,g,hg,hgt,_⟩ :=
    borel_small_critical_seed_selectors_with_opposite h e hz hk u hR p hp
  let x := (embedM Rg r)⁻¹
  let c := act Rg g delta
  have hxG : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hxa : act Rg x (alpha Rg) = alpha Rg := hxG
  have hpact : ∃ q : CriticalPath Rg (sourceGeometry h)
      (act Rg x (alpha Rg)) (act Rg x z),
      ∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i) :=
    ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hxa] at hpact
  obtain ⟨q,hqverts⟩ := hpact
  have hqs : (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hxa,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hp
  have hct : Adjacent Rg c t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hd
  have hc : color Rg c = false := by
    have h₁ := adjacent_color_ne Rg hat
    have h₂ := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h₁
    cases he : color Rg c <;> cases he' : color Rg t <;> simp_all
  have hb := distance_gt_two h e hz hk
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
  have hstrict : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) := by
    change 2 < (B Rg (alpha Rg) _).relIndex (U Rg (act Rg g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hs
  have hfirst : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  have hdcol : color Rg delta = false := by
    simpa only [c,action_preserves_color] using hc
  have hga : act Rg g (alpha Rg) = alpha Rg := hg
  have hJa := remaining_edge_join_act h e hz hk u (Or.inr hR) rfl hfirst g
  have hJd := remaining_edge_join_act h e hz hk u (Or.inr hR) hdcol hd g
  simp only [hga,hgt] at hJa hJd
  have hnec : edgeOffenderJoin (alpha Rg) t ≠ edgeOffenderJoin c t := by
    intro he
    apply heq
    apply map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
    exact hJa.symm.trans (he.trans hJd)
  have extend (w : Vertex Rg) (s : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hn : ¬ Z Rg c ≤ Q Rg (s.walk.getVert (s.walk.length-2))) :
      ∃ b : CriticalPath Rg (sourceGeometry h) c (s.walk.getVert (s.walk.length-2)),
        b.walk.getVert 1 = t ∧ ∀ i ≤ s.walk.length-2, b.walk.getVert (i+2) = s.walk.getVert i := by
    let v : (cosetGraph Rg).Walk c (alpha Rg) :=
      .cons ((cosetGraph_adj Rg _ _).mpr hct)
        (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
    have hv : v.length = 2 := rfl
    let b := s.prepend_two (Nat.le_of_lt hb) hc v hv hn
    refine ⟨b,?_,fun i hi => s.prepend_two_overlap _ _ _ _ _ hi⟩
    simp only [b,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hv,show 1<2 from by decide,ite_true,v,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  by_cases hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2))
  · by_cases hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))
    · have hZB := borel_distinct_trapped_slice_of_not_central_generation h e hz hk u hR
        p q hp hqs hat hct hnec hn hgen hbad hbad'
      have hi := relIndex_eq_one.mpr ((DistanceEight.U_le_Z Rg c).trans hZB)
      omega
    · exact ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,g,hg,hgt,
        hstrict,Or.inr (extend _ q hbad')⟩
  · exact ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,g,hg,hgt,
      hstrict,Or.inl (extend _ p hbad)⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
