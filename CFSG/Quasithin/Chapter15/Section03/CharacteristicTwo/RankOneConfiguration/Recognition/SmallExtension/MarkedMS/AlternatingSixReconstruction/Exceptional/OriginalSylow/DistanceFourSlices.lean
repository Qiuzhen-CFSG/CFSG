module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourEqual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourInitial
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneTerminal

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourInitial
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourEqual

/-!
# Terminal reciprocal slices on the original Borel graph

Two small midpoint slices give the full opposite-core bounds already proved
for the original cubic graph. The Borel radius-escape theorem supplies the
remaining nonabelian-span hypothesis: an abelian span would lie in the
midpoint two-core, and endpoint control would put it in the starting Baumann
subgroup, contradicting forward eligibility. Thus a critical pair in one
midpoint orbit has a strict slice on one side of that same two-edge segment.

For a small critical image, the compatible normalized backward selection
constructs exactly such a pair, with its actual residual transporter. Mapping
the slice back along this transporter gives the reciprocal alternative on
the original segment. Large images already give its strict forward slice.
The initial compatible choices discharge all path assumptions, so a strict
slice exists and transports to every original Borel edge. Reselecting at a
strict edge gives initial compatible paths whose backward slice is strict
on that very path, retaining generation and the full fixed-subgroup comparison.
The internal imports reuse the established initial selectors and path
constructor without changing their public boundary.

This excludes the uniformly small-slice case without assuming any local
slice bound. It retains both full moving covers, their central attachments,
and the original cubic kernel E with its odd quotient E/Q. The literal
original-Sylow source application is in OriginalSylowExceptional. Excluding
the surviving strict-slice configurations, whole CoreExhaustion and the
exceptional block reconstruction remain necessary.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.10) and the terminal two-slice argument of (5.12), printed
pp.879--881,927; Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open CFSG.Quasithin.ChapterB.Offenders.Six
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
include h e hz hk in
private theorem borel_selected_span_nonabelian_of_endpoint
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hcomm : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓
      Q Rg (p.walk.getVert 2),Z Rg a'⁆ ≤ Z Rg (alpha Rg)) :
    ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ := by
  intro he
  have hb := distance_gt_two h e hz hk
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan Rg c (alpha Rg)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases hh' : color Rg t <;> simp_all
  have hPQ := (selected_span_le_forward_kernel (h := h) hb p).trans inf_le_left
  have hPG : P ≤ stabilizer Rg c :=
    (hPQ.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hPc : P ≤ Q Rg c := two_subgroup_seed_centralizer_le_core h e hz hcol P
    ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
      (alpha Rg) rfl).to_le hPQ)
    (le_inf hPG ((commutator_eq_bot_iff_le_centralizer.mp he).trans
      (centralizer_le (Z_le_localZSpan Rg c (alpha Rg)))))
  have hPV : P ≤ V Rg (alpha Rg) := localZSpan_le_V Rg (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  change ⁅P ⊓ Q Rg c,Z Rg a'⁆ ≤ Z Rg (alpha Rg) at hcomm
  have hPB := normalized_radius_le_slice_of_critical_commutator h e hz hb p P hPV
    (localZSpan_normalized Rg _ _) (by simpa only [inf_eq_left.mpr hPc] using hcomm)
  exact (borel_critical_paths h e hz hk u hR p).2.2.2
    ((DistanceEight.U_le_Z Rg _).trans ((Z_le_localZSpan Rg _ _).trans hPB))

include h e hz hk in
/-- At distance four, a Borel critical pair in one midpoint orbit has a
strict slice at one of the two ends of the same two-edge segment. -/
private theorem borel_midpoint_slice_alternative
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g (alpha Rg) = a') :
    2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2)) ∨
      2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg a') := by
  by_contra! hs
  have hb := distance_gt_two h e hz hk
  have hPQ := (selected_span_le_forward_kernel (h := h) hb p).trans inf_le_left
  have hm := (midpoint_common_kernel_endpoint_commutator h e hz hk hb4 p g hg he hs.2).2
  have hcomm : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓
      Q Rg (p.walk.getVert 2),Z Rg a'⁆ ≤ Z Rg (alpha Rg) :=
    ((commutator_mono (inf_le_inf_right _ hPQ) le_rfl).trans_eq hm).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
          (sourceDistance_pos h) p.critical).trans (Z_normalized Rg _)))
  exact selected_terminal_false_of_midpoint_slices h e hz hk p
    (borel_selected_span_nonabelian_of_endpoint h e hz hk u hR p hcomm) hs.1 g hg he hs.2

include h e hz hk in
/-- Transport the two-slice exclusion with the original midpoint conjugator
and both literal Baumann subgroups. -/
theorem borel_midpoint_slice_alternative_at
    (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (hb : sourceDistance h = 4)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g a = a') :
    2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2)) ∨
      2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg a') := by
  obtain ⟨x,rfl⟩ := exists_mVertex_of_color Rg p.start_color
  have hxbase : act Rg x⁻¹ (mVertex Rg x) = alpha Rg := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have base := borel_midpoint_slice_alternative h e hz hk u hR hb
    (a' := act Rg x⁻¹ a')
  rw [←hxbase] at base
  let k := x*g*x⁻¹
  have hrestore (v : Vertex Rg) : act Rg x (act Rg x⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hkg : k ∈ stabilizer Rg ((p.act x⁻¹).walk.getVert 2) := by
    change k ∈ stabilizer Rg ((actWalk Rg x⁻¹ p.walk).getVert 2)
    rw [actWalk_getVert,stabilizer_act]
    exact ⟨g,hg,by simp only [inv_inv]; rfl⟩
  have hke : act Rg k (act Rg x⁻¹ (mVertex Rg x)) = act Rg x⁻¹ a' := by
    simp only [k,act_mul]
    rw [hrestore,he]
  have hci : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by have hl : p.walk.length = sourceDistance h := p.length_eq_b; omega)).mpr (by decide)
  have hh := base (p.act x⁻¹) k hkg hke
  change 2 < (B Rg (act Rg x⁻¹ (mVertex Rg x))
      ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg ((actWalk Rg x⁻¹ p.walk).getVert 2)) ∨
    2 < (B Rg ((actWalk Rg x⁻¹ p.walk).getVert 2)
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg x⁻¹ a')) at hh
  rw [actWalk_getVert,
    Escape.PairingControl.FirstPairing.B_act (by omega : 2 < sourceDistance h) _ _ p.start_color,
    Escape.PairingControl.FirstPairing.B_act (by omega : 2 < sourceDistance h) _ _ hci,
    U_act,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective,
    relIndex_map_map_of_injective _ _ (MulAut.conj _).injective] at hh
  exact hh

include h e hz hk in
/-- Compatible forward choices force a strict slice on one side of the
literal initial two-edge segment. Large images give the forward inequality;
small images use the normalized backward path and its residual transporter. -/
theorem borel_four_compatible_reciprocal_slice
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hfixed : Z Rg (p.walk.getVert 3) ⊓ centralizer
        (edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) :
    2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2)) ∨
      2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a) := by
  have hb := borel_distance_eq_four h e hz hk u hR
  have hb2 := distance_gt_two h e hz hk
  by_cases hp : (Q Rg z).relIndex (Z Rg a) < 4
  · obtain ⟨d,t,x,hx,hxd,hxt,hat,hdt,hgen',hfix',q,hqt,hover,hnorm⟩ :=
      borel_four_normalized_backward_selection h e hz hk u hR p r hrz hgen hp hfixed
    have hqa : q.walk.getVert 2 = a := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
    have hxG : x ∈ stabilizer Rg a := Ltilde_le_stabilizer a hx
    have hxc : act Rg x⁻¹ d = p.walk.getVert 2 := by
      rw [←hxd,←act_mul,mul_inv_cancel,act_one]
    have hh := borel_midpoint_slice_alternative_at h e hz hk u hR hb q x⁻¹
      (hqa.symm ▸ (stabilizer Rg a).inv_mem hxG) hxc
    rw [hqa] at hh
    rcases hh with hi | hi
    · right
      have hc := q.end_color
      have hUa : (U Rg a).map (MulAut.conj x⁻¹).toMonoidHom = U Rg a := by
        rw [←U_act,show act Rg x a = a from hxG]
      rw [←hxd,Escape.PairingControl.FirstPairing.B_act (geometry := sourceGeometry h)
        hb2 x (p.walk.getVert 2) hc,←hUa,
        relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective] at hi
      exact hi
    · exact Or.inl hi
  · exact Or.inl (large_remaining_four_forward_slice_strict_at h e hz hk hb u
      (Or.inr hR) p (by omega))

include h e hz hk in
/-- The initial compatible choices discharge every path premise in the
reciprocal terminal exclusion. Consequently the original Borel graph has
a strict two-edge slice on both moving-cover branches. -/
private theorem borel_four_strict_slice_exists
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    ∃ a c t : Vertex Rg, color Rg a = false ∧ Adjacent Rg a t ∧ Adjacent Rg c t ∧
      2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) := by
  obtain ⟨a,z,y,p,r,hrz,hgen,hfixed⟩ := borel_four_initial_compatible_paths h e hz hk u hR
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hat : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  rcases borel_four_compatible_reciprocal_slice h e hz hk u hR p r hrz hgen hfixed with hi | hi
  · exact ⟨a,p.walk.getVert 2,p.walk.getVert 1,p.start_color,hat,hct,hi⟩
  · exact ⟨p.walk.getVert 2,a,p.walk.getVert 1,
      (p.vertex_color (by omega)).mpr (by decide),hct,hat,hi⟩

include h e hz hk in
/-- Every original Borel edge has a strict two-edge Baumann slice. This
transports the terminal exclusion and the constructed initial choices;
no critical path, image bound or slice premise is assumed. -/
theorem borel_four_strict_slice_at_edge
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t) :
    ∃ c : Vertex Rg, Adjacent Rg c t ∧
      2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) := by
  obtain ⟨a₀,c₀,t₀,ha₀,hat₀,hct₀,hi₀⟩ := borel_four_strict_slice_exists h e hz hk u hR
  have hb := distance_gt_two h e hz hk
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg ha₀
  obtain ⟨k,hk'⟩ := exists_mVertex_of_color Rg ha
  let f := g⁻¹*k
  have hfa : act Rg f a₀ = a := by
    rw [hg,act_mVertex]
    change mVertex Rg (g*(g⁻¹*k)) = a
    rw [←mul_assoc,mul_inv_cancel,one_mul,←hk']
  have haft : Adjacent Rg a (act Rg f t₀) := by
    rw [←hfa]
    exact (adjacent_act_iff Rg f _ _).mpr hat₀
  have hfcft : Adjacent Rg (act Rg f c₀) (act Rg f t₀) :=
    (adjacent_act_iff Rg f _ _).mpr hct₀
  have hif : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg f c₀)) := by
    rw [←hfa,Escape.PairingControl.FirstPairing.B_act
      (geometry := sourceGeometry h) hb f a₀ ha₀,U_act,
      relIndex_map_map_of_injective _ _ (MulAut.conj f⁻¹).injective]
    exact hi₀
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors Rg a haft hat
  have hB : (B Rg a ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B Rg a ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := sourceGeometry h)
        hb a ha ((stabilizer Rg a).inv_mem hx))
  refine ⟨act Rg x (act Rg f c₀),?_,?_⟩
  · rw [←hxt]
    exact (adjacent_act_iff Rg x _ _).mpr hfcft
  · rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hif

include h e hz hk in
private theorem strict_initial_small_pair_base
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hfirst : p.walk.getVert 1 = beta Rg) :
    ∃ z', ∃ s : CriticalPath Rg (sourceGeometry h) (alpha Rg) z',
      (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4 ∧
      ∃ d t, ∃ q : CriticalPath Rg (sourceGeometry h) d (s.walk.getVert 2),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ 2, q.walk.getVert (i+2) = s.walk.getVert i) ∧
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
        Q Rg t ⊔ Z Rg z' = stabilizer Rg (alpha Rg) ∧
        Z Rg (s.walk.getVert 1) ⊓ centralizer
          (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  have hb := borel_distance_eq_four h e hz hk u hR
  obtain ⟨t,hat,x,hx,hgen,hpair,hgen₀,hgen₁,hfix₀,hfix₁⟩ :=
    initial_seed_selectors_base h e hz hk u hR p hp hfirst
  have hxa : act Rg x (alpha Rg) = alpha Rg := hx
  have hpact : ∃ s : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
      ∀ i, s.walk.getVert i = act Rg x (p.walk.getVert i) := by
    have hh : ∃ s : CriticalPath Rg (sourceGeometry h)
        (act Rg x (alpha Rg)) (act Rg x z),
        ∀ i, s.walk.getVert i = act Rg x (p.walk.getVert i) :=
      ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [hxa] at hh
  obtain ⟨s,hsverts⟩ := hpact
  have hs : (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hxa,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hp
  obtain ⟨c,hct,hstrict⟩ := borel_four_strict_slice_at_edge h e hz hk u hR rfl hat
  have hel : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    intro hh
    rw [relIndex_eq_one.mpr hh] at hstrict
    omega
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hat
    have hh' := adjacent_color_ne Rg hct
    change false ≠ color Rg t at hh
    cases hc : color Rg c <;> cases ht : color Rg t <;> simp_all
  have escape : ¬ Z Rg c ≤ Q Rg (p.walk.getVert 2) ∨
      ¬ Z Rg c ≤ Q Rg (s.walk.getVert 2) := by
    by_contra! hbad
    have hl : p.walk.length = 4 := p.length_eq_b.trans hb
    have hsl : s.walk.length = 4 := s.length_eq_b.trans hb
    have hbad₀ : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
      simpa only [hl,Nat.reduceSub] using hbad.1
    have hbad₁ : Z Rg c ≤ Q Rg (s.walk.getVert (s.walk.length-2)) := by
      simpa only [hsl,Nat.reduceSub] using hbad.2
    by_cases hsplit : X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
        (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)))
    · by_cases heq : edgeOffenderJoin (alpha Rg) t = edgeOffenderJoin c t
      · exact borel_equal_strict_paired_not_trapped h e hz hk u hR p x hx s hsverts
          hp hs hat hct heq hgen hpair hbad₀ hbad₁ hstrict
      · exact borel_central_distinct_strict_escape h e hz hk u hR p hp hat hct
          hgen₀ hsplit heq hstrict hbad₀
    · exact hel ((DistanceEight.U_le_Z Rg c).trans
        (borel_trapped_slice_of_not_central_generation h e hz hk u hR p s hp hs
          hat hct hsplit hgen hbad₀ hbad₁))
  rcases escape with hn | hn
  · obtain ⟨q,hqt,hover⟩ := four_prepend_selected h hb p hc hat hct hn
    exact ⟨z,p,hp,c,t,q,hqt,hover,hstrict,hgen₀,hfix₀⟩
  · obtain ⟨q,hqt,hover⟩ := four_prepend_selected h hb s hc hat hct hn
    refine ⟨_,s,hs,c,t,q,hqt,hover,hstrict,hgen₁,?_⟩
    simpa only [hsverts] using hfix₁

include h e hz hk in
/-- A small critical image supplies initial compatible paths, including
whole-stabilizer generation and the full fixed-subgroup comparison on the
same path. No forward critical path or fixed-subgroup bound is assumed. -/
private theorem borel_four_small_initial_strict_paths
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ z', ∃ s : CriticalPath Rg (sourceGeometry h) (alpha Rg) z',
      (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4 ∧
      ∃ d t, ∃ q : CriticalPath Rg (sourceGeometry h) d (s.walk.getVert 2),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ 2, q.walk.getVert (i+2) = s.walk.getVert i) ∧
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
        Q Rg t ⊔ Z Rg z' = stabilizer Rg (alpha Rg) ∧
        Z Rg (s.walk.getVert 1) ⊓ centralizer
          (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  have hab : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  obtain ⟨x,hx,hxb⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hab (base_adjacent Rg)
  have hxa : act Rg x (alpha Rg) = alpha Rg := hx
  have hpact : ∃ s : CriticalPath Rg (sourceGeometry h)
      (act Rg x (alpha Rg)) (act Rg x z),
      s.walk.getVert 1 = act Rg x (p.walk.getVert 1) :=
    ⟨p.act x,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hxa,hxb] at hpact
  obtain ⟨s,hs⟩ := hpact
  have hsmall : (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hxa,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hp
  exact strict_initial_small_pair_base h e hz hk u hR s hsmall hs

include h e hz hk in
/-- The initial compatible pair can be chosen with a strict backward
Baumann slice on that very path. The small-image construction now uses the
proved strict slice at its selected edge; large images retain their adjusted
actor and actual residual transporter. -/
theorem borel_four_initial_compatible_strict_backward
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    ∃ a z y, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y,
        r.walk.getVert 2 = z ∧
        Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2) ∧
        (Z Rg (p.walk.getVert 3) ⊓ centralizer
          (edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) ∧
        2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a) := by
  obtain ⟨z,hzcrit⟩ := criticalPair_exists Rg (alpha Rg)
    ((sourceGeometry h).exists_critical (alpha Rg) rfl)
  let p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z := CriticalPath.ofPair rfl hzcrit
  have pair : ∃ z', ∃ s : CriticalPath Rg (sourceGeometry h) (alpha Rg) z',
      ∃ d t, ∃ q : CriticalPath Rg (sourceGeometry h) d (s.walk.getVert 2),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ 2, q.walk.getVert (i+2) = s.walk.getVert i) ∧
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
        Q Rg t ⊔ Z Rg z' = stabilizer Rg (alpha Rg) ∧
        Z Rg (s.walk.getVert 1) ⊓ centralizer
          (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    by_cases hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4
    · obtain ⟨z',s,_,d,t,q,hqt,hover,hi,hgen,hfix⟩ :=
        borel_four_small_initial_strict_paths h e hz hk u hR p hp
      exact ⟨z',s,d,t,q,hqt,hover,hi,hgen,hfix⟩
    · obtain ⟨A,_,_,_,_,d,t,x,hx,hxd,_,_,_,_,hfix,_,hgen,q,hqt,hover,_⟩ :=
        borel_four_large_adjusted_backward_selection h e hz hk u hR p (by omega)
      have hi := large_remaining_four_forward_slice_strict_at h e hz hk
        (borel_distance_eq_four h e hz hk u hR) u (Or.inr hR) p (by omega)
      have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
          (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
        mem_normalizer_iff_map_conj_eq.mp
          (Escape.Propagation.Rigidity.B_normalized (geometry := sourceGeometry h)
            (distance_gt_two h e hz hk) (alpha Rg) rfl
            ((stabilizer Rg (alpha Rg)).inv_mem (Ltilde_le_stabilizer _ hx)))
      have hid : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) := by
        rw [←hxd,U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
        exact hi
      exact ⟨z,p,d,t,q,hqt,hover,hid,hgen,hfix⟩
  obtain ⟨z',s,d,t,q,hqt,hover,hi,hgen,hfix⟩ := pair
  have hqa : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
  have hq3 : q.walk.getVert 3 = s.walk.getVert 1 := hover 1 (by decide)
  refine ⟨d,s.walk.getVert 2,z',q,?_⟩
  rw [hqa]
  exact ⟨s,rfl,by simpa only [hqt] using hgen,by simpa only [hqt,hq3] using hfix,hi⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
