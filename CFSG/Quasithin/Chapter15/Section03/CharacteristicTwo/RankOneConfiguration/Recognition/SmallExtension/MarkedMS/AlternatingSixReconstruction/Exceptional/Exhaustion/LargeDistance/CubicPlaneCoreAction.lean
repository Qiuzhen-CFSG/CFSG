module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneKernels

/-!
# Plane-edge control of the original cubic two-core

When the radical image is the plane D, the source Thompson join is the
entire edge kernel at both adjacent component vertices. Its quadratic action
on the full seed puts [Z_c,Q_t] in the actual edge omega-center Z_t. Applying
this along every two-edge path and taking the generated subgroup gives
[V_a,Q_a] <= Z_a. The original selected span consequently has both its core
commutator and its derived subgroup inside the same full seed.

For the normalized paired selectors, this places each full reverse omega
kernel commutator inside the selected edge seed, hence inside both incident
seeds, and fixes it by the whole selected edge kernel. If both backward
containments hold, the preceding paired-kernel theorem shows that some such
commutator is noncentral in the eligible vertex stabilizer. Generation by
the actual local residual and edge kernel then proves nontrivial residual
movement of that very commutator.

The final application uses the existing selectors and the same neighbor
transporter for the strict slice. An escaping seed constructs its backward
critical path with every overlap vertex recorded. Otherwise the explicit
residual obstruction remains. This is a comparison for the plane branch,
not a proof that this obstruction vanishes or a completion of source (5.7).
The Borel branch, terminal contradictions and both core exhaustions remain.
All groups and kernels are on the original cubic graph, and both moving
covers and the nontrivial odd kernel quotient E/Q are retained.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the equal-Thompson case in (5.6)--(5.7), printed pp.917--919;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
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
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- Quadraticity on the full seed puts the entire edge commutator in the
edge omega-center, with the central attachment retained. -/
theorem plane_edge_seed_commutator (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t) :
    ⁅Z Rg c,Q Rg t⁆ ≤ Z Rg t := by
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hct
    rw [hc] at hh
    cases he : color Rg t <;> simp_all
  have hctG : Q Rg t ≤ stabilizer Rg c :=
    fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have hmove : ⁅Z Rg c,Q Rg t⁆ ≤ Z Rg c :=
    le_normalizer_iff_commutator_le_left.mp (hctG.trans (Z_normalized Rg c))
  have hZQ : Z Rg c ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg c ((sourceGeometry h).exists_critical c hc)
    rw [SimpleGraph.dist_self,(sourceGeometry h).distance_constant c hc]
    exact sourceDistance_pos h
  have hquad := remaining_edge_full_seed_quadratic h e hz hk u (Or.inl hR) hc hct
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR hc hct] at hquad
  have hfix := commutator_eq_bot_iff_le_centralizer.mp hquad
  have hZX := (sourceGeometry h).omega_bound c hc (by
    rw [(sourceGeometry h).distance_constant c hc]
    exact sourceDistance_pos h)
  intro v hv
  rw [Z,if_neg (by simp [ht])]
  exact mem_omegaCenter_iff.mpr
    ⟨(hZQ.trans (Q_le_adjacent_h Rg ht hct)) (hmove hv),
      (mem_omegaCenter_iff.mp (hZX (hmove hv))).2.1,hfix hv⟩

include h e hz hk in
private theorem plane_neighbor_core_commutator (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t) :
    ⁅Z Rg c,Q Rg a⁆ ≤ Z Rg t := by
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [ha] at hh
    cases he : color Rg t <;> simp_all
  exact (commutator_mono le_rfl (Q_le_adjacent_h Rg ht hat)).trans
    (plane_edge_seed_commutator h e hz hk u hR hc hct)

include h e hz hk in
/-- In the plane branch, the whole radius is fixed modulo the full seed by
its original two-core. -/
theorem plane_radius_core_commutator (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a : Vertex Rg} (ha : color Rg a = false) :
    ⁅V Rg a,Q Rg a⁆ ≤ Z Rg a := by
  have hb := distance_gt_two h e hz hk
  let I := {c : Vertex Rg // color Rg c = false ∧ (cosetGraph Rg).dist c a ≤ 2}
  have hV : V Rg a = ⨆ c : I,Z Rg c.val := by
    apply le_antisymm
    · apply (V_le_iff Rg ha _).mpr
      intro c hc hca
      exact le_iSup_of_le (⟨c,hc,hca⟩ : I) le_rfl
    · exact iSup_le fun c => le_iSup_of_le c.val (le_iSup_of_le c.property.2 le_rfl)
  rw [hV,commutator_iSup_of_le _ _ (fun c : I =>
    (le_iSup_of_le c.val (le_iSup_of_le c.property.2 le_rfl)).trans
      ((sourceGeometry h).V_le_Q hb a ha))]
  apply iSup_le
  rintro ⟨c,hc,hca⟩
  obtain ⟨w,hw⟩ := (cosetGraph_connected Rg).exists_walk_length_eq_dist c a
  have hlen : w.length ≤ 2 := hw.trans_le hca
  cases w with
  | nil =>
      rw [Z_centralizes_Q Rg a ha]
      exact bot_le
  | @cons c t a hct w =>
      cases w with
      | nil =>
          exact ((adjacent_color_ne Rg ((cosetGraph_adj Rg _ _).mp hct))
            (hc.trans ha.symm)).elim
      | @cons t v a htv w =>
          have hzero : w.length = 0 := by
            simp only [SimpleGraph.Walk.length_cons] at hlen
            omega
          have hva := w.eq_of_length_eq_zero hzero
          subst v
          have hat : Adjacent Rg a t := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp htv)
          exact (plane_neighbor_core_commutator h e hz hk u hR ha hc hat
            ((cosetGraph_adj Rg _ _).mp hct)).trans (adjacent_Z_le Rg ha hat)

include h e hz hk in
/-- Every full reverse omega kernel has its commutator with a neighboring
seed inside the actual edge seed. In particular it is fixed by the entire
edge kernel, with no assertion of centrality in the neighboring stabilizer. -/
theorem plane_reverse_kernel_edge_control (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a c t z : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t) :
    ⁅X Rg z ⊓ Q Rg a,Z Rg c⁆ ≤ Z Rg t ∧
      ⁅X Rg z ⊓ Q Rg a,Z Rg c⁆ ≤ Z Rg a ⊓ Z Rg c ∧
      ⁅⁅X Rg z ⊓ Q Rg a,Z Rg c⁆,Q Rg t⁆ = ⊥ := by
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [ha] at hh
    cases he : color Rg t <;> simp_all
  have hle : ⁅X Rg z ⊓ Q Rg a,Z Rg c⁆ ≤ Z Rg t := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans
      (plane_neighbor_core_commutator h e hz hk u hR ha hc hat hct)
  refine ⟨hle,hle.trans (le_inf (adjacent_Z_le Rg ha hat) (adjacent_Z_le Rg hc hct)),?_⟩
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro v hv
  have he := hle hv
  rw [Z,if_neg (by simp [ht])] at he
  exact (mem_omegaCenter_iff.mp he).2.2

include h e hz hk in
/-- If both backward candidates fail, some full reverse omega-kernel
commutator in the shared edge seed is moved by the actual local residual. -/
theorem plane_paired_backward_residual_obstruction
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hel : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))) :
    ∃ w, (w = z ∨ w = z') ∧
      let H := ⁅X Rg w ⊓ Q Rg (alpha Rg),Z Rg c⁆
      H ≤ Z Rg t ∧ H ≤ Z Rg (alpha Rg) ⊓ Z Rg c ∧
      ⁅H,Q Rg t⁆ = ⊥ ∧ ⁅H,Ltilde Rg c⁆ ≠ ⊥ := by
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hnon := paired_backward_reverse_kernels_not_both_central h e hz hk
    (distance_gt_two h e hz hk) u (Or.inl hR) p q hp hq hat hct hgen hel hbad hbad'
  have hgenC : Ltilde Rg c ⊔ Q Rg t = stabilizer Rg c := by
    apply CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
    · rw [h.relative_residual]
      exact (codisjoint_subgroupOf_sup L R).eq_top
    · exact hc
    · exact hct
  have hcentral (w : Vertex Rg)
      (he : ⁅⁅X Rg w ⊓ Q Rg (alpha Rg),Z Rg c⁆,Ltilde Rg c⁆ = ⊥) :
      ⁅X Rg w ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
        centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
    have hfix := (plane_reverse_kernel_edge_control h e hz hk u hR rfl hc hat hct (z := w)).2.2
    apply le_centralizer_iff.mp
    rw [←hgenC]
    exact sup_le
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hfix))
  by_cases he : ⁅⁅X Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆,Ltilde Rg c⁆ = ⊥
  · have hn : ⁅⁅X Rg z' ⊓ Q Rg (alpha Rg),Z Rg c⁆,Ltilde Rg c⁆ ≠ ⊥ :=
      fun he' => hnon ⟨hcentral z he,hcentral z' he'⟩
    obtain ⟨h₁,h₂,h₃⟩ := plane_reverse_kernel_edge_control h e hz hk u hR rfl hc hat hct (z := z')
    exact ⟨z',Or.inr rfl,h₁,h₂,h₃,hn⟩
  · obtain ⟨h₁,h₂,h₃⟩ := plane_reverse_kernel_edge_control h e hz hk u hR rfl hc hat hct (z := z)
    exact ⟨z,Or.inl rfl,h₁,h₂,h₃,he⟩

include h e hz hk in
/-- The original selected span has both its two-core commutator and its
own derived subgroup in the original seed. -/
theorem plane_selected_span_core_control (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a c : Vertex Rg} (ha : color Rg a = false)
    (hca : (cosetGraph Rg).dist c a ≤ 2) :
    ⁅localZSpan Rg c a,Q Rg a⁆ ≤ Z Rg a ∧
      ⁅localZSpan Rg c a,localZSpan Rg c a⁆ ≤ Z Rg a := by
  have hPV := localZSpan_le_V Rg hca
  have hPQ := hPV.trans ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a ha)
  have hcomm := (commutator_mono hPV le_rfl).trans
    (plane_radius_core_commutator h e hz hk u hR ha)
  exact ⟨hcomm,(commutator_mono le_rfl hPQ).trans hcomm⟩

include h e hz hk in
/-- Apply the reverse-kernel comparison to the actual normalized selectors
and a transported strict slice. If either seed escapes its predecessor core,
construct that backward critical path with every shared vertex recorded.
Otherwise the same full reverse kernel is moved by the actual residual. -/
theorem plane_small_critical_backward_alternative
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hd : Adjacent Rg delta (p.walk.getVert 1))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta)) :
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
              ∀ i ≤ q.walk.length-2, b.walk.getVert (i+2) = q.walk.getVert i) ∨
           (∃ w, (w = z ∨ w = act Rg x z) ∧
              let H := ⁅X Rg w ⊓ Q Rg (alpha Rg),Z Rg c⁆
              H ≤ Z Rg t ∧ H ≤ Z Rg (alpha Rg) ⊓ Z Rg c ∧
              ⁅H,Q Rg t⁆ = ⊥ ∧ ⁅H,Ltilde Rg c⁆ ≠ ⊥)) := by
  obtain ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,_,_,_,_,_,_,_,htransport⟩ :=
    remaining_small_critical_paired_kernel_selectors h e hz hk u (Or.inl hR) p hp
  obtain ⟨g,hg,hgt,hstrict,_⟩ := htransport delta hd hs
  let c := act Rg g delta
  have hct : Adjacent Rg c t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hd
  have hc : color Rg c = false := by
    have h₁ := adjacent_color_ne Rg hat
    have h₂ := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h₁
    cases he : color Rg c <;> cases he' : color Rg t <;> simp_all
  have hb := distance_gt_two h e hz hk
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
  refine ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,g,hg,hgt,hstrict,?_⟩
  by_cases hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2))
  · by_cases hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))
    · right; right
      apply plane_paired_backward_residual_obstruction h e hz hk u hR
        p q hp hqs hat hct hgen _ hbad hbad'
      intro hel
      have he : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) = 1 :=
        relIndex_eq_one.mpr hel
      have hs' : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) := hstrict
      omega
    · exact Or.inr (Or.inl (extend _ q hbad'))
  · exact Or.inl (extend _ p hbad)

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
