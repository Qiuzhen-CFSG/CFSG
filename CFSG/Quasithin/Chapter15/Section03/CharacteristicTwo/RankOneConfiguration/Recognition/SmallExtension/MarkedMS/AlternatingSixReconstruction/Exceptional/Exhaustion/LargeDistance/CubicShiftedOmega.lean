module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaKernel

/-!
# The full shifted omega commutator on the original cubic paths

A small critical transposition normally generates the symmetric local image.
It moves the full omega layer X by the same critical line as U. Passing to
the quotient by U therefore proves [X_a,G_a] = U_a. This keeps the odd
kernel E/Q and does not identify X with its seed orbit Z.

Take consecutive critical four-edge paths a--z and d--c, with midpoints c
and a. The literal shifted term of MS93 (5.12)(1) is
R1 = [U_d intersect Q_c, X_z intersect Q_a]. The backward predecessor line
H- = [Z_d intersect Q_c,Q_a] has order two and contains R1. The pointwise
fixers of the full and seed critical kernels coincide inside G_z. Thus the
seed version of R1 is trivial exactly when R1 is trivial; otherwise both
are H-. This proves their equality without a central-generation premise.

The seed version also lies in the forward line
H+ = [Z_z intersect Q_a,Q_c]. Each predecessor line lies in the full omega
layer at its midpoint. Consequently R1 lies in X_a intersect X_c, and a
nonzero R1 identifies H- with H+. The full local movement identity places
R1 in both U_d and U_z; the radius bounds show that it fixes both radii.

The actual selected-path application retains its original span P and its
central derived line, together with these exact shifted-kernel comparisons.
The whole-core and literal C.1.32 consumers retain both moving covers, the
nonsylow radical and the cubic projection kernel. This does not show that
R1 is nonzero or establish the remaining commutator inequality in (5.12)(1).
The terminal contradiction, other radical branches, natural exhaustion and
both final reconstruction outcomes remain to be proved.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), printed pp.866--867, (5.2)(iii), pp.914--915, and
(5.12)(1), p.924; Aschbacher--Smith C.1.31--32, pp.135--136.
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

include h e hz hk in
/-- A small critical transposition generates the full local omega movement. -/
theorem small_critical_full_omega_movement
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    ⁅centralOmega L R,(⊤ : Subgroup M)⁆ =
      ⁅centralOmega L R,L.subgroupOf M⁆ := by
  let := h.relative_normal
  let W := ⁅centralOmega L R,L.subgroupOf M⁆
  let A := (Z Rg z).comap (embedM Rg)
  have hmA : A.map (embedM Rg) = Z Rg z := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  have hZX : Z Rg z ≤ X Rg z := (sourceGeometry h).omega_bound z p.end_color (by
    rw [(sourceGeometry h).distance_constant _ p.end_color]
    exact sourceDistance_pos h)
  have hline : ⁅X Rg (alpha Rg),Z Rg z⁆ ≤ U Rg (alpha Rg) := by
    apply ((commutator_mono le_rfl hZX).trans_eq
      (small_critical_omega_commutator h e hz hk p hsmall)).trans
    rw [←small_critical_moving_commutator_eq h e hz hk p hsmall]
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
        (sourceDistance_pos h) p.critical).trans (U_normalized (alpha Rg)))
  have hWA : ⁅centralOmega L R,A⁆ ≤ W := by
    apply (map_le_map_iff_of_injective (embedM_injective Rg)).mp
    rw [map_commutator,←graph_X h,hmA,graph_U_map h e hz]
    exact hline
  let q := QuotientGroup.mk' W
  let N := (centralizer ((centralOmega L R).map q : Set (M ⧸ W))).comap q
  let : N.Normal := inferInstance
  have hAN : A ≤ N := by
    have hh : (⁅centralOmega L R,A⁆).map q = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      simpa only [q,QuotientGroup.ker_mk'] using hWA
    rw [map_commutator,commutator_comm] at hh
    exact map_le_iff_le_comap.mp (commutator_eq_bot_iff_le_centralizer.mp hh)
  have hEN : extensionKernel h ≤ N := by
    have hE : ⁅centralOmega L R,extensionKernel h⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hk.ge
    have hh := congrArg (Subgroup.map q) hE
    rw [map_commutator,Subgroup.map_bot,commutator_comm] at hh
    exact map_le_iff_le_comap.mp (commutator_eq_bot_iff_le_centralizer.mp hh)
  let : (N.map π).Normal := (inferInstance : N.Normal).map π
    (CubicEven.projection_surjective h e hz hk)
  obtain ⟨t,ht,hAt⟩ := small_critical_image_eq_swap h e hz hk p hsmall
  have htN : t ∈ N.map π := map_mono hAN (by
    change t ∈ ((Z Rg z).comap (embedM Rg)).map π
    rw [hAt]
    exact mem_zpowers t)
  have hNtop : N.map π = ⊤ := by
    apply top_unique
    rw [←Equiv.Perm.closure_isSwap]
    apply (closure_le _).mpr
    intro y hy
    obtain ⟨i,j,hij,rfl⟩ := ht
    obtain ⟨k,l,hkl,rfl⟩ := hy
    obtain ⟨g,hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hij hkl)
    exact hg ▸ Subgroup.Normal.conj_mem inferInstance _ htN g
  have hNt : N = ⊤ := by
    have hh := congrArg (Subgroup.comap π) hNtop
    rw [comap_map_eq,CubicAction.projection_kernel,comap_top,sup_eq_left.mpr hEN] at hh
    exact hh
  apply le_antisymm _ (commutator_mono le_rfl le_top)
  have hfix : (⊤ : Subgroup M).map q ≤
      centralizer ((centralOmega L R).map q : Set (M ⧸ W)) :=
    map_le_iff_le_comap.mpr hNt.ge
  have hh : (⁅centralOmega L R,(⊤ : Subgroup M)⁆).map q = ⊥ := by
    rw [map_commutator,commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hfix
  simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hh

include h e hz hk in
/-- The full stabilizer moves X by exactly U in the point-core branch. -/
theorem point_omega_stabilizer_commutator
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (a : Vertex Rg) (ha : color Rg a = false) :
    ⁅X Rg a,stabilizer Rg a⁆ = U Rg a := by
  obtain ⟨z,⟨p⟩⟩ := CriticalPath.exists_from (R := Rg) (geometry := sourceGeometry h)
    (a := alpha Rg) rfl
  have hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR p).1]
    decide
  have hh := congrArg (Subgroup.map (embedM Rg))
    (small_critical_full_omega_movement h e hz hk p hsmall)
  rw [map_commutator,map_commutator,←graph_X h,←MonoidHom.range_eq_map,
    show (embedM Rg).range = stabilizer Rg (alpha Rg) from
      (stabilizer_m_base Rg).symm,←graph_component h,←graph_U_eq_X_commutator h e hz] at hh
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color Rg ha
  have hm := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hh
  rw [map_commutator,←X_act,←stabilizer_act,←U_act] at hm
  simpa only [alpha,act_mVertex,one_mul] using hm

include h e hz hk in
/-- The seed-kernel line lies in the midpoint's full omega layer. -/
theorem point_critical_seed_kernel_line_le_midpoint_omega
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    ⁅Z Rg z ⊓ Q Rg a,Q Rg (p.walk.getVert 2)⁆ ≤ X Rg (p.walk.getVert 2) := by
  let c := p.walk.getVert 2
  let H := ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆
  have hcard : Nat.card H = 2 := (point_critical_radius_cross_kernel_line_at h e hz hk u hR p).1
  have hl : p.walk.length = 4 := p.length_eq_b.trans
    (point_image_distance_eq_four h e hz hk u hR)
  have hZQ : Z Rg z ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,hl,(sourceGeometry h).distance_constant _ p.end_color]
    change 4 - 2 < sourceDistance h
    rw [point_image_distance_eq_four h e hz hk u hR]
    decide
  have hHQ : H ≤ Q Rg c := (Subgroup.commutator_le_sup _ _).trans
    (sup_le (inf_le_left.trans hZQ) le_rfl)
  have hfix : Q Rg c ≤ centralizer (H : Set (FreeAmalgam Rg)) :=
    (normalizer_commutator_ge_right _ _).trans
      (normalizer_le_centralizer_of_card_two H hcard)
  have hHX : H ≤ X Rg z :=
    (commutator_mono inf_le_left le_rfl).trans ((le_normalizer_iff_commutator_le_left.mp
      ((Q_le_stabilizer_of_dist_le_two c z
        ((p.vertex_color (by omega)).mpr (by decide)) p.end_color
        (by rw [p.dist_end,hl])).trans (Z_normalized Rg z))).trans
      ((sourceGeometry h).omega_bound z p.end_color (by
        rw [(sourceGeometry h).distance_constant _ p.end_color]
        exact sourceDistance_pos h)))
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hHQ hx,(mem_omegaCenter_iff.mp (hHX hx)).2.1,
    (le_centralizer_iff.mp hfix) hx⟩

include h e hz hk in
/-- All full omega-kernel movement of a subgroup of the starting-radius
kernel stays in the opposite moving cover and centralizes both radii. -/
theorem point_critical_omega_kernel_movement
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (Y : Subgroup (FreeAmalgam Rg)) (hY : Y ≤ V Rg a ⊓ Q Rg (p.walk.getVert 2)) :
    ⁅Y,X Rg z ⊓ Q Rg a⁆ ≤ U Rg z ⊓ Q Rg a ∧
      ⁅Y,X Rg z ⊓ Q Rg a⁆ ≤ centralizer (V Rg a : Set (FreeAmalgam Rg)) ∧
      ⁅Y,X Rg z ⊓ Q Rg a⁆ ≤
        centralizer (V Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let K := X Rg z ⊓ Q Rg a
  let C := ⁅Y,K⁆
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans
    (point_image_distance_eq_four h e hz hk u hR)
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hYG : Y ≤ stabilizer Rg z :=
    (hY.trans inf_le_right).trans (Q_le_stabilizer_of_dist_le_two c z hc p.end_color
      (by rw [p.dist_end,hl]))
  have hYQa : Y ≤ Q Rg a := (hY.trans inf_le_left).trans
    (V_le_Q Rg (geometry := sourceGeometry h) p.start_color hb)
  have hCU : C ≤ U Rg z := by
    rw [←point_omega_stabilizer_commutator h e hz hk u hR z p.end_color,
      commutator_comm (X Rg z)]
    exact commutator_mono hYG inf_le_left
  have hCK : C ≤ K := le_normalizer_iff_commutator_le_right.mp
    ((le_inf (hYG.trans (X_normalized Rg z))
      (hYQa.trans (Q Rg a).le_normalizer)).trans inf_normalizer_le_normalizer_inf)
  exact ⟨le_inf hCU (hCK.trans inf_le_right),
    (commutator_mono (hY.trans inf_le_left) inf_le_right).trans
      (radius_bounds_at h e hz hk a p.start_color z c).1,
    hCK.trans (point_critical_omega_kernels_centralize_midpoint_radius h e hz hk u hR p).2⟩

include h e hz hk in
/-- The source shifted moving subgroup is kept literal. Its full X-kernel
commutator lies in both moving groups, in both cores, and fixes both radii.
The seed-kernel commutator is either trivial or the established midpoint line. -/
theorem point_shifted_omega_kernel_placement
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hd : color Rg d = false) (hda : (cosetGraph Rg).dist d a ≤ 2) :
    let c := p.walk.getVert 2
    let Y := U Rg d ⊓ Q Rg c
    let H := ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆
    let R₁ := ⁅Y,X Rg z ⊓ Q Rg a⁆
    R₁ ≤ (U Rg d ⊓ Q Rg c) ⊓ (U Rg z ⊓ Q Rg a) ∧
      R₁ ≤ centralizer (V Rg a : Set (FreeAmalgam Rg)) ∧
      R₁ ≤ centralizer (V Rg c : Set (FreeAmalgam Rg)) ∧
      (⁅Y,Z Rg z ⊓ Q Rg a⁆ = ⊥ ∨ ⁅Y,Z Rg z ⊓ Q Rg a⁆ = H) ∧
      ⁅Y,Z Rg z ⊓ Q Rg a⁆ ≤ R₁ := by
  let c := p.walk.getVert 2
  let Y := U Rg d ⊓ Q Rg c
  let K := X Rg z ⊓ Q Rg a
  let H := ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆
  let R₁ := ⁅Y,K⁆
  have hUV : U Rg d ≤ V Rg a := (DistanceEight.U_le_Z Rg d).trans
    (le_iSup_of_le d (le_iSup_of_le hda le_rfl))
  have hYV : Y ≤ V Rg a ⊓ Q Rg c := inf_le_inf_right _ hUV
  have hmove := point_critical_omega_kernel_movement h e hz hk u hR p Y hYV
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hKQc : K ≤ Q Rg c := inf_le_left.trans (by
    apply X_le_Q_of_dist_lt Rg (sourceGeometry h) (sourceEdgeCentralizer h e) z p.end_color
    rw [(sourceGeometry h).distance_constant _ p.end_color]
    change (cosetGraph Rg).dist z c < sourceDistance h
    rw [SimpleGraph.dist_comm,p.dist_end,hl,hb]
    decide)
  have hKY : K ≤ normalizer (Y : Set (FreeAmalgam Rg)) :=
    (le_inf ((inf_le_right.trans (Q_le_stabilizer_of_dist_le_two a d p.start_color hd
      (by rwa [SimpleGraph.dist_comm]))).trans (U_normalized d))
      (hKQc.trans (Q Rg c).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hRY : R₁ ≤ Y := le_normalizer_iff_commutator_le_left.mp hKY
  have hseed : ⁅Y,Z Rg z ⊓ Q Rg a⁆ ≤ H := by
    rw [commutator_comm Y]
    exact commutator_mono le_rfl inf_le_right
  have hcard : Nat.card H = 2 := (point_critical_radius_cross_kernel_line_at h e hz hk u hR p).1
  let : Finite H := Nat.finite_of_card_ne_zero (by omega)
  let : Finite (⁅Y,Z Rg z ⊓ Q Rg a⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hseed) (inclusion_injective _)
  refine ⟨le_inf hRY hmove.1,hmove.2.1,hmove.2.2,?_,?_⟩
  · by_cases hn : ⁅Y,Z Rg z ⊓ Q Rg a⁆ = ⊥
    · exact Or.inl hn
    · exact Or.inr (eq_of_le_of_card_ge hseed (by
        change Nat.card H ≤ Nat.card (⁅Y,Z Rg z ⊓ Q Rg a⁆ : Subgroup (FreeAmalgam Rg))
        have hh := (one_lt_card_iff_ne_bot _).mpr hn
        omega))
  · exact commutator_mono le_rfl (inf_le_inf_right _
      ((sourceGeometry h).omega_bound z p.end_color (by
        rw [(sourceGeometry h).distance_constant _ p.end_color]
        exact sourceDistance_pos h)))

include h e hz hk in
/-- On the actual consecutive critical four-edge paths d--c and a--z,
with respective midpoints a and c, the full shifted X-kernel commutator
is bounded by the order-two predecessor line. No X = Z or central-generation
hypothesis is used. -/
theorem point_shifted_omega_kernel_line
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = a) :
    let H := ⁅Z Rg d ⊓ Q Rg c,Q Rg a⁆
    let R₁ := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg a⁆
    Nat.card H = 2 ∧ H ≤ X Rg a ∧
      (R₁ = ⊥ ∨ R₁ = H) ∧
      R₁ ≤ U Rg d ⊓ U Rg z ∧
      R₁ ≤ centralizer (V Rg a : Set (FreeAmalgam Rg)) ∧
      R₁ ≤ centralizer (V Rg c : Set (FreeAmalgam Rg)) ∧
      R₁ = ⁅U Rg d ⊓ Q Rg c,Z Rg z ⊓ Q Rg a⁆ ∧
      R₁ ≤ X Rg a ⊓ X Rg c ∧
      (R₁ ≠ ⊥ → H = ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆) := by
  let H := ⁅Z Rg d ⊓ Q Rg c,Q Rg a⁆
  let R₁ := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg a⁆
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  let qr : CriticalPath Rg (sourceGeometry h) c d :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) d q.start_color
        (by rw [(sourceGeometry h).distance_constant _ q.start_color]; exact sourceDistance_pos h)
        c q.end_color q.critical⟩
  have hqr : qr.walk.getVert 2 = a := by
    change q.walk.reverse.getVert 2 = a
    rw [SimpleGraph.Walk.getVert_reverse,hl]
    exact hqa
  have hqrl : qr.walk.length = 4 := by
    change q.walk.reverse.length = 4
    rw [SimpleGraph.Walk.length_reverse,hl]
  have hdata := point_critical_radius_cross_kernel_line_at h e hz hk u hR qr
  have hcard : Nat.card H = 2 := by simpa only [hqr] using hdata.1
  have hHX : H ≤ X Rg a := by
    simpa only [hqr] using point_critical_seed_kernel_line_le_midpoint_omega h e hz hk u hR qr
  have hmove := (critical_kernel_predecessor_moving h e hz (distance_gt_two h e hz hk) qr).2.2
    (Q Rg a) (by rw [hqrl,show 4-2=2 from rfl,hqr])
  have hRH : R₁ ≤ H := by
    change R₁ ≤ ⁅Z Rg d ⊓ Q Rg c,Q Rg a⁆
    rw [hmove]
    exact commutator_mono le_rfl inf_le_right
  let : Finite H := Nat.finite_of_card_ne_zero (by omega)
  let : Finite R₁ := Finite.of_injective (inclusion hRH) (inclusion_injective _)
  have halt : R₁ = ⊥ ∨ R₁ = H := by
    by_cases hn : R₁ = ⊥
    · exact Or.inl hn
    · exact Or.inr (eq_of_le_of_card_ge hRH (by
        have hh := (one_lt_card_iff_ne_bot _).mpr hn
        omega))
  have hda : (cosetGraph Rg).dist d a ≤ 2 := by
    rw [←hqa,q.dist_start (by omega)]
  have hh := point_shifted_omega_kernel_placement h e hz hk u hR p q.start_color hda
  rw [hpc] at hh
  let J := ⁅U Rg d ⊓ Q Rg c,Z Rg z ⊓ Q Rg a⁆
  have hJR : J ≤ R₁ := commutator_mono le_rfl (inf_le_inf_right _
    ((sourceGeometry h).omega_bound z p.end_color (by
      rw [(sourceGeometry h).distance_constant _ p.end_color]
      exact sourceDistance_pos h)))
  let : Finite J := Finite.of_injective (inclusion hJR) (inclusion_injective _)
  have heq : R₁ = J := by
    by_cases hJ : J = ⊥
    · let pr : CriticalPath Rg (sourceGeometry h) z a :=
        CriticalPath.ofPair p.end_color
          (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) a p.start_color
            (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
            z p.end_color p.critical)
      have hs : (Q Rg a).relIndex (Z Rg z) < 4 := by
        rw [(point_image_critical_indices_two h e hz hk u hR p).2.1]
        decide
      have hYG : U Rg d ⊓ Q Rg c ≤ stabilizer Rg z :=
        inf_le_right.trans (Q_le_stabilizer_of_dist_le_two c z q.end_color p.end_color (by
          rw [←hpc,p.dist_end,show p.walk.length = 4 from p.length_eq_b.trans hb]))
      have hfix : U Rg d ⊓ Q Rg c ≤
          stabilizer Rg z ⊓ centralizer (Z Rg z ⊓ Q Rg a : Set (FreeAmalgam Rg)) :=
        le_inf hYG (commutator_eq_bot_iff_le_centralizer.mp hJ)
      rw [small_critical_kernel_centralizer_eq h e hz hk pr hs,
        ←small_critical_omega_kernel_centralizer h e hz hk pr hs] at hfix
      exact (commutator_eq_bot_iff_le_centralizer.mpr (hfix.trans inf_le_right)).trans hJ.symm
    · have hJl := (one_lt_card_iff_ne_bot J).mpr hJ
      have hRu := card_le_of_le hRH
      exact (eq_of_le_of_card_ge hJR (by omega)).symm
  let Hf := ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆
  have hRF : R₁ ≤ Hf := by
    rw [heq]
    change ⁅U Rg d ⊓ Q Rg c,Z Rg z ⊓ Q Rg a⁆ ≤ Hf
    rw [commutator_comm]
    exact commutator_mono le_rfl inf_le_right
  have hFX : Hf ≤ X Rg c := by
    simpa only [hpc] using point_critical_seed_kernel_line_le_midpoint_omega h e hz hk u hR p
  have hFcard : Nat.card Hf = 2 := by
    simpa only [hpc] using (point_critical_radius_cross_kernel_line_at h e hz hk u hR p).1
  let : Finite Hf := Nat.finite_of_card_ne_zero (by omega)
  have hsame (hne : R₁ ≠ ⊥) : H = Hf := by
    have hRt : R₁ = H := halt.resolve_left hne
    have hRFt : R₁ = Hf := eq_of_le_of_card_ge hRF (by rw [hRt,hcard,hFcard])
    exact hRt.symm.trans hRFt
  exact ⟨hcard,hHX,halt,
    le_inf (hh.1.trans (inf_le_left.trans inf_le_left))
      (hh.1.trans (inf_le_right.trans inf_le_left)),hh.2.1,hh.2.2.1,heq,le_inf (hRH.trans hHX) (hRF.trans hFX),hsame⟩

include h e hz hk in
/-- The original selected span and the full shifted X-kernel term use the
same backward critical path and the same two midpoints. -/
theorem point_image_selected_shifted_omega_line
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    ∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
      ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
        (p.walk.getVert (p.walk.length-2)),
      q.walk.getVert 2 = alpha Rg ∧
      let c := p.walk.getVert (p.walk.length-2)
      let P := localZSpan Rg c (alpha Rg)
      let H := ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆
      let R₁ := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
      Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
      Nat.card H = 2 ∧ H ≤ X Rg (alpha Rg) ∧
      (R₁ = ⊥ ∨ R₁ = H) ∧ R₁ ≤ U Rg d ⊓ U Rg z ∧
      R₁ ≤ centralizer (V Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      R₁ ≤ centralizer (V Rg c : Set (FreeAmalgam Rg)) ∧
      R₁ = ⁅U Rg d ⊓ Q Rg c,Z Rg z ⊓ Q Rg (alpha Rg)⁆ ∧
      R₁ ≤ X Rg (alpha Rg) ⊓ X Rg c ∧
      (R₁ ≠ ⊥ → H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆) := by
  obtain ⟨hb,z,p,_,d,t,x,hx,hxd,_,_,_,q,_,hover,_,_,hcard,hcentral⟩ :=
    point_image_small_central_generating_configuration h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hq2 : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  let qr : CriticalPath Rg (sourceGeometry h) (p.walk.getVert (p.walk.length-2)) d :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) d q.start_color
        (by rw [(sourceGeometry h).distance_constant _ q.start_color]; exact sourceDistance_pos h)
        _ q.end_color q.critical⟩
  have hqr2 : qr.walk.getVert 2 = alpha Rg := by
    change q.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,show q.walk.length = 4 from q.length_eq_b.trans hb]
    exact hq2
  have hd : d ∈ Set.range (fun g : stabilizer Rg (alpha Rg) =>
      act Rg g (p.walk.getVert (p.walk.length-2))) := by
    refine ⟨⟨x,hx⟩,?_⟩
    simpa only [hl,Nat.reduceSub] using hxd
  have hcent : ⁅Z Rg (p.walk.getVert (p.walk.length-2)),Z Rg d⁆ ≤
      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    rwa [commutator_comm]
  have hs := point_selected_span_radius_commutator h e hz hk u hR qr hqr2 hd hcent
  rw [commutator_comm (Z Rg (p.walk.getVert (p.walk.length-2))) (Z Rg d)] at hs
  refine ⟨z,p,d,q,hq2,?_,hs.2.trans_le hcentral,hs.1.trans hs.2.symm,?_⟩
  · rw [hs.2]
    exact hcard
  · exact point_shifted_omega_kernel_line h e hz hk u hR p q
      (by simp only [hl,Nat.reduceSub]) hq2

omit hk in
include h e hz in
/-- Whole-core application on the same selected critical paths. Both covers,
the original nonsylow radical, and the odd cubic kernel are retained. -/
theorem coreExhaustion_or_cubic_shifted_omega_line :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ a : Vertex Rg, color Rg a = false →
            ⁅X Rg a,stabilizer Rg a⁆ = U Rg a) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
          ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
            (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 2 = alpha Rg ∧
          let c := p.walk.getVert (p.walk.length-2)
          let P := localZSpan Rg c (alpha Rg)
          let H := ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆
          let R₁ := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
          Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
          ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
          Nat.card H = 2 ∧ H ≤ X Rg (alpha Rg) ∧
          (R₁ = ⊥ ∨ R₁ = H) ∧ R₁ ≤ U Rg d ⊓ U Rg z ∧
          R₁ ≤ centralizer (V Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          R₁ ≤ centralizer (V Rg c : Set (FreeAmalgam Rg)) ∧
          R₁ = ⁅U Rg d ⊓ Q Rg c,Z Rg z ⊓ Q Rg (alpha Rg)⁆ ∧
          R₁ ≤ X Rg (alpha Rg) ⊓ X Rg c ∧
          (R₁ ≠ ⊥ → H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_radical_cases h e hz with
    hx | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint.2,hpoint.1,
      point_omega_stabilizer_commutator h e hz hk u hpoint.2.le,
      point_image_selected_shifted_omega_line h e hz hk u hpoint.2.le⟩⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- The exact shifted omega/seed comparison in the literal C.1.32 consumer. -/
theorem rankTwo_or_cubic_shifted_omega_line :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ a : Vertex Rg, color Rg a = false →
            ⁅X Rg a,stabilizer Rg a⁆ = U Rg a) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
          ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
            (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 2 = alpha Rg ∧
          let c := p.walk.getVert (p.walk.length-2)
          let P := localZSpan Rg c (alpha Rg)
          let H := ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆
          let R₁ := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
          Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
          ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
          Nat.card H = 2 ∧ H ≤ X Rg (alpha Rg) ∧
          (R₁ = ⊥ ∨ R₁ = H) ∧ R₁ ≤ U Rg d ⊓ U Rg z ∧
          R₁ ≤ centralizer (V Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          R₁ ≤ centralizer (V Rg c : Set (FreeAmalgam Rg)) ∧
          R₁ = ⁅U Rg d ⊓ Q Rg c,Z Rg z ⊓ Q Rg (alpha Rg)⁆ ∧
          R₁ ≤ X Rg (alpha Rg) ⊓ X Rg c ∧
          (R₁ ≠ ⊥ → H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_shifted_omega_line h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
