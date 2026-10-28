module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicThompsonSelectors

/-!
# Retaining the preceding cubic Thompson selector

Let a--z be the preceding critical path, with midpoint c, and let d--c
be its selected backward path, with midpoint a. Retain the same generating
edge and the element of G_a carrying c to d. The critical line [Z_d,Z_c]
is central in G_a. The reverse-kernel line H = [Z_c intersect Q_d,Q_a]
lies in that critical line joined to the central attachment at c.

If H were central in G_d, both summands would put it in the forward edge
seed of a--z. The literal Thompson centralizer bound then makes it central
in G_a. Transport by the retained midpoint conjugator makes it central in
G_c, contradicting the augmentation-cover kernel calculation. Thus H is
not central in G_d.

For any further generating critical path v--a with midpoint d, a nonzero
[U_v intersect Q_a,X_c intersect Q_d] would be H and central in G_d.
It therefore vanishes, giving the full-X comparison in MS93 (5.12)(1)
for these three compatible critical paths. The same argument excludes a
strict forward slice on d--c, so its index is exactly two. The actual
point-branch construction and both whole-core and C.1.32 applications
retain the preceding selector and the same-pair marking X_c = Z_c; the
exceptional two-transvection marking is excluded on that pair.

This does not construct a preceding selector for an arbitrary strict path,
or prove the comparison before the third path is critical. The source
selection and terminal point contradiction remain necessary, as do the
plane/Sylow exclusions, natural exhaustion and both final reconstruction
outcomes. All actions remain on the original cubic graph, with projection
kernel E, its nontrivial odd quotient E/Q, and both moving cover sizes.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(b),(c), p.915, the choices on p.919, and (5.12)(1),
pp.924--925; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf M
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk

private theorem central_omega_le_incident_seed {a t : Vertex Rg}
    (ha : color Rg a = false) (hat : Adjacent Rg a t) :
    X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) ≤ Z Rg t := by
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [ha] at hh
    cases he : color Rg t <;> simp_all
  have hQa : Q Rg a ≤ Q Rg t := Q_le_adjacent_h Rg ht hat
  have htG : Q Rg t ≤ stabilizer Rg a := fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  intro x hx
  have hxX : x ∈ omegaCenter (Q Rg a) := hx.1
  rw [Z,if_neg (by simp [ht])]
  exact mem_omegaCenter_iff.mpr ⟨hQa (mem_omegaCenter_iff.mp hxX).1,
    (mem_omegaCenter_iff.mp hxX).2.1,fun y hy => hx.2 y (htG hy)⟩

include h e hz hk in
/-- Retaining the preceding generating edge prevents the reverse-kernel
line from being central at the selected backward endpoint. -/
theorem point_selected_backward_kernel_not_central
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = alpha Rg)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg))
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (alpha Rg))
    (hgc : act Rg g c = d) :
    ¬ ⁅Z Rg c ⊓ Q Rg d,Q Rg (alpha Rg)⁆ ≤
      centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) := by
  intro hHd
  let H := ⁅Z Rg c ⊓ Q Rg d,Q Rg (alpha Rg)⁆
  let D₀ := ⁅Z Rg d,Z Rg c⁆
  let C := U Rg c ⊓ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))
  let b := p.walk.getVert 1
  let t := q.walk.getVert 1
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hab : Adjacent Rg (alpha Rg) b := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  have hcb : Adjacent Rg c b := by
    rw [←hpc]
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hat : Adjacent Rg (alpha Rg) t := by
    rw [←hqa]
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have hdt : Adjacent Rg d t := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (cosetGraph_adj Rg _ _).mp (q.walk.adj_getVert_succ (i := 0) (by omega))
  have hda : (cosetGraph Rg).dist d (alpha Rg) ≤ 2 := by
    rw [←hqa,q.dist_start (by omega)]
  have hca : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    rw [←hpc,SimpleGraph.dist_comm,p.dist_start (by omega)]
  have hDc : D₀ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    selected_critical_commutator_central h e hz hk u hR q p hda hca
      (by rw [←hpc,p.dist_end,hl,hb]; decide) hgen
  have hdV : Z Rg d ≤ V Rg (alpha Rg) :=
    le_iSup_of_le d (le_iSup_of_le hda le_rfl)
  have hcV : Z Rg c ≤ V Rg (alpha Rg) :=
    le_iSup_of_le c (le_iSup_of_le hca le_rfl)
  have hDX : D₀ ≤ X Rg (alpha Rg) :=
    (commutator_mono hdV hcV).trans
      (radius_bounds_at h e hz hk (alpha Rg) rfl d c).2.1
  have hDb : D₀ ≤ Z Rg b :=
    (le_inf hDX hDc).trans (central_omega_le_incident_seed rfl hab)
  have hCX : C ≤ X Rg c := inf_le_left.trans ((DistanceEight.U_le_Z Rg c).trans
    ((sourceGeometry h).omega_bound c q.end_color (by
      rw [(sourceGeometry h).distance_constant _ q.end_color]
      exact sourceDistance_pos h)))
  have hCb : C ≤ Z Rg b :=
    (le_inf hCX inf_le_right).trans (central_omega_le_incident_seed q.end_color hcb)
  have hHD : H ≤ D₀ ⊔ C := by
    have hh := (point_critical_midpoint_attachment_plane h e hz hk u hR q).2.1
    rw [hqa] at hh
    exact le_sup_left.trans hh.le
  have hHt : H ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) :=
    hHd.trans (centralizer_le (fun _ hx => hx.2 _ (adjacent_symm Rg hdt)))
  have hHa : H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    have hh := point_selected_thompson_centralizer h e hz hk u hR p hat hgen
    rw [point_edgeOffenderJoin_eq h e hz hk u hR rfl hat] at hh
    exact (le_inf (hHD.trans (sup_le hDb hCb)) hHt).trans hh
  have hfixed : H.map (MulAut.conj g).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hHa hg))
  have hback : (stabilizer Rg d).map (MulAut.conj g).toMonoidHom =
      stabilizer Rg c := by
    have hh := stabilizer_act Rg g⁻¹ d
    rw [inv_inv] at hh
    rw [←hh,←hgc,←act_mul,mul_inv_cancel,act_one]
  have hHc : H ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
    have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hHd).trans
      (map_centralizer_le_centralizer_image _ _)
    rwa [hfixed,←Subgroup.coe_map,hback] at hh
  have hcard : Nat.card H = 2 := by
    simpa only [hqa] using (point_critical_radius_cross_kernel_line_at h e hz hk u hR q).1
  have hne : H ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hcard
    omega
  have hs : (Q Rg c).relIndex (Z Rg d) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR q).1]
    decide
  have hh := four_kernel_core_noncentral h e hz hk hb q hs
  rw [hqa] at hh
  exact hh hne hHc




include h e hz hk in
/-- The full marked omega comparison for three compatible critical paths.
The preceding selector is retained, rather than inferred from the last two paths. -/
theorem point_selected_backward_full_omega_control
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z c d v : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (r : CriticalPath Rg (sourceGeometry h) v (alpha Rg))
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = alpha Rg)
    (hrd : r.walk.getVert 2 = d)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg))
    (hgen' : Q Rg (r.walk.getVert 1) ⊔ Z Rg c = stabilizer Rg d)
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (alpha Rg))
    (hgc : act Rg g c = d) :
    ⁅U Rg v ⊓ Q Rg (alpha Rg),X Rg c ⊓ Q Rg d⁆ = ⊥ ∧
      ⁅U Rg v ⊓ Q Rg (alpha Rg),X Rg c⁆ ≤ ⁅Z Rg d,Z Rg c⁆ := by
  have hzero : ⁅U Rg v ⊓ Q Rg (alpha Rg),X Rg c ⊓ Q Rg d⁆ = ⊥ := by
    by_contra hn
    have hh := point_shifted_omega_kernel_line h e hz hk u hR q r hqa hrd
    have he := (hh.2.2.1.resolve_left hn).trans (hh.2.2.2.2.2.2.2.2 hn)
    have hc := (point_generating_shifted_kernel_central h e hz hk u hR q r
      hqa hrd hgen').2.1
    rw [he] at hc
    exact point_selected_backward_kernel_not_central h e hz hk u hR p q
      hpc hqa hgen g hg hgc hc
  have hb := (point_shifted_full_omega_control_iff h e hz hk u hR q r hqa hrd).mpr hzero
  rw [hzero,sup_bot_eq] at hb
  exact ⟨hzero,hb⟩

include h e hz hk in
private theorem point_strict_forward_kernel_central_at
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hlarge : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) :
    ⁅Z Rg z ⊓ Q Rg a,Q Rg (p.walk.getVert 2)⁆ ≤
      centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hi : 2 < (B Rg (act Rg g⁻¹ a) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg g⁻¹ (p.walk.getVert 2))) := by
    rw [Escape.PairingControl.FirstPairing.B_act (distance_gt_two h e hz hk)
      _ _ p.start_color,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  have hp : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ a) (act Rg g⁻¹ z),
      p₀.walk.getVert 2 = act Rg g⁻¹ (p.walk.getVert 2) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hp hi
  obtain ⟨p₀,hp₀⟩ := hp
  have hi₀ : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p₀.walk.getVert 2)) := by rwa [hp₀]
  obtain ⟨d,q,hqa,hgen,hback,hfull,hcard,hcent,hrest⟩ :=
    point_strict_forward_attachment h e hz hk u hR p₀ hi₀
  have hl : p₀.walk.length = 4 := p₀.length_eq_b.trans
    (point_image_distance_eq_four h e hz hk u hR)
  rw [hfull,hl,show 4-2=2 from rfl,hp₀,←hbase] at hcent
  rw [Z_act,Q_act,Q_act,stabilizer_act,inv_inv,
    ←Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    ←map_commutator] at hcent
  intro x hx y hy
  apply (MulAut.conj g).injective
  simpa only [map_mul,MulEquiv.coe_toMonoidHom] using hcent (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
    _ (mem_map_of_mem (MulAut.conj g).toMonoidHom hy)

include h e hz hk in
/-- The previous Thompson selector forces the next forward slice to have
index two. A strict slice would make its nonzero kernel line central at
both conjugate endpoints, contradicting the full-cover calculation. -/
theorem point_selected_backward_slice_eq_two
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = alpha Rg)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg))
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (alpha Rg))
    (hgc : act Rg g c = d) :
    (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) = 2 := by
  have hle : (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) ≤ 2 := by
    by_contra! hlarge
    have hh := point_strict_forward_kernel_central_at h e hz hk u hR q
      (by rwa [hqa])
    rw [hqa] at hh
    exact point_selected_backward_kernel_not_central h e hz hk u hR p q
      hpc hqa hgen g hg hgc hh
  let := finite_Z Rg (alpha Rg)
  let : Finite (U Rg (alpha Rg)) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg _)) (inclusion_injective _)
  have hne0 : (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) ≠ 0 :=
    index_ne_zero_of_finite
  have hne1 : (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) ≠ 1 := by
    intro he
    apply full_point_critical_forward_eligible h e hz hk (distance_gt_two h e hz hk) u
      (full_point_image_of_contained h e hz hk u hR) q
    rw [hqa]
    exact relIndex_eq_one.mp he
  omega

include h e hz hk in
/-- The original point branch supplies the preceding selector, its literal
midpoint conjugator, and full-X control for every compatible next choice.
No later commutator comparison is assumed. -/
theorem point_image_compatible_forward_control
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    ∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
      ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
        localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ ∧
      ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
      ∃ g ∈ stabilizer Rg (alpha Rg),
        act Rg g (p.walk.getVert 2) = d ∧
        q.walk.getVert 2 = alpha Rg ∧
        Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
        (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) = 2 ∧
        (¬ Source.SplitCriticalImage d (p.walk.getVert 2) ∧
          X Rg (p.walk.getVert 2) = Z Rg (p.walk.getVert 2)) ∧
        (∀ v, ∀ r : CriticalPath Rg (sourceGeometry h) v (alpha Rg),
          r.walk.getVert 2 = d →
          Q Rg (r.walk.getVert 1) ⊔ Z Rg (p.walk.getVert 2) = stabilizer Rg d →
          ⁅U Rg v ⊓ Q Rg (alpha Rg),X Rg (p.walk.getVert 2) ⊓ Q Rg d⁆ = ⊥ ∧
          ⁅U Rg v ⊓ Q Rg (alpha Rg),X Rg (p.walk.getVert 2)⁆ ≤
            ⁅Z Rg d,Z Rg (p.walk.getVert 2)⁆) := by
  obtain ⟨hb,z,p,hnon,d,t,g,hg,hgc,hat,hdt,hgen,q,hqt,hover,hrest⟩ :=
    point_image_small_central_generating_configuration h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hpc : p.walk.getVert 2 = p.walk.getVert (p.walk.length-2) := by rw [hl]
  have hqa : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hgen' : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) := by rwa [hqt]
  have hgc' : act Rg g (p.walk.getVert (p.walk.length-2)) = d := by rwa [←hpc]
  have hslice := point_selected_backward_slice_eq_two h e hz hk u hR p q hpc hqa hgen' g hg hgc'
  have hmark := point_critical_marked_actor h e hz hk u hR q
  have hcontrol := fun v (r : CriticalPath Rg (sourceGeometry h) v (alpha Rg))
      (hrd : r.walk.getVert 2 = d)
      (hgenr : Q Rg (r.walk.getVert 1) ⊔ Z Rg (p.walk.getVert (p.walk.length-2)) = stabilizer Rg d) =>
    point_selected_backward_full_omega_control h e hz hk u hR p q r hpc hqa hrd hgen' hgenr g hg hgc'
  have hout : ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
      ∃ g ∈ stabilizer Rg (alpha Rg),
        act Rg g (p.walk.getVert (p.walk.length-2)) = d ∧
        q.walk.getVert 2 = alpha Rg ∧
        Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
        (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) = 2 ∧
        (¬ Source.SplitCriticalImage d (p.walk.getVert (p.walk.length-2)) ∧
          X Rg (p.walk.getVert (p.walk.length-2)) = Z Rg (p.walk.getVert (p.walk.length-2))) ∧
        (∀ v, ∀ r : CriticalPath Rg (sourceGeometry h) v (alpha Rg),
          r.walk.getVert 2 = d →
          Q Rg (r.walk.getVert 1) ⊔ Z Rg (p.walk.getVert (p.walk.length-2)) = stabilizer Rg d →
          ⁅U Rg v ⊓ Q Rg (alpha Rg),X Rg (p.walk.getVert (p.walk.length-2)) ⊓ Q Rg d⁆ = ⊥ ∧
          ⁅U Rg v ⊓ Q Rg (alpha Rg),X Rg (p.walk.getVert (p.walk.length-2))⁆ ≤
            ⁅Z Rg d,Z Rg (p.walk.getVert (p.walk.length-2))⁆) :=
    ⟨q,g,hg,hgc',hqa,hgen',hslice,hmark,hcontrol⟩
  rw [←hpc] at hout
  exact ⟨z,p,hnon,d,hout⟩

omit hk in
include h e hz in
/-- Whole-core application retaining the preceding selector and the marked
comparison, with both covers and the plane/Sylow alternatives unchanged. -/
theorem coreExhaustion_or_cubic_forward_selectors :
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
            Nat.card (U Rg a) = 32 ∧
            Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
              Subgroup (FreeAmalgam Rg)) = 2) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
              localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ ∧
            ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
            ∃ g ∈ stabilizer Rg (alpha Rg),
              act Rg g (p.walk.getVert 2) = d ∧
              q.walk.getVert 2 = alpha Rg ∧
              Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
              (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) = 2 ∧
              (¬ Source.SplitCriticalImage d (p.walk.getVert 2) ∧
                X Rg (p.walk.getVert 2) = Z Rg (p.walk.getVert 2)) ∧
              (∀ v, ∀ r : CriticalPath Rg (sourceGeometry h) v (alpha Rg),
                r.walk.getVert 2 = d →
                Q Rg (r.walk.getVert 1) ⊔ Z Rg (p.walk.getVert 2) = stabilizer Rg d →
                ⁅U Rg v ⊓ Q Rg (alpha Rg),X Rg (p.walk.getVert 2) ⊓ Q Rg d⁆ = ⊥ ∧
                ⁅U Rg v ⊓ Q Rg (alpha Rg),X Rg (p.walk.getVert 2)⁆ ≤
                  ⁅Z Rg d,Z Rg (p.walk.getVert 2)⁆))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_thompson_selectors h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint.1,hpoint.2.1,hpoint.2.2.1,
      point_image_compatible_forward_control h e hz hk u hpoint.1.le⟩⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the compatible source comparison. -/
theorem rankTwo_or_cubic_forward_selectors :
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
            Nat.card (U Rg a) = 32 ∧
            Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
              Subgroup (FreeAmalgam Rg)) = 2) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
              localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ ∧
            ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
            ∃ g ∈ stabilizer Rg (alpha Rg),
              act Rg g (p.walk.getVert 2) = d ∧
              q.walk.getVert 2 = alpha Rg ∧
              Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
              (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) = 2 ∧
              (¬ Source.SplitCriticalImage d (p.walk.getVert 2) ∧
                X Rg (p.walk.getVert 2) = Z Rg (p.walk.getVert 2)) ∧
              (∀ v, ∀ r : CriticalPath Rg (sourceGeometry h) v (alpha Rg),
                r.walk.getVert 2 = d →
                Q Rg (r.walk.getVert 1) ⊔ Z Rg (p.walk.getVert 2) = stabilizer Rg d →
                ⁅U Rg v ⊓ Q Rg (alpha Rg),X Rg (p.walk.getVert 2) ⊓ Q Rg d⁆ = ⊥ ∧
                ⁅U Rg v ⊓ Q Rg (alpha Rg),X Rg (p.walk.getVert 2)⁆ ≤
                  ⁅Z Rg d,Z Rg (p.walk.getVert 2)⁆))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_forward_selectors h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
