module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneReciprocalSlice

public import Theory.Representation.BinaryPermutation.ProperInvariant

/-!
# The whole moving cover in the derived core of the cubic plane branch

A generating critical four-edge path with strict backward slice has a
nonabelian selected span: the actual selector gives two critical seeds
inside it. Its small reciprocal slice makes the midpoint-core intersection
have index two and retain its derived line. This line is central at the
start and noncentral at the midpoint.

Every proper invariant subspace of either actual moving cover is fixed by
the full symmetric actor. A stabilizer-normalized subgroup containing a
noncentral piece of the cover therefore contains the whole cover. Applied
to the midpoint two-core's derived subgroup, this retains the order-32
central attachment as well as the order-16 cover.

There must be a strict forward slice at distance four: otherwise the two
end-slice calculation and the actual reverse prefixes give both a strict
and a small reciprocal slice. The original backward selector then supplies
the generating path above. Pulling its derived containment back through
the actual cubic midpoint embedding puts the entire original moved layer
in the original two-core's derived subgroup, of order at least sixteen.
The whole-core and literal C.1.32 applications require only the retained
plane image, distance four and uniformly small critical images; no slice,
selected-path or nonabelian-span premise remains.

This is a lower bound, not the terminal contradiction or either core
exhaustion. The nonsylow radical, full kernel E, odd E/Q and both covers are
retained. The invariant-subspace argument follows the same finite-module
calculation as Natural/SectionFive/MidpointDerivedSaturation; no natural
replacement or graph is identified with this original cubic graph.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.10) and (5.12), printed pp.879--881,924--927;
Aschbacher--Smith B.3.1 and C.1.31--32, printed pp.83,135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk


include h e hz hk in
/-- The two selected critical seeds lie in the same original span. -/
theorem plane_generating_midpoint_span_nonabelian
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hmid : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a)) :
    ⁅localZSpan Rg (p.walk.getVert 2) a,localZSpan Rg (p.walk.getVert 2) a⁆ ≠ ⊥ := by
  obtain ⟨s,has,hgen,g,hg,hgs,q,hq1,hq2,hcontrol⟩ :=
    plane_selected_critical_comparison h e hz hk u hR hb4 hsmall p hmid hback
  let P := localZSpan Rg (p.walk.getVert 2) a
  have hcP : Z Rg (p.walk.getVert 2) ≤ P := Z_le_localZSpan Rg _ _
  have hdP : Z Rg (act Rg g (p.walk.getVert 2)) ≤ P := by
    rw [Z_act]
    exact (map_mono hcP).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized Rg _ _ ((stabilizer Rg a).inv_mem hg)))
  intro hzero
  exact critical_commutator_not_central h e hz hk q
    (((commutator_mono hdP hcP).trans_eq hzero).trans bot_le)

include h e hz hk in
/-- The midpoint-core intersection has index two and retains the same
derived line, central at the start and noncentral at the midpoint. -/
theorem plane_generating_midpoint_span_line
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hmid : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (alpha Rg))) :
    let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
    let Y := P ⊓ Q Rg (p.walk.getVert 2)
    Y.relIndex P = 2 ∧ ⁅Y,Y⁆ = ⁅P,P⁆ ∧
      Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      ¬ ⁅P,P⁆ ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  have hb := distance_gt_two h e hz hk
  have hs := plane_generating_midpoint_reciprocal_slice h e hz hk u hR hb4 hsmall p hmid hback
  have hn := plane_generating_midpoint_span_nonabelian h e hz hk u hR hb4 hsmall p hmid hback
  have hd := small_selected_span_derived h e hz hk hb p (hsmall _ _ p) hs hn
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  let Y := P ⊓ Q Rg (p.walk.getVert 2)
  obtain ⟨s,has,hgen,g,hg,hgs,q,hq1,hq2,hcontrol⟩ :=
    plane_selected_critical_comparison h e hz hk u hR hb4 hsmall p hmid hback
  have hcP : Z Rg (p.walk.getVert 2) ≤ P := Z_le_localZSpan Rg _ _
  have hdP : Z Rg (act Rg g (p.walk.getVert 2)) ≤ P := by
    rw [Z_act]
    exact (map_mono hcP).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized Rg _ _ ((stabilizer Rg (alpha Rg)).inv_mem hg)))
  have hnot : ¬ P ≤ Q Rg (p.walk.getVert 2) := fun hh => q.critical.2 (hdP.trans hh)
  have hPQ := (selected_span_le_forward_kernel (h := h) hb p).trans inf_le_left
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite P := Finite.of_injective
    (inclusion (hPQ.trans (show Q Rg (alpha Rg) ≤ stabilizer Rg (alpha Rg) from fun _ hx => hx.1)))
    (inclusion_injective _)
  have hi : Y.relIndex P = 2 := by
    dsimp only [Y]
    rw [inf_relIndex_left]
    have hlo : 0 < (Q Rg (p.walk.getVert 2)).relIndex P := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hne : (Q Rg (p.walk.getVert 2)).relIndex P ≠ 1 := fun hh => hnot (relIndex_eq_one.mp hh)
    have hup := (selected_span_index_of_forward_slice h e hz hk hb p hs).2
    change (Q Rg (p.walk.getVert 2)).relIndex P ≤ 2 at hup
    omega
  refine ⟨hi,selected_span_derived_transfer h e hz hk hb p hd.2.1 Y inf_le_left hi.le,
    hd.2.1,hd.2.2,?_⟩
  intro hcentral
  have hq := critical_commutator_not_central h e hz hk
    (CriticalPath.ofPair q.end_color (critical_reverse Rg (sourceGeometry h)
      (sourceEdgeCentralizer h e) _ q.start_color (by
        rw [(sourceGeometry h).distance_constant _ q.start_color]
        exact sourceDistance_pos h) _ q.end_color q.critical))
  exact hq ((commutator_mono hcP hdP).trans hcentral)

include h e hz hk in
/-- At distance four some original plane critical path has a strict forward
slice. Otherwise the two end-slice argument contradicts its reverse prefix. -/
theorem plane_exists_strict_forward_slice
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4) :
    ∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
      2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2)) := by
  by_contra! hn
  have hb := distance_gt_two h e hz hk
  have allSmall (a z : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a z) :
      (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ≤ 2 := by
    obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
    have hbase : act Rg g⁻¹ a = alpha Rg := by
      rw [hg,act_mVertex,mul_inv_cancel]
      rfl
    have hpact : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
        (act Rg g⁻¹ a) (act Rg g⁻¹ z),
        p₀.walk.getVert 2 = act Rg g⁻¹ (p.walk.getVert 2) :=
      ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
    rw [hbase] at hpact
    obtain ⟨p₀,hvert⟩ := hpact
    have hB := Escape.PairingControl.FirstPairing.B_act
      (geometry := sourceGeometry h) hb g⁻¹ a p.start_color
    rw [hbase,inv_inv] at hB
    have hi := hn _ p₀
    rw [hvert,U_act,inv_inv,hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
    exact hi
  obtain ⟨z,hzcrit⟩ := criticalPair_exists Rg (alpha Rg) ((sourceGeometry h).exists_critical _ rfl)
  let p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z := CriticalPath.ofPair rfl hzcrit
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  let pr : CriticalPath Rg (sourceGeometry h) z (alpha Rg) :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        (alpha Rg) p.start_color (by
          rw [(sourceGeometry h).distance_constant _ p.start_color]
          exact sourceDistance_pos h) z p.end_color p.critical⟩
  have hpr2 : pr.walk.getVert 2 = p.walk.getVert 2 := by
    change p.walk.reverse.getVert 2 = p.walk.getVert 2
    rw [SimpleGraph.Walk.getVert_reverse,hl]
  obtain ⟨d,q,_,hqa⟩ := (plane_critical_paths h e hz hk u hR p).2.2.1
  obtain ⟨d',q',_,hq'z⟩ := (plane_critical_paths h e hz hk u hR pr).2.2.1
  have hop : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2 := by
    simpa only [hpr2,hq'z] using allSmall _ _ q'
  have hconf := plane_four_selected_configuration_of_slices h e hz hk u hR hb4 p (hn _ p) hop
  have hreverse : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (alpha Rg)) ≤ 2 := by
    simpa only [hqa] using allSmall _ _ q
  exact (Nat.not_lt_of_ge hreverse) hconf.2.2.2.1

local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)
private abbrev originalCoverAction : Representation (ZMod 2) S (Additive W₀) := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation W₀ π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)
private theorem originalCoverAction_conjugate (g : M) (v : Additive W₀) :
    ((originalCoverAction h e hz hk (π g) v).toMul : M) = g*v.toMul*g⁻¹ := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation_apply _ _ _ _ g v

include h e hz hk in
private theorem cover_normal_subgroup_dichotomy
    (N : Subgroup (L ⊔ R : Subgroup G)) [N.Normal] :
    W₀ ≤ N ∨ W₀ ⊓ N ≤ center (L ⊔ R : Subgroup G) := by
  classical
  by_cases hle : W₀ ≤ N
  · exact Or.inl hle
  right
  let W := NormalElementaryQuotient.subspace (W₀)
    (N.subgroupOf (W₀))
  have hW : ∀ g : Equiv.Perm (Fin 6), ∀ v ∈ W, originalCoverAction h e hz hk g v ∈ W := by
    intro g v hv
    obtain ⟨x,rfl⟩ := CubicEven.projection_surjective h e hz hk g
    change ((originalCoverAction h e hz hk (π x) v).toMul : (L ⊔ R : Subgroup G)) ∈ N
    rw [originalCoverAction_conjugate]
    exact (inferInstance : N.Normal).conj_mem _ hv x
  have hproper : W ≠ ⊤ := by
    intro he
    apply hle
    intro x hx
    exact (show Additive.ofMul (⟨x,hx⟩ : W₀) ∈ W from he ▸ Submodule.mem_top)
  have hfixed : ∀ g : Equiv.Perm (Fin 6), ∀ v ∈ W, originalCoverAction h e hz hk g v = v := by
    rcases moved_subgroup_cover_model h e hz hk with ⟨E,hE⟩ | ⟨E,hE⟩
    · let F := W.map E.toLinearMap
      have hF : ∀ g : alternatingGroup (Fin 6), ∀ v ∈ F,
          naturalRepresentation (Fin 6) g.val v ∈ F := by
        rintro g _ ⟨v,hv,rfl⟩
        exact ⟨originalCoverAction h e hz hk g.val v,hW g.val v hv,hE g.val v⟩
      have hnF : F ≠ ⊤ := by
        intro he
        apply hproper
        apply top_unique
        intro v _
        obtain ⟨w,hw,heq⟩ := (show E v ∈ F from he ▸ Submodule.mem_top)
        exact E.injective heq ▸ hw
      have hzF := natural_invariant_eq_bot_of_ne_top (by decide : 5 ≤ Fintype.card (Fin 6)) F hF hnF
      intro g v hv
      have hvF : E v ∈ F := ⟨v,hv,rfl⟩
      rw [hzF] at hvF
      have hv0 : v = 0 := E.injective (((show E v = 0 from hvF)).trans E.map_zero.symm)
      rw [hv0,map_zero]
    · let F := W.map E.toLinearMap
      have hF : ∀ g : alternatingGroup (Fin 6), ∀ v ∈ F,
          coreRepresentation (Fin 6) g.val v ∈ F := by
        rintro g _ ⟨v,hv,rfl⟩
        exact ⟨originalCoverAction h e hz hk g.val v,hW g.val v hv,hE g.val v⟩
      have hnF : F ≠ ⊤ := by
        intro he
        apply hproper
        apply top_unique
        intro v _
        obtain ⟨w,hw,heq⟩ := (show E v ∈ F from he ▸ Submodule.mem_top)
        exact E.injective heq ▸ hw
      intro g v hv
      apply E.injective
      rw [hE]
      exact core_proper_invariant_fixed (by decide : 5 ≤ Fintype.card (Fin 6)) F hF hnF
        g (E v) ⟨v,hv,rfl⟩
  rintro x ⟨hxW,hxN⟩
  apply mem_center_iff.mpr
  intro g
  have hh := congrArg (fun v : Additive (W₀) => (v.toMul : (L ⊔ R : Subgroup G)))
    (hfixed (π g) (Additive.ofMul ⟨x,hxW⟩) hxN)
  rw [originalCoverAction_conjugate] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

include h e hz hk in
/-- A noncentral subgroup of the actual moving cover forces any normal
subgroup containing it to contain the entire cover, including its central line. -/
theorem moving_cover_le_normal_of_noncentral
    {c : Vertex Rg}
    (hcol : color Rg c = false)
    (A N : Subgroup (FreeAmalgam Rg))
    (hAU : A ≤ U Rg c) (hAN : A ≤ N)
    (hN : stabilizer Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)))
    (hne : ¬ A ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))) :
    U Rg c ≤ N := by
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,f,hf,hker,hact⟩ := graph_cover h e hz hk c hcol
  let N₀ := N.comap i
  let : N₀.Normal := ⟨by
    intro x hx g
    change i (g*x*g⁻¹) ∈ N
    rw [map_mul,map_mul,map_inv]
    exact (le_normalizer_iff.mp hN (i g) (hir ▸ (show i g ∈ i.range from ⟨g,rfl⟩))) _ hx⟩
  rcases cover_normal_subgroup_dichotomy h e hz hk N₀ with hle | hcentral
  · rw [←hiU]
    exact (map_mono hle).trans (map_comap_le _ _)
  · exfalso
    apply hne
    intro x hx y hy
    obtain ⟨v,hv,hvx⟩ := (hiU.symm ▸ hAU hx)
    obtain ⟨g,rfl⟩ := hir.symm ▸ hy
    have hvN : v ∈ N₀ := by change i v ∈ N; rw [hvx]; exact hAN hx
    rw [←hvx,←map_mul,←map_mul]
    exact congrArg i ((mem_center_iff.mp (hcentral ⟨hv,hvN⟩)) g)

include h e hz hk in
/-- The actual moving cover lies in the midpoint two-core's derived subgroup
on every generating path with strict backward slice. -/
theorem plane_generating_midpoint_moving_le_derived
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hmid : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (alpha Rg))) :
    U Rg (p.walk.getVert 2) ≤ ⁅Q Rg (p.walk.getVert 2),Q Rg (p.walk.getVert 2)⁆ := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hcol : color Rg (p.walk.getVert 2) = false := (p.vertex_color (by omega)).mpr (by decide)
  have hs := plane_generating_midpoint_reciprocal_slice h e hz hk u hR hb4 hsmall p hmid hback
  have hn := plane_generating_midpoint_span_nonabelian h e hz hk u hR hb4 hsmall p hmid hback
  have hd := plane_generating_midpoint_span_line h e hz hk u hR hb4 hsmall p hmid hback
  have hidentity := small_selected_span_derived h e hz hk hb p (hsmall _ _ p) hs hn
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  apply moving_cover_le_normal_of_noncentral h e hz hk hcol ⁅P,P⁆ _
  · rw [hidentity.1]
    apply le_normalizer_iff_commutator_le_left.mp
    exact (inf_le_left.trans (Q_le_stabilizer_of_dist_two Rg _ _ rfl
      (p.dist_start (by omega)))).trans (U_normalized _)
  · rw [←hd.2.1]
    exact commutator_mono inf_le_right inf_le_right
  · intro x hx
    rw [mem_normalizer_iff_map_conj_eq,map_commutator]
    have hQ := mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg (p.walk.getVert 2) hx)
    exact congrArg₂ (fun A B : Subgroup (FreeAmalgam Rg) => ⁅A,B⁆) hQ hQ
  · exact hd.2.2.2.2

include h e hz hk in
private theorem original_derived_of_generating_midpoint
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hmid : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a)) :
    W₀ ≤ ⁅pCore 2 M,pCore 2 M⁆ := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hcol : color Rg (p.walk.getVert 2) = false := (p.vertex_color (by omega)).mpr (by decide)
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ a) (act Rg g⁻¹ z),
      ∀ i, p₀.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i) :=
    ⟨p.act g⁻¹,fun _ => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hverts⟩ := hpact
  have hmid₀ : Q Rg (p₀.walk.getVert 1) ⊔ Q Rg (p₀.walk.getVert 3) =
      stabilizer Rg (p₀.walk.getVert 2) := by
    rw [hverts 1,hverts 3,hverts 2,Q_act,Q_act,stabilizer_act,←Subgroup.map_sup,hmid]
  have hback₀ : 2 < (B Rg (p₀.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (alpha Rg)) := by
    rw [hverts 2,Escape.PairingControl.FirstPairing.B_act hb g⁻¹ _ hcol,←hbase,U_act,
      relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hback
  have hderived := plane_generating_midpoint_moving_le_derived h e hz hk u hR hb4 hsmall
    p₀ hmid₀ hback₀
  have hcol₀ : color Rg (p₀.walk.getVert 2) = false := by
    rw [hverts 2,action_preserves_color]
    exact hcol
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,f,hf,hker,hact⟩ := graph_cover h e hz hk _ hcol₀
  apply (map_le_map_iff_of_injective hi).mp
  rw [hiU,map_commutator,hiQ]
  exact hderived

include h e hz hk in
/-- The small-critical-image distance-four plane branch forces the entire
original moved cover into the derived subgroup of the original two-core.
No slice, selected path or nonabelian-span premise remains. -/
theorem plane_four_small_images_derived_core
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    W₀ ≤ ⁅pCore 2 M,pCore 2 M⁆ ∧
      16 ≤ Nat.card (⁅pCore 2 M,pCore 2 M⁆ : Subgroup M) := by
  obtain ⟨z,p,hstrict⟩ := plane_exists_strict_forward_slice h e hz hk u hR hb4
  obtain ⟨d,c,q,hqa,hmid,hback,_⟩ :=
    plane_selected_backward_small_slice h e hz hk u hR hb4 hsmall p hstrict
  have hle := original_derived_of_generating_midpoint h e hz hk u hR hb4 hsmall q
    (by rwa [hqa]) (by rwa [hqa])
  refine ⟨hle,?_⟩
  have hcard := card_le_of_le hle
  rcases moved_card h e hz hk with hcardU | hcardU <;> rw [hcardU] at hcard <;> omega

omit hk in
include h e hz in
/-- Whole-core consumer of the original derived-core obstruction. The
remaining plane hypotheses and Borel branch remain explicit. -/
theorem coreExhaustion_or_cubic_plane_derived_core :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          W₀ ≤ ⁅pCore 2 M,pCore 2 M⁆ ∧
            16 ≤ Nat.card (⁅pCore 2 M,pCore 2 M⁆ : Subgroup M))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_four_small_images_derived_core h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application with the original two-core and full moved
cover. This lower bound is not the exceptional core exhaustion. -/
theorem rankTwo_or_cubic_plane_derived_core :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          W₀ ≤ ⁅pCore 2 M,pCore 2 M⁆ ∧
            16 ≤ Nat.card (⁅pCore 2 M,pCore 2 M⁆ : Subgroup M))) :=
  (coreExhaustion_or_cubic_plane_derived_core h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
