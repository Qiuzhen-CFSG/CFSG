module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSuccessiveKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusPair

/-!
# Shifted-kernel comparison before critical-candidate selection

For the critical path a--v--c--t--z, the preceding segment d--s--a need
not extend to another critical path. Retain the generating edge cores at
a and c, the element of G_a carrying c to d, and the strict midpoint
slice. The full shifted kernels still commute, and every subgroup of
Z_d intersect Q_c moves Z_z only along the original critical line.

If Z_d escapes Q_c, minimum critical distance makes the raw four-edge
walk critical and the existing comparison applies. Otherwise its kernel
is all Z_d. The edge supplement replaces the full-seed commutator by
[U_d,F]. The same generating-edge argument makes this commutator central
in G_d. The faithful natural quotient kills it, and the full permutation
kernel centralizes U_d, so the commutator itself vanishes. The full
central attachment is retained throughout.

The normalized joint selector supplies the next generating edge without
a strict-slice assumption. Neighbor transitivity supplies its transporter.
Applied to the retained outer backward path, this constructs the next raw
comparison with no extra next-path premise. It does not yet assert that
this raw candidate is critical. The later candidate selection, terminal
exclusion, both whole-core exhaustions and final reconstruction remain open.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.12)(1) before the next critical-pair selection, printed pp.924--925;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
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


local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)

include h e hz hk in
/-- A central commutator on the full moving cover vanishes: the natural
quotient is faithful with the same action kernel as the whole cover. -/
theorem graph_moving_central_commutator_eq_bot
    {d : Vertex Rg} (hd : color Rg d = false)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ stabilizer Rg d)
    (hc : ⁅U Rg d,A⁆ ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg))) :
    ⁅U Rg d,A⁆ = ⊥ := by
  obtain ⟨i,hi,hr,hQ,hE,hW,f,hf,hker,hequiv⟩ := graph_cover h e hz hk d hd
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  intro y hy
  obtain ⟨g,rfl⟩ := hr.symm ▸ hA hy
  have hgn : i g ∈ normalizer (U Rg d : Set (FreeAmalgam Rg)) :=
    U_normalized d (hA hy)
  have hpi : π g = 1 := by
    apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
    rw [map_one]
    ext v : 1
    obtain ⟨v,rfl⟩ := hf (Multiplicative.ofAdd v)
    let w : U Rg d := ⟨i g * v * (i g)⁻¹,
      (mem_normalizer_iff.mp hgn v).mp v.property⟩
    have hcomm : (w * v⁻¹ : U Rg d) ∈ f.ker := by
      rw [hker]
      apply hc
      change ⁅i g,(v : FreeAmalgam Rg)⁆ ∈ ⁅U Rg d,A⁆
      rw [commutator_comm]
      exact commutator_mem_commutator hy v.property
    have he : f w = f v := by
      have hh : f (w * v⁻¹) = 1 := hcomm
      simpa only [map_mul,map_inv,mul_inv_eq_one] using hh
    exact (hequiv g v w rfl).symm.trans (congrArg Multiplicative.toAdd he)
  have hgC : g ∈ centralizer (W₀ : Set M) := by
    rw [←CubicAction.moved_projection_kernel h e hz hk]
    exact hpi
  intro v hv
  obtain ⟨w,hw,rfl⟩ := hW.symm ▸ hv
  simpa only [map_mul] using congrArg i (hgC w hw)

include h e hz hk in
/-- Full shifted-kernel control for a raw preceding two-edge segment.
The first path is critical; the preceding four-edge walk need not be. -/
theorem plane_raw_shifted_kernels_of_midpoint_generation
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    {s : Vertex Rg} (hds : Adjacent Rg d s) (has : Adjacent Rg a s)
    (K : Subgroup (FreeAmalgam Rg)) (hK : K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2))
    (hgen : Q Rg s ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a)
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg a)
    (hgd : act Rg g (p.walk.getVert 2) = d)
    (hmidgen : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a)) :
    ⁅K,Z Rg z ⊓ Q Rg a⁆ = ⊥ ∧ ⁅K,Z Rg z⁆ ≤ ⁅Z Rg a,Z Rg z⁆ := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hsc : color Rg s = true := by
    have hh := adjacent_color_ne Rg has
    rw [p.start_color] at hh
    cases he : color Rg s <;> simp_all
  have hd : color Rg d = false := by
    have hh := adjacent_color_ne Rg hds
    rw [hsc] at hh
    cases he : color Rg d <;> simp_all
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  let w : (cosetGraph Rg).Walk d a :=
    .cons ((cosetGraph_adj Rg _ _).mpr hds)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg has)) .nil)
  have hw : w.length = 2 := rfl
  by_cases hn : Z Rg d ≤ Q Rg (p.walk.getVert 2)
  swap
  · have hns : ¬ Z Rg d ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
      simpa only [hl,Nat.reduceSub] using hn
    let q := p.prepend_two (Nat.le_of_lt hb) hd w hw hns
    have he : p.walk.getVert (p.walk.length-2) = p.walk.getVert 2 := by rw [hl]
    have hq : ∃ q : CriticalPath Rg (sourceGeometry h) d
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = s ∧ q.walk.getVert 2 = a := by
      refine ⟨q,?_,?_⟩
      · simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
          hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
          SimpleGraph.Walk.getVert_zero]
      · simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
          p.prepend_two_overlap (Nat.le_of_lt hb) hd w hw hns (i := 0) (by omega)
    rw [he] at hq
    obtain ⟨q,hq1,hq2⟩ := hq
    exact plane_shifted_kernels_of_midpoint_generation h e hz hk u hR hb4 hsmall
      p q hq2 K hK (by rwa [hq1]) g hg hgd hmidgen hback
  let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆
  have hda : (cosetGraph Rg).dist d a ≤ 2 := (cosetGraph Rg).dist_le w
  have hDV : Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≤ V Rg a :=
    inf_le_left.trans (le_iSup_of_le d (le_iSup_of_le hda le_rfl))
  have hHa : H ≤ Z Rg a :=
    (commutator_mono hDV inf_le_right).trans
      (plane_radius_core_commutator h e hz hk u hR p.start_color)
  have hav : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcv : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg (p.walk.getVert 3) <;> simp_all
  have hDt : Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≤ Q Rg (p.walk.getVert 3) :=
    inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hHt : H ≤ Z Rg (p.walk.getVert 3) := by
    rw [show H = ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆ from rfl,
      commutator_comm]
    exact (commutator_mono inf_le_left hDt).trans
      (plane_edge_seed_commutator h e hz hk u hR p.end_color hzt)
  have hHc : H ≤ Z Rg (p.walk.getVert 2) := hHt.trans
    (adjacent_Z_le Rg hc hct)
  have hHv : H ≤ Z Rg (p.walk.getVert 1) :=
    (le_inf hHa hHc).trans_eq
      (plane_strict_slice_eq_edge h e hz hk u hR hc p.start_color hcv hav hback).2.1
  have hHs : H ≤ Z Rg s :=
    (commutator_mono inf_le_left (inf_le_right.trans (Q_le_adjacent_h Rg hsc has))).trans
      (plane_edge_seed_commutator h e hz hk u hR hd hds)
  have hcA : H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :=
    (le_inf hHs hHv).trans
      ((plane_generating_edge_seed_intersection h e hz hk u hR p.start_color
        has hav hgen).le.trans inf_le_right)
  have hcC : H ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) :=
    (le_inf hHv hHt).trans
      ((plane_generating_edge_seed_intersection h e hz hk u hR hc hcv hct hmidgen).le.trans
        inf_le_right)
  have hm : H.map (MulAut.conj g⁻¹).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp
      ((le_centralizer_iff.mp hcA).trans (Subgroup.centralizer_le_normalizer _)
        ((stabilizer Rg a).inv_mem hg))
  have hcD := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hcC).trans
    (map_centralizer_le_centralizer_image _ _)
  change H.map (MulAut.conj g⁻¹).toMonoidHom ≤
    centralizer (((stabilizer Rg (p.walk.getVert 2)).map
      (MulAut.conj g⁻¹).toMonoidHom) : Set (FreeAmalgam Rg)) at hcD
  rw [hm,←stabilizer_act,hgd] at hcD
  have hFs : Z Rg z ⊓ Q Rg a ≤ Q Rg s :=
    inf_le_right.trans (Q_le_adjacent_h Rg hsc has)
  have hFG : Z Rg z ⊓ Q Rg a ≤ stabilizer Rg d :=
    hFs.trans (fun _ hv => hv.2 _ (adjacent_symm Rg hds))
  have hHU : H = ⁅U Rg d,Z Rg z ⊓ Q Rg a⁆ := by
    change ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆ = _
    rw [inf_eq_left.mpr hn]
    exact full_seed_commutator_eq_moving h e hz hd hds _ hFs
  have he : H = ⊥ := hHU.trans
    (graph_moving_central_commutator_eq_bot h e hz hk hd _ hFG (hHU ▸ hcD))
  have hKF : ⁅K,Z Rg z ⊓ Q Rg a⁆ = ⊥ :=
    bot_unique ((commutator_mono hK le_rfl).trans_eq he)
  have hKG : K ≤ stabilizer Rg z :=
    (hK.trans hDt).trans (fun _ hx => hx.2 _ (adjacent_symm Rg hzt))
  exact ⟨hKF,small_critical_kernel_commutator h e hz hk p (hsmall _ _ p) K hKG
    (commutator_eq_bot_iff_le_centralizer.mp hKF)⟩

include h e hz hk in
private theorem plane_select_generating_edge
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    ∃ s, Adjacent Rg a s ∧
      Q Rg s ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a := by
  have base {z : Vertex Rg}
      (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
      ∃ s, Adjacent Rg (alpha Rg) s ∧
        Q Rg s ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg (alpha Rg) := by
    have hav : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
      apply (cosetGraph_adj Rg _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using
        p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
    obtain ⟨s,has,r,hr,hgen,hpair,hfix,hnorm,hinside,hcomm⟩ :=
      remaining_small_critical_normalized_plane_selectors h e hz hk u (Or.inl hR)
        p (hsmall _ _ p)
    rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl has] at hgen
    rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hav] at hinside
    refine ⟨s,has,le_antisymm ?_ ?_⟩
    · exact sup_le (fun _ hv => hv.2 _ (adjacent_symm Rg has))
        (fun _ hv => hv.2 _ (adjacent_symm Rg hav))
    · rw [←hgen]
      exact sup_le (sup_le le_sup_left ((le_sup_left.trans hinside).trans le_sup_right))
        ((le_sup_right.trans hinside).trans le_sup_right)
  obtain ⟨g,ha⟩ := exists_mVertex_of_color Rg p.start_color
  have hga : act Rg g (alpha Rg) = a := by
    simpa only [alpha,act_mVertex,one_mul] using ha.symm
  have hgia : act Rg g⁻¹ a = alpha Rg := by
    rw [←hga,←act_mul,mul_inv_cancel,act_one]
  have hp0 : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ a) (act Rg g⁻¹ z),
      p₀.walk.getVert 1 = act Rg g⁻¹ (p.walk.getVert 1) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hgia] at hp0
  obtain ⟨p₀,hp₀⟩ := hp0
  obtain ⟨s,has,hgen⟩ := base p₀
  have hgs : Adjacent Rg a (act Rg g s) := by
    rw [←hga]
    exact (adjacent_act_iff Rg g _ _).mpr has
  refine ⟨act Rg g s,hgs,?_⟩
  have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
  rw [Subgroup.map_sup,←Q_act,←Q_act,←stabilizer_act,hga,hp₀,
    ←act_mul,inv_mul_cancel,act_one] at he
  exact he

include h e hz hk in
/-- The joint selector supplies a genuine generating edge and transporter
for the raw preceding segment; no second criticality or strict-slice
assumption enters the selection. -/
theorem plane_selected_raw_comparison
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hmidgen : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a)) :
    ∃ s, Adjacent Rg a s ∧
      Q Rg s ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a ∧
      ∃ g ∈ stabilizer Rg a, act Rg g (p.walk.getVert 1) = s ∧
        Adjacent Rg (act Rg g (p.walk.getVert 2)) s ∧
        ∀ K : Subgroup (FreeAmalgam Rg),
          K ≤ Z Rg (act Rg g (p.walk.getVert 2)) ⊓ Q Rg (p.walk.getVert 2) →
          ⁅K,Z Rg z ⊓ Q Rg a⁆ = ⊥ ∧ ⁅K,Z Rg z⁆ ≤ ⁅Z Rg a,Z Rg z⁆ := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hav : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcv : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨s,has,hgen⟩ := plane_select_generating_edge h e hz hk u hR hsmall p
  obtain ⟨g,hg,hgs⟩ := stabilizer_transitive_neighbors Rg a hav has
  have hds : Adjacent Rg (act Rg g (p.walk.getVert 2)) s := by
    rw [←hgs]
    exact (adjacent_act_iff Rg g _ _).mpr hcv
  refine ⟨s,has,hgen,g,hg,hgs,hds,?_⟩
  intro K hK
  exact plane_raw_shifted_kernels_of_midpoint_generation h e hz hk u hR hb4 hsmall
    p hds has K hK hgen g hg rfl hmidgen hback


include h e hz hk in
/-- On the outer selector's same retained backward path, construct the next
raw preceding segment with its generating edges, actual transporter and
full-kernel comparison. Criticality of this raw candidate is not assumed. -/
theorem plane_selected_successive_raw_comparison
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf (L ⊔ R),
      let x := (embedM Rg r)⁻¹
      ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let d := act Rg g (p.walk.getVert 2)
          let comparison := fun w (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w) =>
            ∃ q : CriticalPath Rg (sourceGeometry h) d (v.walk.getVert 2),
              q.walk.getVert 1 = t ∧
              (∀ i ≤ 2, q.walk.getVert (i+2) = v.walk.getVert i) ∧
              ∃ s, Adjacent Rg d s ∧
                Q Rg s ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d ∧
                ∃ k ∈ stabilizer Rg d, act Rg k (q.walk.getVert 1) = s ∧
                  Adjacent Rg (act Rg k (q.walk.getVert 2)) s ∧
                  ∀ K : Subgroup (FreeAmalgam Rg),
                    K ≤ Z Rg (act Rg k (q.walk.getVert 2)) ⊓ Q Rg (q.walk.getVert 2) →
                    ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg d⁆ = ⊥ ∧
                      ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤ ⁅Z Rg d,Z Rg (v.walk.getVert 2)⁆
          comparison z p ∨ comparison (act Rg x z) p' := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have ha1 : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hc1 : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,r,hr,p',hverts,hps,hgen,hpair,hnorm,hinside,g,hg,hgt,hstrict,halt⟩ :=
    plane_small_critical_backward_shift h e hz hk u hR p (hsmall _ _ p) hc1 hs
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hat' : Adjacent Rg (alpha Rg) (act Rg x t) := by
    rw [←show act Rg x (alpha Rg) = alpha Rg from hx]
    exact (adjacent_act_iff Rg x _ _).mpr hat
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat] at hgen hpair
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat'] at hpair
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl ha1] at hnorm hinside
  have hfirst : Q Rg t ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg (alpha Rg) := by
    apply le_antisymm
    · exact sup_le (fun _ hv => hv.2 _ (adjacent_symm Rg hat))
        (fun _ hv => hv.2 _ (adjacent_symm Rg ha1))
    · rw [←hgen]
      exact sup_le (sup_le le_sup_left ((le_sup_left.trans hinside).trans le_sup_right))
        ((le_sup_right.trans hinside).trans le_sup_right)
  have hQfirst : Q Rg (p'.walk.getVert 1) = Q Rg (p.walk.getVert 1) := by
    rw [hverts 1,Q_act]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg))).inv_mem hnorm)
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  refine ⟨t,hat,r,hr,p',hverts,hgen,hpair,g,hg,hgt,?_⟩
  have hl' : p'.walk.length = 4 := p'.length_eq_b.trans hb4
  have cast_end {d v w : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) d v)
      (he : v = w) : ∃ q' : CriticalPath Rg (sourceGeometry h) d w,
        ∀ i, q'.walk.getVert i = q.walk.getVert i := by
    subst w
    exact ⟨q,fun _ => rfl⟩
  have finish {w : Vertex Rg}
      (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (q : CriticalPath Rg (sourceGeometry h) (act Rg g (p.walk.getVert 2)) (v.walk.getVert 2))
      (hq1 : q.walk.getVert 1 = t)
      (hqv : ∀ i ≤ 2, q.walk.getVert (i+2) = v.walk.getVert i)
      (hgenq : Q Rg t ⊔ Q Rg (v.walk.getVert 1) = stabilizer Rg (alpha Rg))
      :
      ∃ s, Adjacent Rg (act Rg g (p.walk.getVert 2)) s ∧
        Q Rg s ⊔ Q Rg (q.walk.getVert 1) =
          stabilizer Rg (act Rg g (p.walk.getVert 2)) ∧
        ∃ k ∈ stabilizer Rg (act Rg g (p.walk.getVert 2)),
          act Rg k (q.walk.getVert 1) = s ∧
          Adjacent Rg (act Rg k (q.walk.getVert 2)) s ∧
          ∀ K : Subgroup (FreeAmalgam Rg),
            K ≤ Z Rg (act Rg k (q.walk.getVert 2)) ⊓ Q Rg (q.walk.getVert 2) →
            ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg (act Rg g (p.walk.getVert 2))⁆ = ⊥ ∧
              ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤
                ⁅Z Rg (act Rg g (p.walk.getVert 2)),Z Rg (v.walk.getVert 2)⁆ := by
    have hqa : q.walk.getVert 2 = alpha Rg := by
      simpa only [SimpleGraph.Walk.getVert_zero] using hqv 0 (by omega)
    apply plane_selected_raw_comparison h e hz hk u hR hb4 hsmall q
    · rw [hqa,hq1,hqv 1 (by omega)]
      exact hgenq
    · simpa only [hqa] using hstrict
  rcases halt with ⟨q,hq1,hqv⟩ | ⟨q,hq1,hqv⟩
  · obtain ⟨q',hq'⟩ := cast_end q (show p.walk.getVert (p.walk.length-2) =
        p.walk.getVert 2 by rw [hl])
    have hqv' : ∀ i ≤ 2, q'.walk.getVert (i+2) = p.walk.getVert i :=
      fun i hi => (hq' (i+2)).trans (hqv i (by omega))
    have hq1' := (hq' 1).trans hq1
    exact Or.inl ⟨q',hq1',hqv',finish p q' hq1' hqv' hfirst⟩
  · obtain ⟨q',hq'⟩ := cast_end q (show p'.walk.getVert (p'.walk.length-2) =
        p'.walk.getVert 2 by rw [hl'])
    have hqv' : ∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i :=
      fun i hi => (hq' (i+2)).trans (hqv i (by omega))
    have hq1' := (hq' 1).trans hq1
    exact Or.inr ⟨q',hq1',hqv',finish p' q' hq1' hqv' (by rwa [hQfirst])⟩

omit hk in
include h e hz in
/-- The original whole-core reduction supplies the outer critical path
and the next raw comparison, on both full moving covers. -/
theorem coreExhaustion_or_cubic_selected_raw_comparison :
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
          ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) →
        ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf (L ⊔ R),
          let x := (embedM Rg r)⁻¹
          ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
            (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
            (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
            Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
            ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
              let d := act Rg g (p.walk.getVert 2)
              let comparison := fun w (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w) =>
                ∃ q : CriticalPath Rg (sourceGeometry h) d (v.walk.getVert 2),
                  q.walk.getVert 1 = t ∧
                  (∀ i ≤ 2, q.walk.getVert (i+2) = v.walk.getVert i) ∧
                  ∃ s, Adjacent Rg d s ∧
                    Q Rg s ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d ∧
                    ∃ k ∈ stabilizer Rg d, act Rg k (q.walk.getVert 1) = s ∧
                      Adjacent Rg (act Rg k (q.walk.getVert 2)) s ∧
                      ∀ K : Subgroup (FreeAmalgam Rg),
                        K ≤ Z Rg (act Rg k (q.walk.getVert 2)) ⊓ Q Rg (q.walk.getVert 2) →
                        ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg d⁆ = ⊥ ∧
                          ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤ ⁅Z Rg d,Z Rg (v.walk.getVert 2)⁆
              comparison z p ∨ comparison (act Rg x z) p')) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,?_⟩⟩
    intro hb4 hsmall z p hstrict
    exact plane_selected_successive_raw_comparison h e hz hk u hplane hb4 hsmall p hstrict

omit hk in
include h e hz in
/-- Literal C.1.32 application of the successive comparison, with the
original projection, radical, full attachments and both covers retained. -/
theorem rankTwo_or_cubic_selected_raw_comparison :
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
          ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) →
        ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf (L ⊔ R),
          let x := (embedM Rg r)⁻¹
          ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
            (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
            (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
            Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
            ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
              let d := act Rg g (p.walk.getVert 2)
              let comparison := fun w (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w) =>
                ∃ q : CriticalPath Rg (sourceGeometry h) d (v.walk.getVert 2),
                  q.walk.getVert 1 = t ∧
                  (∀ i ≤ 2, q.walk.getVert (i+2) = v.walk.getVert i) ∧
                  ∃ s, Adjacent Rg d s ∧
                    Q Rg s ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d ∧
                    ∃ k ∈ stabilizer Rg d, act Rg k (q.walk.getVert 1) = s ∧
                      Adjacent Rg (act Rg k (q.walk.getVert 2)) s ∧
                      ∀ K : Subgroup (FreeAmalgam Rg),
                        K ≤ Z Rg (act Rg k (q.walk.getVert 2)) ⊓ Q Rg (q.walk.getVert 2) →
                        ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg d⁆ = ⊥ ∧
                          ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤ ⁅Z Rg d,Z Rg (v.walk.getVert 2)⁆
              comparison z p ∨ comparison (act Rg x z) p')) :=
  (coreExhaustion_or_cubic_selected_raw_comparison h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
