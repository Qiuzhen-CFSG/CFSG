module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelOppositePair
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelOppositePair
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSelectors
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullSeed

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration

/-!
# Equal-mover small critical shifts in the Borel branch

The Borel Thompson mover is a proper subgroup of the edge. Its fixed part
on the full omega layer of a small critical pair lies in the source seed:
the six-letter displacement coordinates fixed by its three transpositions
have even augmentation. When the movers on two incident edges agree,
quadraticity therefore controls the full neighboring-seed/core commutator
and every reverse omega kernel.

For two compatible critical paths trapped at a strict Baumann slice, the
omega-control dichotomy either gives central generation of the full layer,
or makes the two-seed span normal in the local stabilizer. The latter puts
the neighboring moving cover inside the strict slice, a contradiction.
Consequently the paired selectors give a backward critical path unless the
full omega layer is centrally generated. The equal-mover and strict-slice
hypotheses remain explicit. Distinct movers and the source terminal
arguments are still needed for whole-core exhaustion; X = Z alone is not
that equality. Both full moving-cover orders, 16 and 32, are retained.

The `import all` dependencies intentionally share private coordinates and
transport lemmas within this package's exceptional reconstruction proof.
Their implementation names do not enter the public statements.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.7), printed p.919; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull

private theorem plane_fixed_in_moved {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) S Y)
    (j : (coreRepresentation (Fin 6)).IntertwiningMap ρ)
    (hj : ∀ i k : Fin 6, i ≠ k → j (Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.pairVector i k) ≠ 0)
    (hcoords : ∀ z : Y, ∃ w : Full (Fin 6), ∀ g : S,
      ρ g z-z = j (Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.displacement g w))
    (u : S) (v : Y) (hv : v ∈ fixedSpace ρ (D.map (MulAut.conj u).toMonoidHom)) :
    v ∈ j.toLinearMap.range ⊔ ρ.invariants := by
  obtain ⟨w,hw⟩ := hcoords v
  have pair (i k : Fin 6) (hik : i ≠ k) (hs : Equiv.swap i k ∈ D) :
      w (u i) + w (u k) = 0 := by
    have hm : Equiv.swap (u i) (u k) ∈ D.map (MulAut.conj u).toMonoidHom := by
      rw [Equiv.swap_apply_apply]
      exact mem_map_of_mem _ hs
    have he : ρ (Equiv.swap (u i) (u k)) v = v := hv ⟨_,hm⟩
    have hh := hw (Equiv.swap (u i) (u k))
    rw [he,sub_self,Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.displacement_swap,map_smul] at hh
    exact (smul_eq_zero.mp hh.symm).resolve_right (hj _ _ (u.injective.ne hik))
  have h01 := pair 0 1 (by decide) swap01_mem_D
  have h23 := pair 2 3 (by decide) swap23_mem_D
  have h45 := pair 4 5 (by decide) swap45_mem_D
  have heven : augmentation (Fin 6) w = 0 := by
    change ∑ i, w i = 0
    rw [←Equiv.sum_comp u w]
    rw [Fin.sum_univ_six]
    calc
      _ = (w (u 0)+w (u 1))+(w (u 2)+w (u 3))+(w (u 4)+w (u 5)) := by abel
      _ = 0 := by rw [h01,h23,h45]; rfl
  let v₀ : core (Fin 6) := ⟨w,heven⟩
  have he (g : S) : Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates.displacement g w = coreRepresentation (Fin 6) g v₀-v₀ := by
    apply Subtype.ext
    rfl
  have hf : v-j v₀ ∈ ρ.invariants := by
    intro g
    have hh := hw g
    rw [he,map_sub,j.isIntertwining] at hh
    rw [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp hh
  have hm := Submodule.add_mem_sup (LinearMap.mem_range_self j.toLinearMap v₀) hf
  change j v₀ + (v-j v₀) ∈ j.toLinearMap.range ⊔ ρ.invariants at hm
  convert hm using 1; abel

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "X₀" => centralOmega L R
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem small_critical_plane_fixed_omega_base
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    X Rg (alpha Rg) ⊓ centralizer
      (edgeOffenderJoin (alpha Rg) (beta Rg) : Set (FreeAmalgam Rg)) ≤ Z Rg (alpha Rg) := by
  have hJ : edgeOffenderJoin (alpha Rg) (beta Rg) =
      (borelPlane h e hz hk u).map (embedM Rg) :=
    remaining_join_in_chart h e hz hk u (Or.inr hR) rfl (base_adjacent Rg) (embedM Rg)
      (embedM_injective Rg) (Q_beta Rg).symm
      (Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le).symm
      (graph_U_map h e hz)
  rintro v ⟨hv,hfix⟩
  rw [graph_X h] at hv
  obtain ⟨m,hm,rfl⟩ := hv
  have hmfix : m ∈ centralizer (borelPlane h e hz hk u : Set M) := by
    intro r hr
    apply embedM_injective Rg
    simpa only [map_mul] using hfix (embedM Rg r) (hJ.symm ▸ mem_map_of_mem _ hr)
  obtain ⟨j,hjr,hj,hcoords⟩ := omega_coordinates h e hz hk p hsmall
  have hvfix : Additive.ofMul (⟨m,hm⟩ : X₀) ∈
      fixedSpace (omegaAction h e hz hk) (D.map (MulAut.conj u).toMonoidHom) := by
    rw [←borelPlane_image h e hz hk u hR]
    exact (NormalElementaryQuotient.mem_fixedSpace_image X₀ π
      (CubicEven.projection_surjective h e hz hk)
      ((CubicAction.projection_kernel h e hz hk).trans hk.symm)
      (borelPlane h e hz hk u) _).mpr hmfix
  have hmem := plane_fixed_in_moved (omegaAction h e hz hk) j hj hcoords u _ hvfix
  rw [hjr] at hmem
  obtain ⟨v₀,⟨v₁,rfl⟩,w,hw,he⟩ := Submodule.mem_sup.mp hmem
  have hwc : (w.toMul : M) ∈ center M := by
    apply mem_center_iff.mpr
    intro r
    have hh := congrArg (fun y : Additive X₀ => (y.toMul : M)) (hw (π r))
    rw [omegaAction_conjugate] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hmprod : (v₁.toMul : M) * (w.toMul : M) = m :=
    congrArg (fun y : Additive X₀ => (y.toMul : M)) he
  have hwu : embedM Rg (v₁.toMul : M) ∈ Z Rg (alpha Rg) :=
    DistanceEight.U_le_Z Rg _ ((graph_U_map h e hz) ▸ mem_map_of_mem _ v₁.toMul.property)
  have hwz : embedM Rg (w.toMul : M) ∈ Z Rg (alpha Rg) := by
    apply omega_fixed_le_seed h (alpha Rg) rfl
    refine ⟨(graph_X h).symm ▸ mem_map_of_mem _ w.toMul.property,?_⟩
    intro r hr
    change r ∈ stabilizer Rg (mVertex Rg 1) at hr
    rw [stabilizer_m_base] at hr
    obtain ⟨r₀,rfl⟩ := hr
    simpa only [map_mul] using congrArg (embedM Rg) ((mem_center_iff.mp hwc) r₀)
  rw [←hmprod,map_mul]
  exact (Z Rg (alpha Rg)).mul_mem hwu hwz

include h e hz hk in
/-- At a small critical pair, the full omega layer fixed by its incident
Borel Thompson mover lies in the original seed. The full fixed subgroup and
both possible moving covers are retained. -/
theorem borel_small_critical_fixed_omega_le_seed
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4)
    (hat : Adjacent Rg a t) :
    X Rg a ⊓ centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg)) ≤ Z Rg a := by
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common Rg a t).mp hat
  · obtain ⟨rfl,rfl⟩ := hg
    have hga : act Rg g (alpha Rg) = mVertex Rg g := by
      simp only [alpha,act_mVertex,one_mul]
    have hgt : act Rg g (beta Rg) = hVertex Rg g := by
      simp only [beta,act_hVertex,one_mul]
    have hback : act Rg g⁻¹ (mVertex Rg g) = alpha Rg := by
      simp only [act_mVertex,mul_inv_cancel]; rfl
    have hp : Nonempty (CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg g⁻¹ z)) := by
      rw [←hback]
      exact ⟨p.act g⁻¹⟩
    obtain ⟨q⟩ := hp
    have hs : (Q Rg (act Rg g⁻¹ z)).relIndex (Z Rg (alpha Rg)) < 4 := by
      rw [←hback,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹⁻¹).injective]
      exact hsmall
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (small_critical_plane_fixed_omega_base h e hz hk u hR q hs)
    rw [←map_inf_centralizer_of_injective _ (MulAut.conj g⁻¹).injective,
      ←X_act,←Z_act,hga] at hh
    have he := remaining_edge_join_act h e hz hk u (Or.inr hR) rfl (base_adjacent Rg) g
    simp only [act_mVertex,act_hVertex,one_mul] at he
    change edgeOffenderJoin (mVertex Rg g) (hVertex Rg g) =
      (edgeOffenderJoin (alpha Rg) (beta Rg)).map (MulAut.conj g⁻¹).toMonoidHom at he
    rwa [←he] at hh
  · rw [hg.1] at p
    have hh := p.start_color
    cases hh

include h e hz hk in
/-- The central omega subgroup of the Borel Thompson mover belongs to the
source seed, with the actual relative centralizer retained. -/
theorem borel_small_critical_mover_center_le_seed
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4)
    (hat : Adjacent Rg a t) :
    omegaCenter (edgeOffenderJoin a t) ≤ Z Rg a := by
  have hj := remaining_edge_thompson h e hz hk u (Or.inr hR) p.start_color hat
  have hJG : edgeOffenderJoin a t ≤ stabilizer Rg a :=
    hj.2.2.1.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hat))
  have he := omegaCenter_eq_fixed_of_selfcentralizing (stabilizer Rg a) (Q Rg a)
    (edgeOffenderJoin a t) hj.2.1 hJG (vertex_core_selfcentralizing h e hz p.start_color hat)
  change omegaCenter (edgeOffenderJoin a t) =
    X Rg a ⊓ centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg)) at he
  rw [he]
  exact borel_small_critical_fixed_omega_le_seed h e hz hk u hR p hsmall hat

include h e hz hk in
/-- Equal Borel Thompson movers control the whole neighboring-seed/core
commutator. It lies in both full seeds and is fixed by the common mover;
the proper mover is not replaced by the full edge kernel. -/
theorem borel_equal_thompson_core_commutator
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z c t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4)
    (hc : color Rg c = false) (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (heq : edgeOffenderJoin a t = edgeOffenderJoin c t) :
    ⁅Z Rg c,Q Rg a⁆ ≤ Z Rg a ⊓ Z Rg c ∧
      ⁅⁅Z Rg c,Q Rg a⁆,edgeOffenderJoin a t⁆ = ⊥ := by
  have hJa := remaining_edge_thompson h e hz hk u (Or.inr hR) p.start_color hat
  have hJc := remaining_edge_thompson h e hz hk u (Or.inr hR) hc hct
  have hQJ : Q Rg a ≤ edgeOffenderJoin c t := heq ▸ hJa.2.1
  have hQGc : Q Rg a ≤ stabilizer Rg c :=
    (hQJ.trans hJc.2.2.1).trans (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hmove : ⁅Z Rg c,Q Rg a⁆ ≤ Z Rg c :=
    le_normalizer_iff_commutator_le_left.mp (hQGc.trans (Z_normalized Rg c))
  have hquad : ⁅⁅Z Rg c,Q Rg a⁆,edgeOffenderJoin c t⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono (commutator_mono le_rfl hQJ) le_rfl).trans_eq
      (remaining_edge_full_seed_quadratic h e hz hk u (Or.inr hR) hc hct))
  have hZX := (sourceGeometry h).omega_bound c hc (by
    rw [(sourceGeometry h).distance_constant c hc]
    exact sourceDistance_pos h)
  have hcenter : ⁅Z Rg c,Q Rg a⁆ ≤ omegaCenter (edgeOffenderJoin c t) := by
    intro v hv
    obtain ⟨hvQ,hv2,_⟩ := mem_omegaCenter_iff.mp (hZX (hmove hv))
    exact mem_omegaCenter_iff.mpr ⟨hJc.2.1 hvQ,hv2,
      commutator_eq_bot_iff_le_centralizer.mp hquad hv⟩
  have hseed : ⁅Z Rg c,Q Rg a⁆ ≤ Z Rg a := by
    rw [←heq] at hcenter
    exact hcenter.trans (borel_small_critical_mover_center_le_seed h e hz hk u hR p hsmall hat)
  exact ⟨le_inf hseed hmove,heq.symm ▸ hquad⟩

include h e hz hk in
/-- Equal-mover control applies to every full reverse omega kernel on the
same edge, without identifying that kernel with its seed or moving part. -/
theorem borel_equal_thompson_reverse_kernel_control
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z c t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4)
    (hc : color Rg c = false) (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (heq : edgeOffenderJoin a t = edgeOffenderJoin c t) (w : Vertex Rg) :
    ⁅X Rg w ⊓ Q Rg a,Z Rg c⁆ ≤ Z Rg a ⊓ Z Rg c ∧
      ⁅⁅X Rg w ⊓ Q Rg a,Z Rg c⁆,edgeOffenderJoin a t⁆ = ⊥ := by
  have hh := borel_equal_thompson_core_commutator h e hz hk u hR p hsmall hc hat hct heq
  have hle : ⁅X Rg w ⊓ Q Rg a,Z Rg c⁆ ≤ ⁅Z Rg c,Q Rg a⁆ := by
    rw [commutator_comm]
    exact commutator_mono le_rfl inf_le_right
  exact ⟨hle.trans hh.1,le_bot_iff.mp ((commutator_mono hle le_rfl).trans_eq hh.2)⟩

include h e hz hk in
/-- For equal Borel movers, trapping both compatible small critical paths
at a strict slice forces central generation of the entire omega layer.
The full-layer fixed-subgroup theorem supplies the missing seed control;
only the proper Thompson mover is used in the generation argument. -/
theorem borel_equal_thompson_trapped_omega_generation
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (heq : edgeOffenderJoin (alpha Rg) t = edgeOffenderJoin c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)) :
    ∀ a : Vertex Rg, color Rg a = false →
      (X Rg a = U Rg a ⊔
        (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) ∧
      X Rg a = Z Rg a := by
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
  have hZQ : Z Rg c ≤ Q Rg (alpha Rg) :=
    hZV.trans ((sourceGeometry h).V_le_Q hb _ rfl)
  have hcase {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hr : (Q Rg w).relIndex (Z Rg (alpha Rg)) < 4)
      (hrbad : Z Rg c ≤ Q Rg (r.walk.getVert (r.walk.length-2))) :
      (X Rg w = U Rg w ⊔
        (X Rg w ⊓ centralizer (stabilizer Rg w : Set (FreeAmalgam Rg)))) ∨
      ⁅Z Rg c,Z Rg w⁆ ≤ Z Rg (alpha Rg) := by
    have hrev := critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      (alpha Rg) rfl (sourceDistance_pos h) w r.end_color r.critical
    let rr : CriticalPath Rg (sourceGeometry h) w (alpha Rg) :=
      CriticalPath.ofPair r.end_color hrev
    have hrs : (Q Rg (alpha Rg)).relIndex (Z Rg w) < 4 := by
      rw [(small_critical_indices h e hz hk r hr).2]
      decide
    rcases small_critical_omega_generation_or_control_at h e hz hk rr hrs with hcentral | hcontrol
    · exact Or.inl hcentral
    right
    have hl : 2 < r.walk.length := r.length_eq_b ▸ hb
    let last := r.walk.getVert (r.walk.length-1)
    have hwlast : Adjacent Rg w last := by
      have hh := r.walk.adj_getVert_succ (i := r.walk.length-1) (by omega)
      rw [show r.walk.length-1+1=r.walk.length by omega,r.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have hlast : color Rg last = true := by
      have hh := adjacent_color_ne Rg hwlast
      rw [r.end_color] at hh
      cases he : color Rg last <;> simp_all
    have hprevlast : Adjacent Rg (r.walk.getVert (r.walk.length-2)) last := by
      have hh := r.walk.adj_getVert_succ (i := r.walk.length-2) (by omega)
      rw [show r.walk.length-2+1=r.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have hlocal : Z Rg c ≤ stabilizer Rg w :=
      (hrbad.trans (Q_le_adjacent_h Rg hlast hprevlast)).trans
        (fun _ hx => hx.2 _ (adjacent_symm Rg hwlast))
    have hline : ⁅X Rg w,Z Rg (alpha Rg)⁆ ≤ Z Rg (alpha Rg) :=
      le_normalizer_iff_commutator_le_right.mp
        ((critical_X_le_vertex h e w r.end_color (alpha Rg) hrev).trans (Z_normalized Rg _))
    have hfixed : Z Rg c ≤ centralizer
        ((⁅X Rg w,Z Rg (alpha Rg)⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
      (hZQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg (alpha Rg) rfl)))).trans (centralizer_le hline)
    have hkernel : ⁅Z Rg c,X Rg w ⊓ Q Rg (alpha Rg)⁆ ≤ Z Rg (alpha Rg) := by
      rw [commutator_comm]
      exact (borel_equal_thompson_reverse_kernel_control h e hz hk u hR p hp hc hat hct heq w).1.trans inf_le_left
    have hZX : Z Rg w ≤ X Rg w := (sourceGeometry h).omega_bound w r.end_color (by
      rw [(sourceGeometry h).distance_constant w r.end_color]
      exact sourceDistance_pos h)
    exact (commutator_mono le_rfl hZX).trans
      ((hcontrol (Z Rg c) hlocal hfixed).trans (sup_le hline hkernel))
  have finish (w : Vertex Rg) (hw : color Rg w = false)
      (hcentral : X Rg w = U Rg w ⊔
        (X Rg w ⊓ centralizer (stabilizer Rg w : Set (FreeAmalgam Rg)))) :
      ∀ a : Vertex Rg, color Rg a = false →
        (X Rg a = U Rg a ⊔
          (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) ∧
        X Rg a = Z Rg a := by
    intro a ha
    have hh := omega_generation_transport hw ha hcentral
    exact ⟨hh,omega_eq_seed_of_central_generation h a ha hh⟩
  rcases hcase p hp hbad with hcentral | hcomm
  · exact finish z p.end_color hcentral
  rcases hcase q hq hbad' with hcentral | hcomm'
  · exact finish z' q.end_color hcentral
  exfalso
  let Y := Z Rg c ⊔ Z Rg (alpha Rg)
  have hmove {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hm : ⁅Z Rg c,Z Rg w⁆ ≤ Z Rg (alpha Rg)) :
      ⁅Y,Z Rg w⁆ ≤ Z Rg (alpha Rg) := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      (Z Rg c) (Z Rg (alpha Rg)) (Z Rg w) (Z Rg (alpha Rg))
      (Z_normalized Rg _) (hZV.trans ((sourceGeometry h).V_local _ rfl hb))
      (Z_le_stabilizer Rg _) hm
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
        (sourceDistance_pos h) r.critical).trans (Z_normalized Rg _))
  have hpY := hmove p hcomm
  have hqY := hmove q hcomm'
  have hYN : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ (le_normalizer_iff_commutator_le_left.mpr
      (hpY.trans le_sup_right))) (le_normalizer_iff_commutator_le_left.mpr
        (hqY.trans le_sup_right))
    apply le_trans (remaining_edge_thompson h e hz hk u (Or.inr hR) rfl hat).2.2.1
    exact (le_inf ((show Q Rg t ≤ stabilizer Rg c from
      fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg c))
      ((show Q Rg t ≤ stabilizer Rg (alpha Rg) from
        fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hUB : U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    (DistanceEight.U_le_Z Rg c).trans (le_sup_left.trans
      (normalized_radius_le_slice_of_critical_commutator h e hz hb p Y
        (sup_le hZV (Z_le_VBall Rg _ 2)) hYN hpY))
  have hi := relIndex_eq_one.mpr hUB
  omega

include h e hz hk in
/-- The equal-mover Borel case constructs compatible backward critical paths
unless the full omega layer is centrally generated. Both candidates retain
the same component switch, neighbor transporter, and generation identities. -/
theorem borel_equal_thompson_small_shift_or_central_generation
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hd : Adjacent Rg delta (p.walk.getVert 1))
    (heq : edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) =
      edgeOffenderJoin delta (p.walk.getVert 1))
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
  have heqc : edgeOffenderJoin (alpha Rg) t = edgeOffenderJoin c t := by
    have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) heq
    rw [←remaining_edge_join_act h e hz hk u (Or.inr hR) rfl hfirst g,
      ←remaining_edge_join_act h e hz hk u (Or.inr hR) hdcol hd g,hgt,
      show act Rg g (alpha Rg) = alpha Rg from hg] at hh
    exact hh
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
    · exact Or.inl (borel_equal_thompson_trapped_omega_generation h e hz hk u hR
        p q hp hqs hat hct heqc hgen hbad hbad' hstrict)
    · exact Or.inr ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,g,hg,hgt,
        hstrict,Or.inr (extend _ q hbad')⟩
  · exact Or.inr ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,g,hg,hgt,
      hstrict,Or.inl (extend _ p hbad)⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
