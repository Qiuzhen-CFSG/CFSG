module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourMoverFixed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelSelectors

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer

/-!
# Residual selectors on the original Borel graph

Every element of a component stabilizer is a product of an incident edge
kernel element and an element of its actual two-residual. The first factor
fixes the whole incident star. Discarding it preserves the images of both
vertices of a two-edge segment, and also preserves the transported image
of every subgroup normalized by that edge kernel.

Apply this simultaneously to the small-critical-image selectors. Both
selected transporters lie in the actual residual; the full fixed-subgroup
comparisons, two edge-generation identities, and paired opposite-mover
generation retain the same choices. The construction works at every
component vertex. With distinct movers and central generation, the
core-containment alternative is impossible, giving both residual-generation
clauses of MS93 (5.5)(c) on these selected edges.

For compatible distance-four paths, the star replacement removes the
residual-membership hypothesis from the existing two-cover normalization
theorem. Its same-path fixed-subgroup comparison is still required.
The selection theorems do not assert that their transported neighboring
seeds form critical backward paths. That compatibility, the equal-mover
and remaining critical-image cases, and the terminal contradiction remain
before CoreExhaustion and whole exceptional block reconstruction.

OriginalSylowExceptional applies these results to the original c.L,d.S.
Both full moving covers, their central attachments, and the original cubic
kernel E with its odd quotient E/Q are retained.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)--(5.6) and (5.12)(1), printed pp.915--918,924--925;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf M
local notation "π" => CubicAction.projection h e hz hk

include h in
/-- A stabilizer transporter can be replaced by an element of its actual
residual on the entire incident star. The discarded edge-kernel factor
fixes every vertex of that star. -/
theorem residual_star_transporter
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg a) :
    ∃ y ∈ Ltilde Rg a, ∃ k ∈ Q Rg t, k * y = x ∧
      act Rg y t = act Rg x t ∧
      ∀ v, Adjacent Rg v t → act Rg y v = act Rg x v := by
  let P := stabilizer Rg a
  let N := pResidual 2 P
  let T := (Q Rg t).subgroupOf P
  have hTP : Q Rg t ≤ P := fun _ hv => hv.2 _ (adjacent_symm Rg hat)
  have hN : (Ltilde Rg a).subgroupOf P = N := subgroupOf_map_subtype_eq _
  have hsup : T ⊔ N = ⊤ := by
    rw [←hN,←subgroupOf_sup hTP (Ltilde_le_stabilizer a),sup_comm (Q Rg t),
      residual_edge_generation h ha hat,subgroupOf_self]
  obtain ⟨k,hk,y,hy,he⟩ := mem_sup_of_normal_right.mp
    (show (⟨x,hx⟩ : P) ∈ T ⊔ N from hsup ▸ mem_top _)
  have hkQ : (k : FreeAmalgam Rg) ∈ Q Rg t := hk
  have he' : (k : FreeAmalgam Rg) * (y : FreeAmalgam Rg) = x := congrArg Subtype.val he
  refine ⟨y,mem_map_of_mem P.subtype hy,k,hkQ,he',?_,?_⟩
  · rw [←he',act_mul,show act Rg (k : FreeAmalgam Rg) t = t from hkQ.1]
  · intro v hvt
    rw [←he',act_mul,show act Rg (k : FreeAmalgam Rg) v = v from
      hkQ.2 v (adjacent_symm Rg hvt)]

include h in
/-- This replacement also preserves the conjugates of every subgroup
normalized by the incident edge kernel, simultaneously. In particular it
preserves the opposite index-two mover used in MS93 (5.6). -/
theorem residual_star_transporter_subgroups
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg a) :
    ∃ y ∈ Ltilde Rg a,
      act Rg y t = act Rg x t ∧
      (∀ v, Adjacent Rg v t → act Rg y v = act Rg x v) ∧
      ∀ A : Subgroup (FreeAmalgam Rg), Q Rg t ≤ normalizer (A : Set (FreeAmalgam Rg)) →
        A.map (MulAut.conj y⁻¹).toMonoidHom = A.map (MulAut.conj x⁻¹).toMonoidHom := by
  obtain ⟨y,hy,k,hk,rfl,hyt,hyv⟩ := residual_star_transporter h ha hat x hx
  refine ⟨y,hy,hyt,hyv,?_⟩
  intro A hA
  have hAn : A.map (MulAut.conj k⁻¹).toMonoidHom = A :=
    mem_normalizer_iff_map_conj_eq.mp (hA ((Q Rg t).inv_mem hk))
  have hcomp : (A.map (MulAut.conj k⁻¹).toMonoidHom).map
      (MulAut.conj y⁻¹).toMonoidHom = A.map (MulAut.conj (k*y)⁻¹).toMonoidHom := by
    rw [map_map]
    congr 1
    apply MonoidHom.ext
    intro v
    change y⁻¹*(k⁻¹*v*k⁻¹⁻¹)*y⁻¹⁻¹ = (k*y)⁻¹*v*((k*y)⁻¹)⁻¹
    group
  rwa [hAn] at hcomp

include h e hz hk in
/-- The small-image source selectors can be chosen in the actual local
residual. Both fixed-subgroup comparisons, both edge-generation equations,
and the paired opposite-mover generation use these same choices. -/
theorem borel_small_residual_selectors_base
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      ∃ x ∈ Ltilde Rg (alpha Rg), ∃ y ∈ Ltilde Rg (alpha Rg),
      let b := p.walk.getVert 1
      let J := edgeOffenderJoin (alpha Rg) t
      let J' := edgeOffenderJoin (alpha Rg) (act Rg x t)
      act Rg y b = t ∧
      (J ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
      J ⊔ J' = stabilizer Rg (alpha Rg) ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      Z Rg b ⊓ centralizer (J : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      Z Rg b ⊓ centralizer (J' : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      x ∈ normalizer (edgeOffenderJoin (alpha Rg) b : Set (FreeAmalgam Rg)) ∧
      (∀ J₀ : Subgroup (FreeAmalgam Rg), Q Rg (alpha Rg) ≤ J₀ →
        J₀ ≤ Q Rg b → J₀.relIndex (Q Rg b) = 2 →
        let J₁ := J₀.map (MulAut.conj y⁻¹).toMonoidHom
        (J₁ ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom) ⊔ Z Rg z =
          stabilizer Rg (alpha Rg)) := by
  obtain ⟨t,hat,r,hr,hgen,hpair,_,_,hgen₀,hgen₁,hfix₀,hfix₁,hnorm,_,_,g,hg,hgt,hop⟩ :=
    borel_small_critical_seed_selectors_with_opposite h e hz hk u hR p hp
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ Ltilde Rg (alpha Rg) := by
    rw [graph_component h]
    exact ⟨r⁻¹,(K).inv_mem hr,by simp only [map_inv,x]⟩
  have hab : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  obtain ⟨y,hy,hyt,_,hmap⟩ := residual_star_transporter_subgroups h rfl hab g hg
  refine ⟨t,hat,x,hx,y,hy,hyt.trans hgt,hgen,hpair,hgen₀,hgen₁,hfix₀,hfix₁,hnorm,?_⟩
  intro J₀ hQJ hJT hi
  let : (J₀.subgroupOf (Q Rg (p.walk.getVert 1))).Normal := normal_of_index_eq_two hi
  have hJN : Q Rg (p.walk.getVert 1) ≤ normalizer (J₀ : Set (FreeAmalgam Rg)) :=
    (normal_subgroupOf_iff_le_normalizer hJT).mp inferInstance
  dsimp only
  rw [hmap J₀ hJN]
  exact hop J₀ hQJ hJT hi

include h e hz hk in
/-- The two-cover normalization theorem only needs a transporter in the
stabilizer: its residual representative preserves the entire backward
segment. The same-path fixed-subgroup comparison remains explicit. -/
theorem borel_four_compatible_kernel_normalized_of_stabilizer
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hgen' : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg a)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg a)
    (hxd : act Rg x (p.walk.getVert 2) = d)
    (hxt : act Rg x (p.walk.getVert 1) = q.walk.getVert 1)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4)
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1))
    (hfixed : Z Rg (p.walk.getVert 3) ⊓ centralizer
        (edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) :
    X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _) := by
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hab : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcb : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨w,hw,_,_,_,hwt,hwc⟩ := residual_star_transporter h p.start_color hab x hx
  exact borel_four_compatible_kernel_normalized h e hz hk u hR
    p q hqa r hrz hgen hgen' w hw ((hwc _ hcb).trans hxd) (hwt.trans hxt) hp hq hne hfixed
include h e hz hk in
/-- The same residual selectors at every component vertex of the original
graph, retaining the full edge seed and the opposite index-two actors. -/
theorem borel_small_residual_selectors
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ t, Adjacent Rg a t ∧
      ∃ x ∈ Ltilde Rg a, ∃ y ∈ Ltilde Rg a,
      let b := p.walk.getVert 1
      let J := edgeOffenderJoin a t
      let J' := edgeOffenderJoin a (act Rg x t)
      act Rg y b = t ∧
      (J ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg a ∧
      J ⊔ J' = stabilizer Rg a ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg a ∧
      Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg a ∧
      Z Rg b ⊓ centralizer (J : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) ∧
      Z Rg b ⊓ centralizer (J' : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) ∧
      x ∈ normalizer (edgeOffenderJoin a b : Set (FreeAmalgam Rg)) ∧
      (∀ J₀ : Subgroup (FreeAmalgam Rg), Q Rg a ≤ J₀ →
        J₀ ≤ Q Rg b → J₀.relIndex (Q Rg b) = 2 →
        let J₁ := J₀.map (MulAut.conj y⁻¹).toMonoidHom
        (J₁ ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom) ⊔ Z Rg z =
          stabilizer Rg a) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hs : (Q Rg (act Rg g⁻¹ z)).relIndex (Z Rg (act Rg g⁻¹ a)) < 4 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹⁻¹).injective]
    exact hp
  have base := borel_small_residual_selectors_base h e hz hk u hR (z := act Rg g⁻¹ z)
  rw [←hbase] at base
  obtain ⟨t,hat,x,hx,y,hy,hyt,hgen,hpair,hgen₀,hgen₁,hfix₀,hfix₁,hnorm,hop⟩ := base (p.act g⁻¹) hs
  let x' := g⁻¹*x*g
  let y' := g⁻¹*y*g
  let f := (MulAut.conj g⁻¹).toMonoidHom
  have hcancel (v : Vertex Rg) : act Rg g (act Rg g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hxc (v : Vertex Rg) : act Rg x' (act Rg g v) = act Rg g (act Rg x v) := by
    rw [←act_mul,←act_mul]
    congr 1
    dsimp only [x']
    group
  have hyc (v : Vertex Rg) : act Rg y' (act Rg g v) = act Rg g (act Rg y v) := by
    rw [←act_mul,←act_mul]
    congr 1
    dsimp only [y']
    group
  have hL : (Ltilde Rg (act Rg g⁻¹ a)).map f = Ltilde Rg a := by
    rw [←Ltilde_act,hcancel]
  have hx' : x' ∈ Ltilde Rg a := by
    have hh := mem_map_of_mem f hx
    rw [hL] at hh
    simpa only [f,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,x'] using hh
  have hy' : y' ∈ Ltilde Rg a := by
    have hh := mem_map_of_mem f hy
    rw [hL] at hh
    simpa only [f,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,y'] using hh
  have hxa : act Rg x (act Rg g⁻¹ a) = act Rg g⁻¹ a := Ltilde_le_stabilizer _ hx
  have haxt : Adjacent Rg (act Rg g⁻¹ a) (act Rg x t) := by
    rw [←hxa]
    exact (adjacent_act_iff Rg x _ _).mpr hat
  have hc : color Rg (act Rg g⁻¹ a) = false := by rw [action_preserves_color,p.start_color]
  have chart (v : Vertex Rg) (hv : Adjacent Rg (act Rg g⁻¹ a) v) :
      (edgeOffenderJoin (act Rg g⁻¹ a) v).map f = edgeOffenderJoin a (act Rg g v) := by
    simpa only [hcancel] using (remaining_edge_join_act h e hz hk u (Or.inr hR) hc hv g).symm
  have hG : (stabilizer Rg (act Rg g⁻¹ a)).map f = stabilizer Rg a := by
    rw [←stabilizer_act,hcancel]
  have hyt' : act Rg y' (p.walk.getVert 1) = act Rg g t := by
    rw [←hcancel (p.walk.getVert 1),hyc]
    simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act Rg g) hyt
  have hgen' := congrArg (Subgroup.map f) hgen
  rw [Subgroup.map_sup,Subgroup.map_sup,chart t hat,←Z_act,hcancel,←Z_act,←hxc,hcancel,hG] at hgen'
  have hpair' := congrArg (Subgroup.map f) hpair
  rw [Subgroup.map_sup,chart t hat,chart _ haxt,←hxc,hG] at hpair'
  have hgen₀' := congrArg (Subgroup.map f) hgen₀
  rw [Subgroup.map_sup,←Q_act,←Z_act,hcancel,hG] at hgen₀'
  have hgen₁' := congrArg (Subgroup.map f) hgen₁
  rw [Subgroup.map_sup,←Q_act,←hxc,←Z_act,hcancel,hG] at hgen₁'
  have fix_transfer (v : Vertex Rg) (hv : Adjacent Rg (act Rg g⁻¹ a) v)
      (hh : Z Rg ((p.act g⁻¹).walk.getVert 1) ⊓
        centralizer (edgeOffenderJoin (act Rg g⁻¹ a) v : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg (act Rg g⁻¹ a) : Set (FreeAmalgam Rg))) :
      Z Rg (p.walk.getVert 1) ⊓ centralizer (edgeOffenderJoin a (act Rg g v) : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    have hh' := (map_mono (f := f) hh).trans (map_centralizer_le_centralizer_image _ f)
    change (Z Rg ((p.act g⁻¹).walk.getVert 1) ⊓
      centralizer (edgeOffenderJoin (act Rg g⁻¹ a) v : Set (FreeAmalgam Rg))).map f ≤
      centralizer ((stabilizer Rg (act Rg g⁻¹ a)).map f : Set (FreeAmalgam Rg)) at hh'
    rw [←map_inf_centralizer_of_injective f (MulAut.conj g⁻¹).injective,chart v hv,hG] at hh'
    have hZ : (Z Rg ((p.act g⁻¹).walk.getVert 1)).map f = Z Rg (p.walk.getVert 1) := by
      simp only [CriticalPath.act,actWalk_getVert]
      change (Z Rg (act Rg g⁻¹ (p.walk.getVert 1))).map
        (MulAut.conj g⁻¹).toMonoidHom = Z Rg (p.walk.getVert 1)
      rw [←Z_act,hcancel]
    rwa [hZ] at hh'
  have hab : Adjacent Rg (act Rg g⁻¹ a) ((p.act g⁻¹).walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (p.act g⁻¹).walk.adj_getVert_succ (i := 0)
        ((p.act g⁻¹).length_eq_b ▸ sourceDistance_pos h)
  refine ⟨act Rg g t,by simpa only [hcancel] using (adjacent_act_iff Rg g _ _).mpr hat,
    x',hx',y',hy',hyt',hgen',hpair',hgen₀',hgen₁',fix_transfer t hat hfix₀,?_,?_,?_⟩
  · simpa only [←hxc] using fix_transfer (act Rg x t) haxt hfix₁
  · have hh := (edgeOffenderJoin (act Rg g⁻¹ a) ((p.act g⁻¹).walk.getVert 1)).le_normalizer_map
      f (mem_map_of_mem f hnorm)
    rw [chart _ hab] at hh
    simpa only [CriticalPath.act,actWalk_getVert,hcancel,f,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,x'] using hh
  · intro J₀ hQJ hJT hi
    let Jb := J₀.map (MulAut.conj g).toMonoidHom
    have hJmap : Jb.map f = J₀ := by
      rw [map_map]
      have he : f.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ := by
        apply MonoidHom.ext
        intro v
        change g⁻¹*(g*v*g⁻¹)*g⁻¹⁻¹=v
        group
      rw [he,map_id]
    have hQJb : Q Rg (act Rg g⁻¹ a) ≤ Jb := by
      simpa only [Q_act,inv_inv,Jb] using map_mono (f := (MulAut.conj g).toMonoidHom) hQJ
    have hJbT : Jb ≤ Q Rg ((p.act g⁻¹).walk.getVert 1) := by
      simpa only [CriticalPath.act,actWalk_getVert,Q_act,inv_inv,Jb] using
        map_mono (f := (MulAut.conj g).toMonoidHom) hJT
    have hib : Jb.relIndex (Q Rg ((p.act g⁻¹).walk.getVert 1)) = 2 := by
      simp only [CriticalPath.act,actWalk_getVert,Q_act,inv_inv,Jb]
      exact (relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        _ _ (MulAut.conj g).injective).trans hi
    have conjugate (A : Subgroup (FreeAmalgam Rg)) (w : FreeAmalgam Rg) :
        (A.map (MulAut.conj w⁻¹).toMonoidHom).map f =
          (A.map f).map (MulAut.conj (g⁻¹*w*g)⁻¹).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro v
      change g⁻¹*(w⁻¹*v*w⁻¹⁻¹)*g⁻¹⁻¹ =
        (g⁻¹*w*g)⁻¹*(g⁻¹*v*g⁻¹⁻¹)*((g⁻¹*w*g)⁻¹)⁻¹
      group
    have hh := congrArg (Subgroup.map f) (hop Jb hQJb hJbT hib)
    rw [Subgroup.map_sup,Subgroup.map_sup,conjugate,conjugate,conjugate,hJmap,←Z_act,hcancel,hG] at hh
    exact hh
include h e hz hk in
/-- Under central generation, distinct movers give the first alternative
of MS93 (5.5)(c) for the same residual selectors as (a) and (b).
The full fixed subgroups in (b) are retained. -/
theorem borel_small_central_distinct_residual_selectors
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z c : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hc : color Rg c = false) (hcb : Adjacent Rg c (p.walk.getVert 1))
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠ edgeOffenderJoin c (p.walk.getVert 1))
    (hsplit : X Rg a = U Rg a ⊔
      (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) :
    ∃ t, Adjacent Rg a t ∧ ∃ x ∈ Ltilde Rg a, ∃ y ∈ Ltilde Rg a,
      act Rg y (p.walk.getVert 1) = t ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg a ∧
      Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg a ∧
      Z Rg (p.walk.getVert 1) ⊓ centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) ∧
      Z Rg (p.walk.getVert 1) ⊓ centralizer (edgeOffenderJoin a (act Rg x t) : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) ∧
      Ltilde Rg a ≤ edgeOffenderJoin (act Rg y c) t ⊔ Z Rg z ∧
      Ltilde Rg a ≤ edgeOffenderJoin (act Rg x (act Rg y c)) (act Rg x t) ⊔ Z Rg z := by
  have hab : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  have hcore : ¬ Q Rg a ≤ edgeOffenderJoin c (p.walk.getVert 1) := fun hh =>
    borel_opposite_containing_core_nonsplit h e hz hk u hR p.start_color hc hab hcb hne hh hsplit
  obtain ⟨t,hat,x,hx,y,hy,hyt,_,_,hgen₀,hgen₁,hfix₀,hfix₁,_,_⟩ :=
    borel_small_residual_selectors h e hz hk u hR p hp
  have hxG := Ltilde_le_stabilizer a hx
  have hyG := Ltilde_le_stabilizer a hy
  have hcy : color Rg (act Rg y c) = false := by rw [action_preserves_color,hc]
  have hcyt : Adjacent Rg (act Rg y c) t := by
    rw [←hyt]
    exact (adjacent_act_iff Rg y _ _).mpr hcb
  have transport_not_le {v t : Vertex Rg} (hv : color Rg v = false) (hvt : Adjacent Rg v t)
      (hn : ¬ Q Rg a ≤ edgeOffenderJoin v t) (g : FreeAmalgam Rg)
      (hg : g ∈ stabilizer Rg a) :
      ¬ Q Rg a ≤ edgeOffenderJoin (act Rg g v) (act Rg g t) := by
    intro hh
    have hQa : (Q Rg a).map (MulAut.conj g⁻¹).toMonoidHom = Q Rg a := by
      rw [←Q_act,show act Rg g a = a from hg]
    rw [remaining_edge_join_act h e hz hk u (Or.inr hR) hv hvt g,←hQa] at hh
    exact hn ((map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh)
  have hcorey : ¬ Q Rg a ≤ edgeOffenderJoin (act Rg y c) t := by
    rw [←hyt]
    exact transport_not_le hc hcb hcore y hyG
  have haxt : Adjacent Rg a (act Rg x t) := by
    rw [←show act Rg x a = a from hxG]
    exact (adjacent_act_iff Rg x _ _).mpr hat
  have hcxy : color Rg (act Rg x (act Rg y c)) = false := by rw [action_preserves_color,hcy]
  have hcorexy := transport_not_le hcy hcyt hcorey x hxG
  exact ⟨t,hat,x,hx,y,hy,hyt,hgen₀,hgen₁,hfix₀,hfix₁,
    (borel_opposite_generation_of_core_not_le h e hz hk u hR p.start_color hcy
      hat hcyt _ hgen₀ hcorey).2,
    (borel_opposite_generation_of_core_not_le h e hz hk u hR p.start_color hcxy
      haxt ((adjacent_act_iff Rg x _ _).mpr hcyt) _ hgen₁ hcorexy).2⟩

include h e hz hk in
/-- In the actual distance-four normalization-failure branch, central
generation is automatic. Thus the distinct-mover case has synchronized
residual choices satisfying all three clauses of (5.5) needed here.
Criticality of their new backward endpoints remains a separate step. -/
theorem borel_four_failure_distinct_residual_selectors
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _))
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1)) :
    ∃ t, Adjacent Rg a t ∧ ∃ x ∈ Ltilde Rg a, ∃ y ∈ Ltilde Rg a,
      act Rg y (p.walk.getVert 1) = t ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg a ∧
      Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg a ∧
      Z Rg (p.walk.getVert 1) ⊓ centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) ∧
      Z Rg (p.walk.getVert 1) ⊓ centralizer (edgeOffenderJoin a (act Rg x t) : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) ∧
      Ltilde Rg a ≤ edgeOffenderJoin (act Rg y (p.walk.getVert 2)) t ⊔ Z Rg z ∧
      Ltilde Rg a ≤ edgeOffenderJoin (act Rg x (act Rg y (p.walk.getVert 2))) (act Rg x t) ⊔ Z Rg z := by
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcb : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  exact borel_small_central_distinct_residual_selectors h e hz hk u hR
    p hp q.end_color hcb hne
    (((borel_four_kernel_omega_control h e hz hk u hR p q hqa hp).2 hnorm a p.start_color).1)

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
