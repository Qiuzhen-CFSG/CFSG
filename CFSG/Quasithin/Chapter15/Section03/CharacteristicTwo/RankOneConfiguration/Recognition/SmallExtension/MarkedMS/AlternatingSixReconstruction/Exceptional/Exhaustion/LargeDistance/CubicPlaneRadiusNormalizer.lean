module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusGrowth
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardRigidity

/-!
# Displacing the original plane radius kernels

Let two plane edges generate an endpoint stabilizer. A noncentral order-two
line in the first edge seed has at least four commutators with the second
edge. These commutators lie in the endpoint's moving subgroup. They cannot
be fixed by a four-image subactor of the first edge: its full fixed seed is
that edge's omega-center, and the two edge seeds intersect in the endpoint
center. The moving central attachment has order at most two, contradicting
the lower bound four. This proves a nonzero mixed commutator.

At distance four with uniformly small critical images, apply this comparison
to both the midpoint radius kernel and the whole last-edge radius kernel
on the previously selected escaping path. An actual element of the opposite
edge conjugates the retained line to a line not centralized by either kernel.
The same element fails to normalize both earlier two-cores, the starting
radius and both radius kernels. It fixes the endpoint and its opposite edge,
so transport produces a second critical path with that same endpoint and
with both starting vertex and midpoint changed. Its literal full radius-kernel
commutator is exactly the conjugated line. The two lines also have different
images modulo the actual endpoint center.

The whole-core and C.1.32 applications use the original cubic graph and
projection with kernel E; both moving covers and all central attachments
remain. This supplies displacement in the generating-stabilizer comparison,
not its terminal contradiction. The remaining image, distance and Borel cases
and both whole-core reconstruction outcomes still require completion.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the generating and common-fixer comparisons of (5.6), (5.12)(1),
printed pp.917--918,924--925; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.NormalElementaryQuotient
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
private theorem moving_central_attachment_card_le_two
    {a : Vertex Rg} (ha : color Rg a = false) :
    Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
      Subgroup (FreeAmalgam Rg)) ≤ 2 := by
  let C := centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))
  have hi := (C.subgroupOf (U Rg a)).index_mul_card
  change C.relIndex (U Rg a) * Nat.card (C.subgroupOf (U Rg a)) = Nat.card (U Rg a) at hi
  rw [moving_whole_fixed_index h e hz hk ha] at hi
  have hc : Nat.card (C.subgroupOf (U Rg a)) = Nat.card (U Rg a ⊓ C : Subgroup (FreeAmalgam Rg)) := by
    rw [←card_map_of_injective (U Rg a).subtype_injective]
    congr 1
    rw [subgroupOf, map_comap_eq,range_subtype,inf_comm]
  rw [hc] at hi
  have hu := graph_U_card h e hz hk a ha
  change Nat.card (U Rg a ⊓ C : Subgroup (FreeAmalgam Rg)) ≤ 2
  omega

include h e hz in
private theorem full_seed_edge_commutator_le_moving
    {a s : Vertex Rg} (ha : color Rg a = false) (has : Adjacent Rg a s) :
    ⁅Z Rg a,Q Rg s⁆ ≤ U Rg a := by
  have he := full_fixed_seed_edge_commutator h e hz ha has
    (⊥ : Subgroup (FreeAmalgam Rg)) bot_le (Q Rg s) le_rfl
  have hbot : centralizer ((⊥ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) = ⊤ := by
    apply top_unique
    intro x _ y hy
    have hy1 : y = 1 := mem_bot.mp hy
    simp only [hy1,mul_one,one_mul]
  rw [hbot,inf_top_eq,inf_top_eq] at he
  rw [he]
  exact le_normalizer_iff_commutator_le_left.mp
    ((show Q Rg s ≤ stabilizer Rg a from
      fun _ hx => hx.2 _ (adjacent_symm Rg has)).trans (U_normalized a))

include h e hz hk in
/-- An opposite generating plane edge moves a noncentral line outside the
full fixed seed of every four-image subactor in the original edge. -/
theorem plane_generating_edge_mixed_commutator
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a t s : Vertex Rg} (ha : color Rg a = false)
    (hat : Adjacent Rg a t) (has : Adjacent Rg a s)
    (hgen : Q Rg t ⊔ Q Rg s = stabilizer Rg a)
    (H P : Subgroup (FreeAmalgam Rg)) (hHt : H ≤ Z Rg t)
    (hcard : Nat.card H = 2)
    (hnon : H ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) = ⊥)
    (hP : P ≤ Q Rg t) (hindex : (Q Rg a).relIndex P = 4) :
    ⁅⁅H,Q Rg s⁆,P⁆ ≠ ⊥ := by
  obtain ⟨_,_,hDcard,hDs,_,_,_⟩ :=
    plane_generating_edge_line_growth h e hz hk u hR ha hat has hgen H hHt hcard hnon
  have hDU : ⁅H,Q Rg s⁆ ≤ U Rg a :=
    (commutator_mono (hHt.trans (adjacent_Z_le Rg ha hat)) le_rfl).trans
      (full_seed_edge_commutator_le_moving h e hz ha has)
  intro he
  have hDt : ⁅H,Q Rg s⁆ ≤ Z Rg t := by
    rw [←(plane_four_image_fixed_seed h e hz hk u hR ha hat P hP hindex).1]
    exact le_inf (hDU.trans (DistanceEight.U_le_Z Rg a))
      (commutator_eq_bot_iff_le_centralizer.mp he)
  have hDC : ⁅H,Q Rg s⁆ ≤
      centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    have hh := le_inf hDt hDs
    rw [plane_generating_edge_seed_intersection h e hz hk u hR ha hat has hgen] at hh
    exact hh.trans inf_le_right
  let := finite_Z Rg a
  let : Finite (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
      Subgroup (FreeAmalgam Rg)) := Finite.of_injective
    (inclusion (inf_le_left.trans (DistanceEight.U_le_Z Rg a))) (inclusion_injective _)
  have hh := (card_le_of_le (le_inf hDU hDC)).trans
    (moving_central_attachment_card_le_two h e hz hk ha)
  omega

private theorem exists_conjugate_not_centralizing {F : Type*} [Group F]
    (H A P : Subgroup F) (hHP : H ≤ centralizer (P : Set F))
    (hne : ⁅⁅H,A⁆,P⁆ ≠ ⊥) :
    ∃ g ∈ A, ¬ H.map (MulAut.conj g).toMonoidHom ≤ centralizer (P : Set F) := by
  by_contra! hn
  apply hne
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply commutator_le.mpr
  intro x hx g hg
  have hc : g*x⁻¹*g⁻¹ ∈ centralizer (P : Set F) :=
    hn g hg (mem_map_of_mem (MulAut.conj g).toMonoidHom (H.inv_mem hx))
  simpa only [commutatorElement_def,mul_assoc] using
    (centralizer (P : Set F)).mul_mem (hHP hx) hc

private theorem conjugate_not_centralizing_excludes_normalizer {F : Type*} [Group F]
    (H P A : Subgroup F) (hHA : H ≤ centralizer (A : Set F)) (hPA : P ≤ A)
    (g : F) (hg : ¬ H.map (MulAut.conj g).toMonoidHom ≤ centralizer (P : Set F)) :
    g ∉ normalizer (A : Set F) := by
  intro hn
  apply hg
  calc
    H.map (MulAut.conj g).toMonoidHom ≤
        (centralizer (A : Set F)).map (MulAut.conj g).toMonoidHom := map_mono hHA
    _ = centralizer (A : Set F) :=
      mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_centralizer A hn)
    _ ≤ centralizer (P : Set F) := centralizer_le hPA



include h e hz hk in
/-- On the same escaping path, an actual opposite-edge conjugation fixes the
endpoint and changes both earlier two-cores, the starting radius, and both
radius kernels. The conjugated line fails to centralize the original kernels. -/
theorem plane_small_four_radius_normalizer_escape
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      let c := p.walk.getVert 2
      let Y := V Rg a ⊓ Q Rg c
      let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
      let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ Y = stabilizer Rg z ∧ Q Rg s ⊔ W = stabilizer Rg z ∧
        Nat.card H = 2 ∧ H ≤ Z Rg a ⊓ Z Rg c ∧ H ≤ Z Rg z ∧
        ⁅⁅H,Q Rg s⁆,Y⁆ ≠ ⊥ ∧ ⁅⁅H,Q Rg s⁆,W⁆ ≠ ⊥ ∧
        ∃ g ∈ Q Rg s,
          act Rg g⁻¹ z = z ∧ act Rg g⁻¹ s = s ∧
          act Rg g⁻¹ a ≠ a ∧ act Rg g⁻¹ c ≠ c ∧
          g ∉ normalizer (Q Rg a : Set (FreeAmalgam Rg)) ∧
          g ∉ normalizer (Q Rg c : Set (FreeAmalgam Rg)) ∧
          g ∉ normalizer (V Rg a : Set (FreeAmalgam Rg)) ∧
          g ∉ normalizer (Y : Set (FreeAmalgam Rg)) ∧
          g ∉ normalizer (W : Set (FreeAmalgam Rg)) ∧
          ¬ H.map (MulAut.conj g).toMonoidHom ≤ centralizer (Y : Set (FreeAmalgam Rg)) ∧
          ¬ H.map (MulAut.conj g).toMonoidHom ≤ centralizer (W : Set (FreeAmalgam Rg)) ∧
          H.map (MulAut.conj g).toMonoidHom ⊔
              (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) ≠
            H ⊔ (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            H.map (MulAut.conj g).toMonoidHom ≤
              Z Rg (act Rg g⁻¹ a) ⊓ Z Rg (q.walk.getVert 2) ∧
            H.map (MulAut.conj g).toMonoidHom ≤ Z Rg z ∧
            H.map (MulAut.conj g).toMonoidHom =
              ⁅V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2),
                X Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ := by
  obtain ⟨a,z,p,s,hzs,hgen,hgenY,hgenW,hiY,hiW,hinter,hcard,hHZ,hHlast,hHC,
    hHs,_,_,_,_,_,_,_,_⟩ := plane_small_four_radius_growth h e hz hk u hR hb4 hsmall
  let c := p.walk.getVert 2
  let t := p.walk.getVert 3
  let Y := V Rg a ⊓ Q Rg c
  let W := V Rg a ⊓ Q Rg t
  let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent Rg c t :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z t := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hYt : Y ≤ Q Rg t := inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hYW : Y ≤ W := le_inf inf_le_left hYt
  have hHZz : H ≤ Z Rg z := hHlast.trans (adjacent_Z_le Rg p.end_color hzt)
  have hnon : H ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) = ⊥ := by
    apply le_bot_iff.mp
    apply le_trans _ hHs.le
    refine le_inf inf_le_left ?_
    rw [←(plane_edge_full_seed_fixer h e hz hk u hR p.end_color hzs).1]
    exact le_inf (inf_le_left.trans hHZz)
      (inf_le_right.trans (centralizer_le (show Q Rg s ≤ stabilizer Rg z from
        fun _ hx => hx.2 _ (adjacent_symm Rg hzs))))
  have hpair : Q Rg t ⊔ Q Rg s = stabilizer Rg z := (sup_comm _ _).trans hgen
  have hmixY := plane_generating_edge_mixed_commutator h e hz hk u hR
    p.end_color hzt hzs hpair H Y hHlast hcard hnon hYt hiY
  have hmixW := plane_generating_edge_mixed_commutator h e hz hk u hR
    p.end_color hzt hzs hpair H W hHlast hcard hnon inf_le_right hiW
  have hHV : H ≤ centralizer (V Rg a : Set (FreeAmalgam Rg)) :=
    hHC.trans (centralizer_le (show V Rg a ≤ V Rg a ⊔ V Rg c from le_sup_left))
  have hHY := hHV.trans (centralizer_le (show Y ≤ V Rg a from inf_le_left))
  obtain ⟨g,hgs,hgY⟩ := exists_conjugate_not_centralizing H (Q Rg s) Y hHY hmixY
  have hgW : ¬ H.map (MulAut.conj g).toMonoidHom ≤
      centralizer (W : Set (FreeAmalgam Rg)) :=
    fun hh => hgY (hh.trans (centralizer_le hYW))
  have hgQa := conjugate_not_centralizing_excludes_normalizer H Y (Q Rg a)
    ((hHZ.trans inf_le_left).trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)))
    (inf_le_left.trans ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a p.start_color)) g hgY
  have hgQc := conjugate_not_centralizing_excludes_normalizer H Y (Q Rg c)
    ((hHZ.trans inf_le_right).trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c hc))) inf_le_right g hgY
  have hgV := conjugate_not_centralizing_excludes_normalizer H Y (V Rg a) hHV inf_le_left g hgY
  have hgNY := conjugate_not_centralizing_excludes_normalizer H Y Y hHY le_rfl g hgY
  have hgNW := conjugate_not_centralizing_excludes_normalizer H W W
    (hHV.trans (centralizer_le inf_le_left)) le_rfl g hgW
  have hsep : H.map (MulAut.conj g).toMonoidHom ⊔
      (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) ≠
      H ⊔ (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) := by
    intro he
    apply hgY
    apply le_trans (show H.map (MulAut.conj g).toMonoidHom ≤
      H ⊔ (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) from
        he ▸ le_sup_left)
    exact sup_le hHY (inf_le_right.trans (centralizer_le
      (hYt.trans (show Q Rg t ≤ stabilizer Rg z from
        fun _ hx => hx.2 _ (adjacent_symm Rg hzt)))))
  have hgz : g ∈ stabilizer Rg z := (hgs.2 _ (adjacent_symm Rg hzs))
  have hfixz : act Rg g⁻¹ z = z := (stabilizer Rg z).inv_mem hgz
  have hfixs : act Rg g⁻¹ s = s := (stabilizer Rg s).inv_mem hgs.1
  have hmove (v : Vertex Rg) (hn : g ∉ normalizer (Q Rg v : Set (FreeAmalgam Rg))) :
      act Rg g⁻¹ v ≠ v := by
    intro hv
    apply hn
    apply Q_normalized Rg v
    have hi : g⁻¹ ∈ stabilizer Rg v := hv
    simpa only [inv_inv] using (stabilizer Rg v).inv_mem hi
  have hq : ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
      ∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i) := by
    have hh : ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) (act Rg g⁻¹ z),
        ∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i) := by
      refine ⟨p.act g⁻¹,?_⟩
      intro i
      simp only [CriticalPath.act,actWalk_getVert]
    let P := fun w : Vertex Rg =>
      ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) w,
        ∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)
    exact (congrArg P hfixz).mp hh
  obtain ⟨q,hverts⟩ := hq
  refine ⟨a,z,p,s,hzs,hgenY,hgenW,hcard,hHZ,hHZz,hmixY,hmixW,g,hgs,
    hfixz,hfixs,hmove a hgQa,hmove c hgQc,hgQa,hgQc,hgV,hgNY,hgNW,hgY,hgW,hsep,q,hverts,?_,?_,?_⟩
  · rw [hverts 2,Z_act,Z_act,inv_inv,←Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    exact map_mono hHZ
  · calc
      H.map (MulAut.conj g).toMonoidHom ≤ (Z Rg z).map (MulAut.conj g).toMonoidHom := map_mono hHZz
      _ = Z Rg z := by
        have hh := congrArg (Z Rg) hfixz
        rw [Z_act,inv_inv] at hh
        exact hh
  · have hXfix : (X Rg z).map (MulAut.conj g).toMonoidHom = X Rg z := by
      simpa only [inv_inv,hfixz] using (X_act Rg g⁻¹ z).symm
    change (⁅V Rg a ⊓ Q Rg c,X Rg z ⊓ Q Rg a⁆).map (MulAut.conj g).toMonoidHom = _
    rw [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      Subgroup.map_inf _ _ _ (MulAut.conj g).injective,hXfix,hverts 2,V_act,Q_act,Q_act,inv_inv]
omit hk in
include h e hz in
/-- Whole-core application of the opposite-edge kernel displacement. The
Borel case, both full covers and the actual cubic kernel remain explicit. -/
theorem coreExhaustion_or_cubic_plane_radius_normalizer_escape :
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
          ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
            let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
            ∃ s, Adjacent Rg z s ∧ Q Rg s ⊔ Y = stabilizer Rg z ∧
              Nat.card H = 2 ∧
              ⁅⁅H,Q Rg s⁆,Y⁆ ≠ ⊥ ∧ ⁅⁅H,Q Rg s⁆,W⁆ ≠ ⊥ ∧
              ∃ g ∈ Q Rg s,
                act Rg g⁻¹ z = z ∧ act Rg g⁻¹ s = s ∧
                act Rg g⁻¹ a ≠ a ∧ act Rg g⁻¹ (p.walk.getVert 2) ≠ p.walk.getVert 2 ∧
                g ∉ normalizer (Q Rg a : Set (FreeAmalgam Rg)) ∧
                g ∉ normalizer (Q Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) ∧
                g ∉ normalizer (V Rg a : Set (FreeAmalgam Rg)) ∧
                g ∉ normalizer (Y : Set (FreeAmalgam Rg)) ∧
                g ∉ normalizer (W : Set (FreeAmalgam Rg)) ∧
                ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
                  (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
                  H.map (MulAut.conj g).toMonoidHom =
                    ⁅V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2),
                      X Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆)) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,?_⟩⟩
    intro hb4 hsmall
    obtain ⟨a,z,p,s,hadj,hgen,_,hcard,_,_,hmixY,hmixW,g,hgs,hgz,hgss,hga,hgc,
      hgQa,hgQc,hgV,hgY,hgW,_,_,_,q,hverts,_,_,hline⟩ :=
      plane_small_four_radius_normalizer_escape h e hz hk u hplane hb4 hsmall
    exact ⟨a,z,p,s,hadj,hgen,hcard,hmixY,hmixW,g,hgs,hgz,hgss,hga,hgc,
      hgQa,hgQc,hgV,hgY,hgW,q,hverts,hline⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application on the same cubic graph. The displaced path
and its full kernel line do not yet discharge the terminal contradiction. -/
theorem rankTwo_or_cubic_plane_radius_normalizer_escape :
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
          ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
            let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
            ∃ s, Adjacent Rg z s ∧ Q Rg s ⊔ Y = stabilizer Rg z ∧
              Nat.card H = 2 ∧
              ⁅⁅H,Q Rg s⁆,Y⁆ ≠ ⊥ ∧ ⁅⁅H,Q Rg s⁆,W⁆ ≠ ⊥ ∧
              ∃ g ∈ Q Rg s,
                act Rg g⁻¹ z = z ∧ act Rg g⁻¹ s = s ∧
                act Rg g⁻¹ a ≠ a ∧ act Rg g⁻¹ (p.walk.getVert 2) ≠ p.walk.getVert 2 ∧
                g ∉ normalizer (Q Rg a : Set (FreeAmalgam Rg)) ∧
                g ∉ normalizer (Q Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) ∧
                g ∉ normalizer (V Rg a : Set (FreeAmalgam Rg)) ∧
                g ∉ normalizer (Y : Set (FreeAmalgam Rg)) ∧
                g ∉ normalizer (W : Set (FreeAmalgam Rg)) ∧
                ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
                  (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
                  H.map (MulAut.conj g).toMonoidHom =
                    ⁅V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2),
                      X Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆)) :=
  (coreExhaustion_or_cubic_plane_radius_normalizer_escape h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
