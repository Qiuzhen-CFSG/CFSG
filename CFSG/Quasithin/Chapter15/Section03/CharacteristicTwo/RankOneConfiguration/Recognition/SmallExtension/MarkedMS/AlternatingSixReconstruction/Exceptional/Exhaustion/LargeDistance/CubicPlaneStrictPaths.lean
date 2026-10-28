module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneStrictKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusGeometry

/-!
# Literal four-edge rotations of strict full kernels

Let a--z be a small critical path, c its second predecessor and t its last
edge. The strict-slice calculation gives a residual element k moving the
section (Z_z intersect Q_a) Z_c/Z_c. The full reverse kernel is normalized
by Q_t. Hence k cannot fix t: the stabilizer of the edge c--t is Q_t.
The tree then puts z and its k-conjugate exactly four edges apart, on the
literal path z--t--c--t^k--z^k. The original critical path is also transported
with every vertex and both full kernels recorded.

At critical distance four, put F = Z_z intersect Q_a and let F' be its
actual conjugate. The two kernel-seed joins meet in Z_c and span index four
over Z_c. Their derived subgroup is exactly [F,F'], which lies in Z_c.
If this commutator is trivial, the entire join is elementary abelian. If
it is nontrivial, the new four-edge path is critical, and [F,F'] equals
its full order-two critical commutator. This equality follows from literal
containment and the small critical index, retaining all central attachments.
It does not identify this new critical line with the earlier radius line.

The selected-path application carries this alternative on both original
displaced paths, unless all overlapping shifted comparisons already hold.
It retains their opposite-edge conjugator, exact cross-distances and larger
endpoint commutator. Whole-core and C.1.32 applications retain the original
radical, cubic projection kernel E, nontrivial odd E/Q, and both covers.
The internal graph import reuses the checked shortest-path lemmas without
changing their existing visibility.

Neither derived alternative is a contradiction by itself. Their exclusion
through the original paired selection, the terminal commutator comparison,
remaining image/distance cases and both core exhaustions remain required.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the shifted comparisons toward (5.12)(1),(3), printed pp.924--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
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
/-- A displacer of the full reverse-kernel section moves the last edge.
Its endpoint lies exactly four edges from the original endpoint. -/
theorem plane_strict_kernel_displacer_distance
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (k : FreeAmalgam Rg)
    (hkm : k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)))
    (hmove : ¬ (Z Rg z ⊓ Q Rg a).map (MulAut.conj k).toMonoidHom ≤
      (Z Rg z ⊓ Q Rg a) ⊔ Z Rg (p.walk.getVert (p.walk.length-2))) :
    let c := p.walk.getVert (p.walk.length-2)
    let t := p.walk.getVert (p.walk.length-1)
    act Rg k⁻¹ t ≠ t ∧ (cosetGraph Rg).dist z (act Rg k⁻¹ z) = 4 ∧
      ∃ w : (cosetGraph Rg).Walk z (act Rg k⁻¹ z),
        w.length = 4 ∧ w.IsPath ∧ w.getVert 1 = t ∧
        w.getVert 2 = c ∧ w.getVert 3 = act Rg k⁻¹ t := by
  let c := p.walk.getVert (p.walk.length-2)
  let t := p.walk.getVert (p.walk.length-1)
  let F := Z Rg z ⊓ Q Rg a
  have hb := distance_gt_two h e hz hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color Rg c = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hct : Adjacent Rg c t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hzt : Adjacent Rg z t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hkfix : act Rg k⁻¹ c = c := Ltilde_le_stabilizer c ((Ltilde Rg c).inv_mem hkm)
  have hkfix' : act Rg k c = c := Ltilde_le_stabilizer c hkm
  let pr : CriticalPath Rg (sourceGeometry h) z a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) a p.start_color
        (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
        z p.end_color p.critical⟩
  have hpr : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(small_critical_indices h e hz hk p hp).2]
    decide
  have hfirst : pr.walk.getVert 1 = t := by
    exact SimpleGraph.Walk.getVert_reverse p.walk 1
  have hnF : Q Rg t ≤ normalizer (F : Set (FreeAmalgam Rg)) := by
    have hn := plane_small_critical_first_edge_normalizes_kernel h e hz hk u hR pr hpr
    rw [hfirst] at hn
    exact hn
  have hkt : act Rg k⁻¹ t ≠ t := by
    intro he
    have hkinv : k⁻¹ ∈ Q Rg t := by
      rw [Q_h_eq_edge Rg ht hct]
      exact ⟨hkfix,he⟩
    have hkn : k ∈ normalizer (F : Set (FreeAmalgam Rg)) := hnF (by simpa only [inv_inv] using (Q Rg t).inv_mem hkinv)
    apply hmove
    change F.map (MulAut.conj k).toMonoidHom ≤ F ⊔ Z Rg c
    exact (mem_normalizer_iff_map_conj_eq.mp hkn).le.trans le_sup_left
  have hzc : (cosetGraph Rg).dist z c = 2 := by
    rw [SimpleGraph.dist_comm,p.dist_end]
    omega
  let v : (cosetGraph Rg).Walk z c :=
    .cons ((cosetGraph_adj Rg _ _).mpr hzt)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hct)) .nil)
  have hv : v.length = (cosetGraph Rg).dist z c := by change 2 = _; exact hzc.symm
  have hzz : z ≠ act Rg k⁻¹ z := by
    intro he
    have hkn : k⁻¹ ∈ stabilizer Rg z ⊓ stabilizer Rg c := ⟨he.symm,hkfix⟩
    exact hkt (stabilizes_shortest_vertices Rg v hv 1 hkn)
  let v' : (cosetGraph Rg).Walk (act Rg k⁻¹ z) c :=
    (actWalk Rg k⁻¹ v).copy rfl hkfix
  have hv' : v'.length = (cosetGraph Rg).dist (act Rg k⁻¹ z) c := by
    calc
      v'.length = v.length := by simp [v',actWalk_length]
      _ = (cosetGraph Rg).dist z c := hv
      _ = (cosetGraph Rg).dist (act Rg k⁻¹ z) (act Rg k⁻¹ c) :=
        (dist_act Rg k⁻¹ z c).symm
      _ = _ := by rw [hkfix]
  have hcolorz : color Rg (act Rg k⁻¹ z) = false := by rw [action_preserves_color,p.end_color]
  have hcolort : color Rg (act Rg k⁻¹ t) = true := by rw [action_preserves_color,ht]
  have hcross : z ≠ act Rg k⁻¹ t := fun he => by
    have hh := congrArg (color Rg) he
    rw [p.end_color,hcolort] at hh
    contradiction
  have hcross' : t ≠ act Rg k⁻¹ z := fun he => by
    have hh := congrArg (color Rg) he
    rw [ht,hcolorz] at hh
    contradiction
  have hcommon (x : Vertex Rg) (hx : x ∈ v.support) (hx' : x ∈ v'.support) : x = c := by
    have hs : v.support = [z,t,c] := rfl
    have hs' : v'.support = [act Rg k⁻¹ z,act Rg k⁻¹ t,c] := by
      simp [v',v,SimpleGraph.Walk.support_copy,actWalk,hkfix]
    rw [hs] at hx
    rw [hs'] at hx'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx hx'
    rcases hx with rfl | rfl | he
    · rcases hx' with he | he | he
      · exact (hzz he).elim
      · exact (hcross he).elim
      · exact he
    · rcases hx' with he | he | he
      · exact (hcross' he).elim
      · exact (hkt he.symm).elim
      · exact he
    · exact he
  let w := v.append v'.reverse
  have hwlen : w.length = 4 := by simp [w,v',v,actWalk_length]
  have hw := shortest_append_at_only_common_vertex Rg v v'
    (v.isPath_of_length_eq_dist hv) (v'.isPath_of_length_eq_dist hv') hcommon
  have hd : (cosetGraph Rg).dist z (act Rg k⁻¹ z) = 4 := hw.symm.trans hwlen
  refine ⟨hkt,hd,w,hwlen,w.isPath_of_length_eq_dist hw,?_,?_,?_⟩
  · rfl
  · simp [w,v,c]
  · simp [w,v',v,SimpleGraph.Walk.getVert_reverse,actWalk_getVert,actWalk_length,t]

private theorem two_kernel_join {J : Type*} [Group J]
    (A B C : Subgroup J) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    [IsElementaryAbelian 2 C]
    (hAC : A ≤ centralizer (C : Set J)) (hBC : B ≤ centralizer (C : Set J))
    (hAB : ⁅A,B⁆ ≤ C) :
    let W := (A ⊔ C) ⊔ (B ⊔ C)
    ⁅W,W⁆ = ⁅A,B⁆ ∧ (⁅A,B⁆ = ⊥ → IsElementaryAbelian 2 W) := by
  let N := A ⊔ C
  let N' := B ⊔ C
  let W := N ⊔ N'
  let H := ⁅A,B⁆
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hAC)
  let : IsElementaryAbelian 2 N' := IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hBC)
  have hCC : C ≤ centralizer (C : Set J) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hNC : N ≤ centralizer (C : Set J) := sup_le hAC hCC
  have hN'C : N' ≤ centralizer (C : Set J) := sup_le hBC hCC
  have hCN' : ⁅C,N'⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp hN'C)
  have hCA : ⁅C,A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp hAC)
  have hcross : ⁅N,N'⁆ = H := by
    rw [show N = A ⊔ C from rfl,
      commutator_sup_of_commuting_factors A C N' hAC
        (hN'C.trans (Subgroup.centralizer_le_normalizer _)),hCN',sup_bot_eq,
      commutator_comm A N',show N' = B ⊔ C from rfl,
      commutator_sup_of_commuting_factors B C A hBC
        (hAC.trans (Subgroup.centralizer_le_normalizer _)),hCA,sup_bot_eq,commutator_comm B A]
  have hNH : W ≤ normalizer (H : Set J) :=
    ((sup_le hNC hN'C).trans (centralizer_le hAB)).trans (Subgroup.centralizer_le_normalizer _)
  have hNN : ⁅N,N⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hN'N' : ⁅N',N'⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hWN : ⁅W,N⁆ ≤ H := commutator_sup_le_of_relative_normal W N N' N H hNH
    le_sup_left le_sup_right (hNN.le.trans bot_le) ((commutator_comm N' N).trans hcross).le
  have hWN' : ⁅W,N'⁆ ≤ H := commutator_sup_le_of_relative_normal W N N' N' H hNH
    le_sup_left le_sup_right hcross.le (hN'N'.le.trans bot_le)
  refine ⟨le_antisymm ?_ (commutator_mono (le_sup_left.trans le_sup_left)
    (le_sup_left.trans le_sup_right)),?_⟩
  · exact commutator_sup_le_of_relative_normal W N N' W H hNH le_sup_left le_sup_right
      (commutator_comm N W ▸ hWN) (commutator_comm N' W ▸ hWN')
  · intro hzero
    have hz : ⁅N,N'⁆ = ⊥ := hcross.trans hzero
    exact IsElementaryAbelian.sup_of_le_centralizer
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))

include h e hz hk in
/-- The mixed commutator of the actual displaced full kernels is either
trivial or the full order-two critical commutator on the new four-edge path.
In both cases it lies in the original midpoint seed. -/
theorem plane_strict_kernel_displacer_commutator
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (k : FreeAmalgam Rg)
    (hkm : k ∈ Ltilde Rg (p.walk.getVert 2))
    (hmove : ¬ (Z Rg z ⊓ Q Rg a).map (MulAut.conj k).toMonoidHom ≤
      (Z Rg z ⊓ Q Rg a) ⊔ Z Rg (p.walk.getVert 2)) :
    let c := p.walk.getVert 2
    let F := Z Rg z ⊓ Q Rg a
    let F' := Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ a)
    let W := (F ⊔ Z Rg c) ⊔ (F' ⊔ Z Rg c)
    ⁅W,W⁆ = ⁅F,F'⁆ ∧ ⁅F,F'⁆ ≤ Z Rg c ∧
      (IsElementaryAbelian 2 W ∨
        ∃ r : CriticalPath Rg (sourceGeometry h) z (act Rg k⁻¹ z),
          r.walk.getVert 1 = p.walk.getVert 3 ∧
          r.walk.getVert 2 = c ∧
          r.walk.getVert 3 = act Rg k⁻¹ (p.walk.getVert 3) ∧
          ⁅F,F'⁆ = ⁅Z Rg z,Z Rg (act Rg k⁻¹ z)⁆ ∧
          Nat.card (⁅F,F'⁆ : Subgroup (FreeAmalgam Rg)) = 2) := by
  let c := p.walk.getVert 2
  let F := Z Rg z ⊓ Q Rg a
  let F' := Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ a)
  let H := ⁅F,F'⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hkm' : k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using hkm
  have hmove' : ¬ F.map (MulAut.conj k).toMonoidHom ≤
      F ⊔ Z Rg (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using hmove
  obtain ⟨_,hd,w,hw,hpath,hw1,hw2,hw3⟩ :=
    plane_strict_kernel_displacer_distance h e hz hk u hR p (hsmall _ _ p) k hkm' hmove'
  simp only [hl,Nat.reduceSub] at hw1 hw2 hw3
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hFV : F ≤ V Rg c := by
    apply inf_le_left.trans
    have hdist : (cosetGraph Rg).dist z c ≤ 2 := by
      rw [SimpleGraph.dist_comm,p.dist_end,hl]
    exact le_iSup_of_le z (le_iSup_of_le hdist le_rfl)
  have hfix : act Rg k⁻¹ c = c := Ltilde_le_stabilizer c ((Ltilde Rg c).inv_mem hkm)
  have hFmap : F.map (MulAut.conj k).toMonoidHom = F' := by
    rw [show F = Z Rg z ⊓ Q Rg a from rfl,
      Subgroup.map_inf _ _ _ (MulAut.conj k).injective]
    simp only [F',Z_act,Q_act,inv_inv]
  have hF'V : F' ≤ V Rg c := by
    rw [←hFmap]
    exact (map_mono hFV).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp
        ((DistanceEight.V_normalized Rg c) (Ltilde_le_stabilizer c hkm)))
  have hHZ : H ≤ Z Rg c :=
    (commutator_mono hFV (hF'V.trans
      ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) c hc))).trans
        (plane_radius_core_commutator h e hz hk u hR hc)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hcol : color Rg (act Rg k⁻¹ z) = false := by
    rw [action_preserves_color,p.end_color]
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) (act Rg k⁻¹ z) hcol
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c hc
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le (show F ≤ Z Rg z from inf_le_left)
  let : IsElementaryAbelian 2 F' := IsElementaryAbelian.of_le
    (show F' ≤ Z Rg (act Rg k⁻¹ z) from inf_le_left)
  have hQC : Q Rg c ≤ centralizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c hc))
  have halgebra := two_kernel_join F F' (Z Rg c)
    ((hFV.trans ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) c hc)).trans hQC)
    ((hF'V.trans ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) c hc)).trans hQC) hHZ
  refine ⟨halgebra.1,hHZ,?_⟩
  by_cases hzero : H = ⊥
  · exact Or.inl (halgebra.2 hzero)
  · have hesc : ¬ Z Rg z ≤ Q Rg (act Rg k⁻¹ z) := by
      intro hle
      apply hzero
      apply le_bot_iff.mp
      have hcol : color Rg (act Rg k⁻¹ z) = false := by
        rw [action_preserves_color,p.end_color]
      have hzq := Z_centralizes_Q Rg (act Rg k⁻¹ z) hcol
      rw [commutator_comm] at hzq
      exact (commutator_mono (inf_le_left.trans hle) inf_le_left).trans_eq hzq
    let r : CriticalPath Rg (sourceGeometry h) z (act Rg k⁻¹ z) :=
      ⟨p.end_color,w,hw.trans hd.symm,by
        refine ⟨?_,hesc⟩
        rw [(sourceGeometry h).distance_constant _ p.end_color]
        exact hd.trans hb4.symm⟩
    have hcard := small_critical_commutator_card h e hz hk r (hsmall _ _ r)
    let C := ⁅Z Rg z,Z Rg (act Rg k⁻¹ z)⁆
    have hHC : H ≤ C := commutator_mono inf_le_left inf_le_left
    let : Finite C := Nat.finite_of_card_ne_zero (by rw [show Nat.card C = 2 from hcard]; decide)
    let : Finite H := Finite.of_injective (inclusion hHC) (inclusion_injective _)
    have hlo : 1 < Nat.card H := (one_lt_card_iff_ne_bot H).mpr hzero
    have he : H = C := eq_of_le_of_card_ge hHC (by rw [hcard]; omega)
    exact Or.inr ⟨r,hw1,hw2,hw3,he,by change Nat.card H = 2; rw [he]; exact hcard⟩

include h e hz hk in
/-- A strict predecessor slice gives literal rotated full kernels. Their
join has index four over the midpoint seed and is either elementary or has
the exact critical line on the new four-edge path as its derived subgroup. -/
theorem plane_strict_predecessor_kernel_geometry
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hs : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg z)) :
    let c := p.walk.getVert 2
    let t := p.walk.getVert 3
    let F := Z Rg z ⊓ Q Rg a
    ∃ k ∈ Ltilde Rg c, act Rg k⁻¹ c = c ∧
      act Rg k⁻¹ t ≠ t ∧ (cosetGraph Rg).dist z (act Rg k⁻¹ z) = 4 ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg k⁻¹ a) (act Rg k⁻¹ z),
        (∀ i, q.walk.getVert i = act Rg k⁻¹ (p.walk.getVert i)) ∧
        let F' := Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ a)
        let N := F ⊔ Z Rg c
        let N' := F' ⊔ Z Rg c
        let W := N ⊔ N'
        ¬ F' ≤ N ∧ N ⊓ N' = Z Rg c ∧ (Z Rg c).relIndex W = 4 ∧
          ⁅W,W⁆ = ⁅F,F'⁆ ∧ ⁅F,F'⁆ ≤ Z Rg c ∧
          (IsElementaryAbelian 2 W ∨
            ∃ r : CriticalPath Rg (sourceGeometry h) z (act Rg k⁻¹ z),
              r.walk.getVert 1 = t ∧ r.walk.getVert 2 = c ∧
              r.walk.getVert 3 = act Rg k⁻¹ t ∧
              ⁅F,F'⁆ = ⁅Z Rg z,Z Rg (act Rg k⁻¹ z)⁆ ∧
              Nat.card (⁅F,F'⁆ : Subgroup (FreeAmalgam Rg)) = 2) := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hs' : 2 < (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) := by
    simpa only [hl,Nat.reduceSub] using hs
  obtain ⟨k,hkm,hfix,hmove,hI,hindex⟩ :=
    plane_strict_predecessor_kernel_displacement h e hz hk u hR p (hsmall _ _ p) hs'
  simp only [hl,Nat.reduceSub] at hkm hfix hmove hI hindex
  have hkm' : k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using hkm
  have hmove' : ¬ (Z Rg z ⊓ Q Rg a).map (MulAut.conj k).toMonoidHom ≤
      (Z Rg z ⊓ Q Rg a) ⊔ Z Rg (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using hmove
  obtain ⟨hne,hd,_⟩ :=
    plane_strict_kernel_displacer_distance h e hz hk u hR p (hsmall _ _ p) k hkm' hmove'
  simp only [hl,Nat.reduceSub] at hne
  have hmap : (Z Rg z ⊓ Q Rg a).map (MulAut.conj k).toMonoidHom =
      Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ a) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj k).injective]
    simp only [Z_act,Q_act,inv_inv]
  have hc := plane_strict_kernel_displacer_commutator h e hz hk u hR hb4 hsmall p k hkm hmove
  rw [hmap] at hmove hI hindex
  exact ⟨k,hkm,hfix,hne,hd,p.act k⁻¹,fun i => by simp only [CriticalPath.act,actWalk_getVert],
    hmove,hI,hindex,hc⟩

include h e hz hk in
/-- On both original displaced paths, the strict alternative supplies
literal rotated critical paths and exact derived-subgroup comparisons.
The original larger endpoint commutator and selected pair are retained. -/
theorem plane_small_four_strict_kernel_geometry
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) ∧
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let F := Z Rg z ⊓ Q Rg a
            let T := ⁅Z Rg a,Z Rg z⁆
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            let F₁ := Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)
            let c₀ := p.walk.getVert 2
            let c₁ := q.walk.getVert 2
            let N₀ := F ⊔ Z Rg c₀
            let N₁ := F₁ ⊔ Z Rg c₁
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,F₁⁆ = C ∧
              (((∃ k ∈ Ltilde Rg c₀, act Rg k⁻¹ c₀ = c₀ ∧
                  act Rg k⁻¹ (p.walk.getVert 3) ≠ p.walk.getVert 3 ∧
                  (cosetGraph Rg).dist z (act Rg k⁻¹ z) = 4 ∧
                  ∃ v : CriticalPath Rg (sourceGeometry h) (act Rg k⁻¹ a) (act Rg k⁻¹ z),
                    (∀ i, v.walk.getVert i = act Rg k⁻¹ (p.walk.getVert i)) ∧
                    let F' := Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ a)
                    let N' := F' ⊔ Z Rg c₀
                    let W := N₀ ⊔ N'
                    ¬ F' ≤ N₀ ∧ N₀ ⊓ N' = Z Rg c₀ ∧ (Z Rg c₀).relIndex W = 4 ∧
                      ⁅W,W⁆ = ⁅F,F'⁆ ∧ ⁅F,F'⁆ ≤ Z Rg c₀ ∧
                      (IsElementaryAbelian 2 W ∨
                        ∃ r : CriticalPath Rg (sourceGeometry h) z (act Rg k⁻¹ z),
                          r.walk.getVert 1 = p.walk.getVert 3 ∧
                          r.walk.getVert 2 = c₀ ∧
                          r.walk.getVert 3 = act Rg k⁻¹ (p.walk.getVert 3) ∧
                          ⁅F,F'⁆ = ⁅Z Rg z,Z Rg (act Rg k⁻¹ z)⁆ ∧
                          Nat.card (⁅F,F'⁆ : Subgroup (FreeAmalgam Rg)) = 2)) ∧
                (∃ l ∈ Ltilde Rg c₁, act Rg l⁻¹ c₁ = c₁ ∧
                  act Rg l⁻¹ (q.walk.getVert 3) ≠ q.walk.getVert 3 ∧
                  (cosetGraph Rg).dist z (act Rg l⁻¹ z) = 4 ∧
                  ∃ v : CriticalPath Rg (sourceGeometry h) (act Rg l⁻¹ (act Rg g⁻¹ a)) (act Rg l⁻¹ z),
                    (∀ i, v.walk.getVert i = act Rg l⁻¹ (q.walk.getVert i)) ∧
                    let F' := Z Rg (act Rg l⁻¹ z) ⊓ Q Rg (act Rg l⁻¹ (act Rg g⁻¹ a))
                    let N' := F' ⊔ Z Rg c₁
                    let W := N₁ ⊔ N'
                    ¬ F' ≤ N₁ ∧ N₁ ⊓ N' = Z Rg c₁ ∧ (Z Rg c₁).relIndex W = 4 ∧
                      ⁅W,W⁆ = ⁅F₁,F'⁆ ∧ ⁅F₁,F'⁆ ≤ Z Rg c₁ ∧
                      (IsElementaryAbelian 2 W ∨
                        ∃ r : CriticalPath Rg (sourceGeometry h) z (act Rg l⁻¹ z),
                          r.walk.getVert 1 = q.walk.getVert 3 ∧
                          r.walk.getVert 2 = c₁ ∧
                          r.walk.getVert 3 = act Rg l⁻¹ (q.walk.getVert 3) ∧
                          ⁅F₁,F'⁆ = ⁅Z Rg z,Z Rg (act Rg l⁻¹ z)⁆ ∧
                          Nat.card (⁅F₁,F'⁆ : Subgroup (FreeAmalgam Rg)) = 2))) ∨
                ((∀ d (r : CriticalPath Rg (sourceGeometry h) d c₀),
                    r.walk.getVert 2 = a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg c₀ →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,F⁆ ⊔ T) ∧
                  (∀ d (r : CriticalPath Rg (sourceGeometry h) d c₁),
                    r.walk.getVert 2 = act Rg g⁻¹ a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg c₁ →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,F₁⁆ ⊔
                        ⁅Z Rg (act Rg g⁻¹ a),Z Rg z⁆))) := by
  obtain ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,hcard,hstrict,hbig,hopp,halt⟩ :=
    plane_small_four_shifted_slice_comparison h e hz hk u hR hb4 hsmall
  refine ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,hcard,hstrict,hbig,hopp,?_⟩
  rcases halt with hs | hcomp
  · have hb := distance_gt_two h e hz hk
    have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
    have hc : color Rg (p.walk.getVert 2) = false :=
      (p.vertex_color (by omega)).mpr (by decide)
    have hUz : (U Rg z).map (MulAut.conj g).toMonoidHom = U Rg z := by
      simpa only [inv_inv,hfix] using (U_act Rg g⁻¹ z).symm
    have hs' : 2 < (B Rg (q.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg z) := by
      rw [hverts 2,Escape.PairingControl.FirstPairing.B_act
        (geometry := sourceGeometry h) hb _ _ hc,inv_inv,←hUz,
        relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
      exact hs
    exact Or.inl ⟨plane_strict_predecessor_kernel_geometry h e hz hk u hR hb4 hsmall p hs,
      plane_strict_predecessor_kernel_geometry h e hz hk u hR hb4 hsmall q hs'⟩
  · exact Or.inr hcomp

omit hk in
include h e hz in
/-- Whole-core application retaining both original paths and both covers,
with literal four-edge rotations and the two exact derived alternatives. -/
theorem coreExhaustion_or_cubic_strict_kernel_geometry :
    CoreExhaustion L R ∨
    ∃ hk : layerKernel L R = extensionKernel h,
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
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) ∧
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let F := Z Rg z ⊓ Q Rg a
            let T := ⁅Z Rg a,Z Rg z⁆
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            let F₁ := Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)
            let c₀ := p.walk.getVert 2
            let c₁ := q.walk.getVert 2
            let N₀ := F ⊔ Z Rg c₀
            let N₁ := F₁ ⊔ Z Rg c₁
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,F₁⁆ = C ∧
              (((∃ k ∈ Ltilde Rg c₀, act Rg k⁻¹ c₀ = c₀ ∧
                  act Rg k⁻¹ (p.walk.getVert 3) ≠ p.walk.getVert 3 ∧
                  (cosetGraph Rg).dist z (act Rg k⁻¹ z) = 4 ∧
                  ∃ v : CriticalPath Rg (sourceGeometry h) (act Rg k⁻¹ a) (act Rg k⁻¹ z),
                    (∀ i, v.walk.getVert i = act Rg k⁻¹ (p.walk.getVert i)) ∧
                    let F' := Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ a)
                    let N' := F' ⊔ Z Rg c₀
                    let W := N₀ ⊔ N'
                    ¬ F' ≤ N₀ ∧ N₀ ⊓ N' = Z Rg c₀ ∧ (Z Rg c₀).relIndex W = 4 ∧
                      ⁅W,W⁆ = ⁅F,F'⁆ ∧ ⁅F,F'⁆ ≤ Z Rg c₀ ∧
                      (IsElementaryAbelian 2 W ∨
                        ∃ r : CriticalPath Rg (sourceGeometry h) z (act Rg k⁻¹ z),
                          r.walk.getVert 1 = p.walk.getVert 3 ∧
                          r.walk.getVert 2 = c₀ ∧
                          r.walk.getVert 3 = act Rg k⁻¹ (p.walk.getVert 3) ∧
                          ⁅F,F'⁆ = ⁅Z Rg z,Z Rg (act Rg k⁻¹ z)⁆ ∧
                          Nat.card (⁅F,F'⁆ : Subgroup (FreeAmalgam Rg)) = 2)) ∧
                (∃ l ∈ Ltilde Rg c₁, act Rg l⁻¹ c₁ = c₁ ∧
                  act Rg l⁻¹ (q.walk.getVert 3) ≠ q.walk.getVert 3 ∧
                  (cosetGraph Rg).dist z (act Rg l⁻¹ z) = 4 ∧
                  ∃ v : CriticalPath Rg (sourceGeometry h) (act Rg l⁻¹ (act Rg g⁻¹ a)) (act Rg l⁻¹ z),
                    (∀ i, v.walk.getVert i = act Rg l⁻¹ (q.walk.getVert i)) ∧
                    let F' := Z Rg (act Rg l⁻¹ z) ⊓ Q Rg (act Rg l⁻¹ (act Rg g⁻¹ a))
                    let N' := F' ⊔ Z Rg c₁
                    let W := N₁ ⊔ N'
                    ¬ F' ≤ N₁ ∧ N₁ ⊓ N' = Z Rg c₁ ∧ (Z Rg c₁).relIndex W = 4 ∧
                      ⁅W,W⁆ = ⁅F₁,F'⁆ ∧ ⁅F₁,F'⁆ ≤ Z Rg c₁ ∧
                      (IsElementaryAbelian 2 W ∨
                        ∃ r : CriticalPath Rg (sourceGeometry h) z (act Rg l⁻¹ z),
                          r.walk.getVert 1 = q.walk.getVert 3 ∧
                          r.walk.getVert 2 = c₁ ∧
                          r.walk.getVert 3 = act Rg l⁻¹ (q.walk.getVert 3) ∧
                          ⁅F₁,F'⁆ = ⁅Z Rg z,Z Rg (act Rg l⁻¹ z)⁆ ∧
                          Nat.card (⁅F₁,F'⁆ : Subgroup (FreeAmalgam Rg)) = 2))) ∨
                ((∀ d (r : CriticalPath Rg (sourceGeometry h) d c₀),
                    r.walk.getVert 2 = a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg c₀ →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,F⁆ ⊔ T) ∧
                  (∀ d (r : CriticalPath Rg (sourceGeometry h) d c₁),
                    r.walk.getVert 2 = act Rg g⁻¹ a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg c₁ →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,F₁⁆ ⊔
                        ⁅Z Rg (act Rg g⁻¹ a),Z Rg z⁆))))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_strict_kernel_geometry h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application through the actual cubic projection, retaining
the original radical and the nontrivial odd quotient of its extension kernel. -/
theorem rankTwo_or_cubic_strict_kernel_geometry :
    RankTwoAlternatives L R ∨
    ∃ hk : layerKernel L R = extensionKernel h,
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
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ (V Rg a ⊓ Q Rg (p.walk.getVert 2)) = stabilizer Rg z ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            (∀ i j, (cosetGraph Rg).dist (p.walk.getVert i) (q.walk.getVert j) =
              (4-i) + (4-j)) ∧
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let F := Z Rg z ⊓ Q Rg a
            let T := ⁅Z Rg a,Z Rg z⁆
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            let F₁ := Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)
            let c₀ := p.walk.getVert 2
            let c₁ := q.walk.getVert 2
            let N₀ := F ⊔ Z Rg c₀
            let N₁ := F₁ ⊔ Z Rg c₁
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,F₁⁆ = C ∧
              (((∃ k ∈ Ltilde Rg c₀, act Rg k⁻¹ c₀ = c₀ ∧
                  act Rg k⁻¹ (p.walk.getVert 3) ≠ p.walk.getVert 3 ∧
                  (cosetGraph Rg).dist z (act Rg k⁻¹ z) = 4 ∧
                  ∃ v : CriticalPath Rg (sourceGeometry h) (act Rg k⁻¹ a) (act Rg k⁻¹ z),
                    (∀ i, v.walk.getVert i = act Rg k⁻¹ (p.walk.getVert i)) ∧
                    let F' := Z Rg (act Rg k⁻¹ z) ⊓ Q Rg (act Rg k⁻¹ a)
                    let N' := F' ⊔ Z Rg c₀
                    let W := N₀ ⊔ N'
                    ¬ F' ≤ N₀ ∧ N₀ ⊓ N' = Z Rg c₀ ∧ (Z Rg c₀).relIndex W = 4 ∧
                      ⁅W,W⁆ = ⁅F,F'⁆ ∧ ⁅F,F'⁆ ≤ Z Rg c₀ ∧
                      (IsElementaryAbelian 2 W ∨
                        ∃ r : CriticalPath Rg (sourceGeometry h) z (act Rg k⁻¹ z),
                          r.walk.getVert 1 = p.walk.getVert 3 ∧
                          r.walk.getVert 2 = c₀ ∧
                          r.walk.getVert 3 = act Rg k⁻¹ (p.walk.getVert 3) ∧
                          ⁅F,F'⁆ = ⁅Z Rg z,Z Rg (act Rg k⁻¹ z)⁆ ∧
                          Nat.card (⁅F,F'⁆ : Subgroup (FreeAmalgam Rg)) = 2)) ∧
                (∃ l ∈ Ltilde Rg c₁, act Rg l⁻¹ c₁ = c₁ ∧
                  act Rg l⁻¹ (q.walk.getVert 3) ≠ q.walk.getVert 3 ∧
                  (cosetGraph Rg).dist z (act Rg l⁻¹ z) = 4 ∧
                  ∃ v : CriticalPath Rg (sourceGeometry h) (act Rg l⁻¹ (act Rg g⁻¹ a)) (act Rg l⁻¹ z),
                    (∀ i, v.walk.getVert i = act Rg l⁻¹ (q.walk.getVert i)) ∧
                    let F' := Z Rg (act Rg l⁻¹ z) ⊓ Q Rg (act Rg l⁻¹ (act Rg g⁻¹ a))
                    let N' := F' ⊔ Z Rg c₁
                    let W := N₁ ⊔ N'
                    ¬ F' ≤ N₁ ∧ N₁ ⊓ N' = Z Rg c₁ ∧ (Z Rg c₁).relIndex W = 4 ∧
                      ⁅W,W⁆ = ⁅F₁,F'⁆ ∧ ⁅F₁,F'⁆ ≤ Z Rg c₁ ∧
                      (IsElementaryAbelian 2 W ∨
                        ∃ r : CriticalPath Rg (sourceGeometry h) z (act Rg l⁻¹ z),
                          r.walk.getVert 1 = q.walk.getVert 3 ∧
                          r.walk.getVert 2 = c₁ ∧
                          r.walk.getVert 3 = act Rg l⁻¹ (q.walk.getVert 3) ∧
                          ⁅F₁,F'⁆ = ⁅Z Rg z,Z Rg (act Rg l⁻¹ z)⁆ ∧
                          Nat.card (⁅F₁,F'⁆ : Subgroup (FreeAmalgam Rg)) = 2))) ∨
                ((∀ d (r : CriticalPath Rg (sourceGeometry h) d c₀),
                    r.walk.getVert 2 = a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg c₀ →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,F⁆ ⊔ T) ∧
                  (∀ d (r : CriticalPath Rg (sourceGeometry h) d c₁),
                    r.walk.getVert 2 = act Rg g⁻¹ a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg c₁ →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,F₁⁆ ⊔
                        ⁅Z Rg (act Rg g⁻¹ a),Z Rg z⁆))))) :=
  (coreExhaustion_or_cubic_strict_kernel_geometry h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
