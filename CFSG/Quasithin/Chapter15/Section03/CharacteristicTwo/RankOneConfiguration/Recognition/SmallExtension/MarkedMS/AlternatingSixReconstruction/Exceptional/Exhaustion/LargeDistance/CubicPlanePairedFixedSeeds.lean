module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneForwardAction
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCriticalPlane

/-!
# Full fixed seeds on the original paired cubic paths

For the escaping path a--v--c--t--z, put Y = V_a intersect Q_c and
F = Z_z intersect Q_a. The earlier four-image theorem identifies C_{Z_z}(Y)
with the full last-edge seed Z_t. The critical kernel F contains this seed
with index two.

The opposite displaced path has full kernel F'. Its actual critical-line
supplement gives Z_z = F' times T, where T = [Z_a,Z_z] has order two and
centralizes Y. Thus the full fixed subgroup splits as
Z_t = T times (F' intersect Z_t), with trivial factor intersection. The
second factor has index two in Z_t and index four in F'. In particular the
same radius has fixed index two on its own full kernel and four on the
opposite full kernel. These statements retain the full central attachments.

The original opposite-edge conjugator has square centralizing Z_z. This
transports both the supplement and its disjointness back to the original
kernel, so both directions hold on the same retained pair of paths. The
whole-core and literal C.1.32 applications retain exact cross-distances,
generation, the larger endpoint commutator, both covers of orders sixteen
and thirty-two, and the original proper odd-index radical. The projection
kernel remains E = extensionKernel, with nontrivial odd E/Q.

This gives exact paired fixed subgroups for the remaining commutator
comparison. It does not assert the terminal contradiction, the other
image/distance/Borel exclusions, either core exhaustion or unconditional
A6 reconstruction. The internal import reuses the existing square-centrality
transport without changing its public boundary.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii) and the paired comparisons in (5.12)(1),(3), printed
pp.866--867,924--927; Aschbacher--Smith C.1.31--32, printed pp.135--136.
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
/-- Specialize the earlier full-seed fixer to this radius and compute its
index inside the original critical kernel. -/
private theorem radius_fixed_seed
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a) :
    let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
    let F := Z Rg z ⊓ Q Rg a
    let C := centralizer (Y : Set (FreeAmalgam Rg))
    Z Rg z ⊓ C = Z Rg (p.walk.getVert 3) ∧
      F ⊓ C = Z Rg (p.walk.getVert 3) ∧
      C.relIndex F = 2 ∧ C.relIndex (Z Rg z) = 4 := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 3
  let Y := V Rg a ⊓ Q Rg c
  let F := Z Rg z ⊓ Q Rg a
  let C := centralizer (Y : Set (FreeAmalgam Rg))
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
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
  have hYt : Y ≤ Q Rg (p.walk.getVert (p.walk.length-1)) := by
    rw [hl]
    exact inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hforward := plane_radius_first_edge_action h e hz hk u hR hb4 hsmall p hescape
  have hAY : Z Rg a ≤ Y := (Z_le_localZSpan Rg _ _).trans hforward.1
  have hi := plane_radius_subactor_index_four h e hz hk u hR p (hsmall _ _ p)
    Y inf_le_left hYt hAY hescape
  have hfixed := plane_four_image_fixed_seed h e hz hk u hR p.end_color hzt Y
    (by simpa only [hl,Nat.reduceSub] using hYt) hi
  have hfull : C.relIndex (Z Rg z) = 4 := by
    rw [←inf_relIndex_left (Z Rg z),hfixed.1]
    exact (plane_edge_full_seed_fixer h e hz hk u hR p.end_color hzt).2.1
  let pr := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by
        rw [(sourceGeometry h).distance_constant _ p.start_color]
        exact sourceDistance_pos h) z p.end_color p.critical)
  have hCF : Z Rg z ⊓ C ≤ F :=
    (inf_le_inf_left _ (centralizer_le hAY)).trans_eq
      (critical_seed_centralizer_intersection h e pr)
  have he : Z Rg z ⊓ C = F ⊓ C := le_antisymm (le_inf hCF inf_le_right)
    (inf_le_inf_right _ inf_le_left)
  have hm := relIndex_mul_relIndex (Z Rg z ⊓ C) F (Z Rg z) hCF inf_le_left
  have hFC : (Z Rg z ⊓ C).relIndex F = C.relIndex F := by
    rw [he,inf_relIndex_left]
  rw [hFC,show F.relIndex (Z Rg z) = 2 by
    rw [show F = Z Rg z ⊓ Q Rg a from rfl,inf_relIndex_left]
    exact (small_critical_indices h e hz hk p (hsmall _ _ p)).2,
    inf_relIndex_left,hfull] at hm
  exact ⟨hfixed.1,he.symm.trans hfixed.1,by change C.relIndex F = 2; omega,hfull⟩

private theorem fixed_supplement_relIndex {J : Type*} [Group J]
    (A F T Z : Subgroup J) [IsMulCommutative Z]
    (hs : F ⊔ T = Z) (hTC : T ≤ centralizer (A : Set J)) :
    (centralizer (A : Set J)).relIndex F =
      (centralizer (A : Set J)).relIndex Z := by
  let C := Z ⊓ centralizer (A : Set J)
  have hFZ : F ≤ Z := hs ▸ le_sup_left
  have hTZ : T ≤ Z := hs ▸ le_sup_right
  have hCZ : C ≤ Z := inf_le_left
  have hgen : C ⊔ F = Z := le_antisymm (sup_le hCZ hFZ) (by
    rw [←hs]
    exact sup_le le_sup_right ((le_inf hTZ hTC).trans le_sup_left))
  let _ : (C.subgroupOf Z).Normal := normal_of_isMulCommutative _
  have hi := relIndex_sup_left (F.subgroupOf Z) (C.subgroupOf Z)
  rw [←subgroupOf_sup hCZ hFZ,hgen,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf hFZ] at hi
  have hCF : C.relIndex F = (centralizer (A : Set J)).relIndex F := by
    change (Z ⊓ centralizer (A : Set J)).relIndex F = _
    rw [inf_comm,←relIndex_inf_mul_relIndex,inf_eq_right.mpr hFZ,
      relIndex_eq_one.mpr hFZ,mul_one]
  rw [hCF] at hi
  exact hi.symm.trans (inf_relIndex_left _ _)

include h e hz hk in
/-- The last-edge seed is the fixed subgroup in the original full kernel.
Its opposite-kernel intersection has index two in that seed and index four
in the opposite kernel, and complements the original critical line. -/
theorem plane_radius_paired_fixed_seed
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a b z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    (hsupp : (Z Rg z ⊓ Q Rg b) ⊔ ⁅Z Rg a,Z Rg z⁆ = Z Rg z)
    (hdis : ⁅Z Rg a,Z Rg z⁆ ⊓ (Z Rg z ⊓ Q Rg b) = ⊥) :
    let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
    let F' := Z Rg z ⊓ Q Rg b
    let T := ⁅Z Rg a,Z Rg z⁆
    let C := centralizer (Y : Set (FreeAmalgam Rg))
    let Zt := Z Rg (p.walk.getVert 3)
    Z Rg z ⊓ C = Zt ∧ (Z Rg z ⊓ Q Rg a) ⊓ C = Zt ∧
      C.relIndex (Z Rg z ⊓ Q Rg a) = 2 ∧ C.relIndex F' = 4 ∧
      Zt = T ⊔ (F' ⊓ Zt) ∧ (F' ⊓ Zt).relIndex Zt = 2 ∧ T ⊓ (F' ⊓ Zt) = ⊥ := by
  let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
  let F' := Z Rg z ⊓ Q Rg b
  let T := ⁅Z Rg a,Z Rg z⁆
  have hTa : T ≤ Z Rg a := le_normalizer_iff_commutator_le_left.mp
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      p.critical).trans (Z_normalized Rg a))
  have hTC : T ≤ centralizer (Y : Set (FreeAmalgam Rg)) :=
    (hTa.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a p.start_color))).trans
        (centralizer_le (inf_le_left.trans
          ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a p.start_color)))
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hTZ : T ≤ Z Rg z := hsupp ▸ le_sup_right
  have hTF : T ≤ normalizer (F' : Set (FreeAmalgam Rg)) :=
    ((hTZ.trans (le_centralizer (H := Z Rg z))).trans
      (centralizer_le (show F' ≤ Z Rg z from inf_le_left))).trans
        (Subgroup.centralizer_le_normalizer _)
  let C := centralizer (Y : Set (FreeAmalgam Rg))
  let Zt := Z Rg (p.walk.getVert 3)
  let J := F' ⊓ Zt
  have hlocal := radius_fixed_seed h e hz hk u hR hb4 hsmall p hescape
  have hE : Z Rg z ⊓ C = Zt := hlocal.1
  have hF'C : F' ⊓ C = F' ⊓ Zt := by
    rw [←hE,←inf_assoc,inf_eq_left.mpr (show F' ≤ Z Rg z from inf_le_left)]
  have hsplit : Zt = T ⊔ J := by
    change Zt = T ⊔ (F' ⊓ Zt)
    rw [←hF'C,←hE]
    conv_lhs => rw [←hsupp,sup_comm F' T]
    exact inf_centralizer_sup_of_centralizing T F' Y hTF hTC
  have hTJ : T ⊓ J = ⊥ := le_bot_iff.mp
    ((inf_le_inf_left T (show J ≤ F' from inf_le_left)).trans_eq hdis)
  have hJZ : J ≤ Z Rg z := inf_le_left.trans inf_le_left
  have hJT : J ≤ normalizer (T : Set (FreeAmalgam Rg)) :=
    ((hJZ.trans (le_centralizer (H := Z Rg z))).trans
      (centralizer_le hTZ)).trans (Subgroup.centralizer_le_normalizer _)
  have hcardE : Nat.card Zt = 2 * Nat.card J := by
    rw [hsplit,card_sup_eq_mul_of_normalizes_of_disjoint T J hJT (disjoint_iff.mpr hTJ),
      small_critical_commutator_card h e hz hk p (hsmall _ _ p)]
  let := finite_Z Rg z
  let : Finite J := Finite.of_injective (inclusion hJZ) (inclusion_injective _)
  have hprod := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam Rg)) J Zt bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,hcardE,mul_comm 2 (Nat.card J)] at hprod
  have hji : J.relIndex Zt = 2 := Nat.eq_of_mul_eq_mul_left Nat.card_pos hprod
  exact ⟨hlocal.1,hlocal.2.1,hlocal.2.2.1,
    (fixed_supplement_relIndex Y F' T (Z Rg z) hsupp hTC).trans hlocal.2.2.2,
    hsplit,hji,hTJ⟩

include h e hz hk in
/-- Both original displaced paths have fixed index two on their own full
kernel and fixed index four on the opposite full kernel. The endpoint fixed
subgroup splits over the original critical line in each direction. -/
theorem plane_small_four_paired_fixed_seeds
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
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            let fixed := fun b (r : CriticalPath Rg (sourceGeometry h) b z) b' =>
              let Y₀ := V Rg b ⊓ Q Rg (r.walk.getVert 2)
              let F₀ := Z Rg z ⊓ Q Rg b
              let F₁ := Z Rg z ⊓ Q Rg b'
              let T := ⁅Z Rg b,Z Rg z⁆
              let K := centralizer (Y₀ : Set (FreeAmalgam Rg))
              let Zt := Z Rg (r.walk.getVert 3)
              Z Rg z ⊓ K = Zt ∧ F₀ ⊓ K = Zt ∧
                K.relIndex F₀ = 2 ∧ K.relIndex F₁ = 4 ∧
                Zt = T ⊔ (F₁ ⊓ Zt) ∧ (F₁ ⊓ Zt).relIndex Zt = 2 ∧ T ⊓ (F₁ ⊓ Zt) = ⊥
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              fixed a p (act Rg g⁻¹ a) ∧ fixed (act Rg g⁻¹ a) q a := by
  obtain ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,
    hsupp,hdis,_,hopp,_,_,_,hcard,hstrict,hbig,hescape,_,_⟩ :=
    plane_small_four_full_kernel_comparison h e hz hk u hR hb4 hsmall
  let F := Z Rg z ⊓ Q Rg a
  let F' := Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)
  let f := (MulAut.conj g).toMonoidHom
  have hZz : (Z Rg z).map f = Z Rg z := by
    simpa only [inv_inv,hfix] using (Z_act Rg g⁻¹ z).symm
  have hF : F.map f = F' := by
    rw [show F = Z Rg z ⊓ Q Rg a from rfl,
      Subgroup.map_inf _ _ f (MulAut.conj g).injective,hZz]
    simp only [F',Q_act,inv_inv,f]
  have hFF : (F.map f).map f = F :=
    map_conj_twice_of_square_centralizes F g
      (centralizer_le inf_le_left
        (plane_edge_square_centralizes_seed h e hz hk u hR p.end_color hzs g hg))
  have hsupp' : F ⊔ ⁅Z Rg (act Rg g⁻¹ a),Z Rg z⁆ = Z Rg z := by
    have hh := congrArg (Subgroup.map f) hsupp
    change (F' ⊔ ⁅Z Rg a,Z Rg z⁆).map f = (Z Rg z).map f at hh
    rw [Subgroup.map_sup,←hF,hFF,map_commutator,hZz] at hh
    simpa only [Z_act,inv_inv,f] using hh
  have hdis' : ⁅Z Rg (act Rg g⁻¹ a),Z Rg z⁆ ⊓ F = ⊥ := by
    have hh := congrArg (Subgroup.map f) hdis
    change (⁅Z Rg a,Z Rg z⁆ ⊓ F').map f = (⊥ : Subgroup (FreeAmalgam Rg)).map f at hh
    rw [Subgroup.map_inf _ _ f (MulAut.conj g).injective,←hF,hFF,
      map_commutator,hZz,Subgroup.map_bot] at hh
    simpa only [Z_act,inv_inv,f] using hh
  have hescape' : ¬ ⁅V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2),Z Rg z⁆ ≤
      Z Rg (act Rg g⁻¹ a) := by
    intro hh
    apply hescape
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
    rw [map_commutator,hZz,Subgroup.map_inf _ _ f (MulAut.conj g).injective]
    simpa only [hverts 2,V_act,Q_act,Z_act,inv_inv,f] using hh
  exact ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,hcard,hstrict,hbig,hopp,
    plane_radius_paired_fixed_seed h e hz hk u hR hb4 hsmall p hescape hsupp hdis,
    plane_radius_paired_fixed_seed h e hz hk u hR hb4 hsmall q hescape' hsupp' hdis'⟩

omit hk in
include h e hz in
/-- The whole-core reduction supplies both literal kernel/edge decompositions
on the same displaced paths, with the original projection and both covers. -/
theorem coreExhaustion_or_cubic_paired_fixed_seeds :
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
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            let fixed := fun b (r : CriticalPath Rg (sourceGeometry h) b z) b' =>
              let Y₀ := V Rg b ⊓ Q Rg (r.walk.getVert 2)
              let F₀ := Z Rg z ⊓ Q Rg b
              let F₁ := Z Rg z ⊓ Q Rg b'
              let T := ⁅Z Rg b,Z Rg z⁆
              let K := centralizer (Y₀ : Set (FreeAmalgam Rg))
              let Zt := Z Rg (r.walk.getVert 3)
              Z Rg z ⊓ K = Zt ∧ F₀ ⊓ K = Zt ∧
                K.relIndex F₀ = 2 ∧ K.relIndex F₁ = 4 ∧
                Zt = T ⊔ (F₁ ⊓ Zt) ∧ (F₁ ⊓ Zt).relIndex Zt = 2 ∧ T ⊓ (F₁ ⊓ Zt) = ⊥
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              fixed a p (act Rg g⁻¹ a) ∧ fixed (act Rg g⁻¹ a) q a)) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_paired_fixed_seeds h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application, retaining the original radical, odd extension
kernel quotient, full central attachments and both paired path calculations. -/
theorem rankTwo_or_cubic_paired_fixed_seeds :
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
            let H := ⁅Y,F⁆
            let C := ⁅Y,Z Rg z⁆
            let fixed := fun b (r : CriticalPath Rg (sourceGeometry h) b z) b' =>
              let Y₀ := V Rg b ⊓ Q Rg (r.walk.getVert 2)
              let F₀ := Z Rg z ⊓ Q Rg b
              let F₁ := Z Rg z ⊓ Q Rg b'
              let T := ⁅Z Rg b,Z Rg z⁆
              let K := centralizer (Y₀ : Set (FreeAmalgam Rg))
              let Zt := Z Rg (r.walk.getVert 3)
              Z Rg z ⊓ K = Zt ∧ F₀ ⊓ K = Zt ∧
                K.relIndex F₀ = 2 ∧ K.relIndex F₁ = 4 ∧
                Zt = T ⊔ (F₁ ⊓ Zt) ∧ (F₁ ⊓ Zt).relIndex Zt = 2 ∧ T ⊓ (F₁ ⊓ Zt) = ⊥
            Nat.card H = 2 ∧ H < C ∧ 4 ≤ Nat.card C ∧
              ⁅Y,Z Rg z ⊓ Q Rg (act Rg g⁻¹ a)⁆ = C ∧
              fixed a p (act Rg g⁻¹ a) ∧ fixed (act Rg g⁻¹ a) q a)) :=
  (coreExhaustion_or_cubic_paired_fixed_seeds h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
