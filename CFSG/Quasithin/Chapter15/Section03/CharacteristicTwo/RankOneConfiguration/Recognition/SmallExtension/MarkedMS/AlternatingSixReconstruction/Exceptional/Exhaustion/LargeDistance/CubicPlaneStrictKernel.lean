module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedSlice
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPredecessorSlice

/-!
# Residual displacement of strict predecessor kernels

For a small critical path a--z, let c be its second predecessor and t its
last edge. A strict Baumann slice on the full endpoint seed has index four
and is exactly Z_t. The reverse kernel F = Z_z intersect Q_a contains Z_t
and has index two in Z_z. Consequently its own slice and its intersection
with Z_c are both exactly Z_t, and F Z_c/Z_c has order two.

The residual at c cannot normalize F Z_c. Any such normalization fixes the
two-element quotient, putting F in the Baumann slice, contrary to its exact
slice index two. Choose a residual conjugate that escapes F Z_c. The two
kernel-seed joins intersect exactly in Z_c and generate a subgroup of index
four over Z_c. The calculation uses [V_c,Q_c] <= Z_c to normalize the joins;
it does not replace the full reverse kernel by its moving subgroup.

On the original selected and displaced critical paths, either all shifted
kernel comparisons hold on both paths, or both paths have these residual
witnesses and exact four-element sections. The opposite-edge conjugator,
cross-distances, order-two radius line and larger full endpoint commutator
are retained. The whole-core and literal C.1.32 applications keep both covers,
the original radical, and projection kernel E with nontrivial odd E/Q.

This identifies the actual residual movement remaining in the strict branch;
it does not exclude it. The terminal comparison, other image/distance cases,
both core exhaustions and unconditional reconstruction remain necessary.
The internal import reuses the existing relative-index transport lemma
without changing its public boundary.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the shifted-kernel and slice comparisons in (5.12)(1),(3), printed
pp.924--927; Aschbacher--Smith C.1.31--32, printed pp.135--136.
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
/-- A strict full-seed slice cuts the reverse kernel in the last edge seed.
The kernel-seed join has index two and is not normalized by the residual. -/
theorem plane_strict_predecessor_kernel_slice
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hs : 2 < (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z)) :
    let c := p.walk.getVert (p.walk.length-2)
    let t := p.walk.getVert (p.walk.length-1)
    let F := Z Rg z ⊓ Q Rg a
    F ⊓ B Rg c ((sourceGeometry h).Z_normal _) = Z Rg t ∧
      F ⊓ Z Rg c = Z Rg t ∧
      (B Rg c ((sourceGeometry h).Z_normal _)).relIndex F = 2 ∧
      (Z Rg c).relIndex (F ⊔ Z Rg c) = 2 ∧
      ¬ Ltilde Rg c ≤ normalizer ((F ⊔ Z Rg c : Subgroup (FreeAmalgam Rg)) :
        Set (FreeAmalgam Rg)) := by
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
  have hAt : Z Rg a ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-1 < sourceDistance h
    omega
  have hfixed : F = Z Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (critical_seed_centralizer_intersection h e
      (CriticalPath.ofPair p.end_color (critical_reverse Rg (sourceGeometry h)
        (sourceEdgeCentralizer h e) a p.start_color
        (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
        z p.end_color p.critical))).symm
  have htF : Z Rg t ≤ F := by
    rw [hfixed]
    refine le_inf (adjacent_Z_le Rg p.end_color hzt) ?_
    intro x hx y hy
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2 y (hAt hy)
  obtain ⟨hB,hZ,_,_⟩ := plane_strict_slice_eq_edge h e hz hk u hR hc p.end_color hct hzt hs
  have hFB : F ⊓ B Rg c ((sourceGeometry h).Z_normal _) = Z Rg t :=
    le_antisymm ((inf_le_inf_right _ (show F ≤ Z Rg z from inf_le_left)).trans_eq hB)
      (le_inf htF ((adjacent_Z_le Rg hc hct).trans (Escape.EdgeTransfer.Z_le_B hb c hc)))
  have hFZ : F ⊓ Z Rg c = Z Rg t :=
    le_antisymm ((inf_le_inf_right _ (show F ≤ Z Rg z from inf_le_left)).trans_eq hZ)
      (le_inf htF (adjacent_Z_le Rg hc hct))
  have hindex : F.relIndex (Z Rg z) = 2 := by
    rw [show F = Z Rg z ⊓ Q Rg a from rfl,inf_relIndex_left]
    exact (small_critical_indices h e hz hk p hp).2
  have htindex : (Z Rg t).relIndex F = 2 := by
    have hh := relIndex_mul_relIndex (Z Rg t) F (Z Rg z) htF inf_le_left
    rw [hindex,(plane_edge_full_seed_fixer h e hz hk u hR p.end_color hzt).2.1] at hh
    omega
  have hBF : (B Rg c ((sourceGeometry h).Z_normal _)).relIndex F = 2 := by
    rw [←inf_relIndex_left F,hFB]
    exact htindex
  have hZF : (Z Rg c).relIndex F = 2 := by
    rw [←inf_relIndex_left F,hFZ]
    exact htindex
  have hFQ : F ≤ Q Rg c := by
    apply inf_le_left.trans
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-(p.walk.length-2) < sourceDistance h
    omega
  have hFN : F ≤ normalizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    (hFQ.trans (fun _ hx => hx.1)).trans (Z_normalized Rg c)
  have hjoin : (Z Rg c).relIndex (F ⊔ Z Rg c) = 2 := by
    rw [sup_comm F (Z Rg c),relIndex_sup_of_normalized _ _ hFN]
    exact hZF
  refine ⟨hFB,hFZ,hBF,hjoin,?_⟩
  intro hn
  have hcomm : ⁅F,Ltilde Rg c⁆ ≤ Z Rg c :=
    (commutator_mono le_sup_left le_rfl).trans
      (commutator_le_of_normalized_index_two (F ⊔ Z Rg c) (Z Rg c) (Ltilde Rg c)
        le_sup_right hjoin hn ((Ltilde_le_stabilizer c).trans (Z_normalized Rg c)))
  have hFV : F ≤ V Rg c := by
    apply inf_le_left.trans
    have hd : (cosetGraph Rg).dist z c ≤ 2 := by
      rw [SimpleGraph.dist_comm,p.dist_end]
      omega
    exact le_iSup_of_le z (le_iSup_of_le hd le_rfl)
  have hVG := ((sourceGeometry h).V_le_Q hb c hc).trans
    (show Q Rg c ≤ stabilizer Rg c from fun _ hx => hx.1)
  have hle : F ≤ B Rg c ((sourceGeometry h).Z_normal _) := by
    intro f hf
    apply (mem_B_iff Rg c _ hVG f).mpr
    refine ⟨hFV hf,fun l hl => ?_⟩
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator hl hf)
  have hone := relIndex_eq_one.mpr hle
  omega

include h e hz hk in
/-- The same full reverse kernel has a residual conjugate whose seed join
meets the original join exactly in the midpoint seed and spans index four. -/
theorem plane_strict_predecessor_kernel_displacement
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hs : 2 < (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z)) :
    let c := p.walk.getVert (p.walk.length-2)
    let F := Z Rg z ⊓ Q Rg a
    ∃ k ∈ Ltilde Rg c, act Rg k⁻¹ c = c ∧
      ¬ F.map (MulAut.conj k).toMonoidHom ≤ F ⊔ Z Rg c ∧
      (F ⊔ Z Rg c) ⊓ (F.map (MulAut.conj k).toMonoidHom ⊔ Z Rg c) = Z Rg c ∧
      (Z Rg c).relIndex ((F ⊔ Z Rg c) ⊔
        (F.map (MulAut.conj k).toMonoidHom ⊔ Z Rg c)) = 4 := by
  let c := p.walk.getVert (p.walk.length-2)
  let F := Z Rg z ⊓ Q Rg a
  let A := F ⊔ Z Rg c
  have hb := distance_gt_two h e hz hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color Rg c = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  obtain ⟨_,_,_,hAi,hn⟩ := plane_strict_predecessor_kernel_slice h e hz hk u hR p hp hs
  change (Z Rg c).relIndex A = 2 at hAi
  change ¬ Ltilde Rg c ≤ normalizer (A : Set (FreeAmalgam Rg)) at hn
  have hFV : F ≤ V Rg c := by
    apply inf_le_left.trans
    have hd : (cosetGraph Rg).dist z c ≤ 2 := by
      rw [SimpleGraph.dist_comm,p.dist_end]
      omega
    exact le_iSup_of_le z (le_iSup_of_le hd le_rfl)
  have hAV : A ≤ V Rg c := sup_le hFV (Z_le_VBall Rg _ 2)
  have hAQ : A ≤ Q Rg c := hAV.trans ((sourceGeometry h).V_le_Q hb c hc)
  let := finite_stabilizer Rg c
  let : Finite A := Finite.of_injective
    (inclusion (hAQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hex : ∃ k ∈ Ltilde Rg c, ¬ F.map (MulAut.conj k).toMonoidHom ≤ A := by
    by_contra! hm
    apply hn
    intro k hk
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hZ : (Z Rg c).map (MulAut.conj k).toMonoidHom = Z Rg c :=
      mem_normalizer_iff_map_conj_eq.mp ((Z_normalized Rg c) (Ltilde_le_stabilizer c hk))
    have hle : A.map (MulAut.conj k).toMonoidHom ≤ A := by
      rw [show A = F ⊔ Z Rg c from rfl,Subgroup.map_sup,hZ]
      exact sup_le (hm k hk) le_sup_right
    exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj k).injective])
  obtain ⟨k,hkm,hescape⟩ := hex
  have hfix : act Rg k⁻¹ c = c := Ltilde_le_stabilizer c ((Ltilde Rg c).inv_mem hkm)
  have hZ : (Z Rg c).map (MulAut.conj k).toMonoidHom = Z Rg c :=
    mem_normalizer_iff_map_conj_eq.mp ((Z_normalized Rg c) (Ltilde_le_stabilizer c hkm))
  let A' := F.map (MulAut.conj k).toMonoidHom ⊔ Z Rg c
  have hmap : A.map (MulAut.conj k).toMonoidHom = A' := by
    rw [show A = F ⊔ Z Rg c from rfl,Subgroup.map_sup,hZ]
  have hA'i : (Z Rg c).relIndex A' = 2 := by
    rw [←hmap,←hZ,relIndex_map_map_of_injective _ _ (MulAut.conj k).injective]
    exact hAi
  have hA'V : A' ≤ V Rg c := by
    rw [←hmap]
    exact (map_mono hAV).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp ((DistanceEight.V_normalized Rg c) (Ltilde_le_stabilizer c hkm)))
  let : Finite A' := Finite.of_injective
    (inclusion ((hA'V.trans ((sourceGeometry h).V_le_Q hb c hc)).trans
      (fun _ hx => hx.1))) (inclusion_injective _)
  have hZA : Z Rg c ≤ A := le_sup_right
  have hZA' : Z Rg c ≤ A' := le_sup_right
  have hnot : ¬ A' ≤ A := fun hh => hescape (le_sup_left.trans hh)
  have hI : A ⊓ A' = Z Rg c := by
    have hZI : Z Rg c ≤ A ⊓ A' := le_inf hZA hZA'
    have hprod := relIndex_mul_relIndex (Z Rg c) (A ⊓ A') A' hZI inf_le_right
    rw [hA'i] at hprod
    have hpos : 0 < (A ⊓ A').relIndex A' := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hne : (A ⊓ A').relIndex A' ≠ 1 := by
      intro hi
      exact hnot ((relIndex_eq_one.mp hi).trans inf_le_left)
    have hi : (Z Rg c).relIndex (A ⊓ A') = 1 := by
      have hlo : 2 ≤ (A ⊓ A').relIndex A' := by omega
      have hle : (Z Rg c).relIndex (A ⊓ A') ≤ 1 := by nlinarith
      have hn : (Z Rg c).relIndex (A ⊓ A') ≠ 0 := by
        intro he
        rw [he,zero_mul] at hprod
        contradiction
      omega
    exact le_antisymm (relIndex_eq_one.mp hi) hZI
  have hAA' : A' ≤ normalizer (A : Set (FreeAmalgam Rg)) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono hAV (hA'V.trans ((sourceGeometry h).V_le_Q hb c hc))).trans
      (plane_radius_core_commutator h e hz hk u hR hc)).trans hZA
  have hjoin : (Z Rg c).relIndex (A ⊔ A') = 4 := by
    have hh := relIndex_mul_relIndex (Z Rg c) A (A ⊔ A') hZA le_sup_left
    have hi : A.relIndex (A ⊔ A') = 2 := by
      rw [relIndex_sup_of_normalized _ _ hAA',←inf_relIndex_left A',inf_comm A' A,hI]
      exact hA'i
    rw [hAi,hi] at hh
    omega
  exact ⟨k,hkm,hfix,hescape,hI,hjoin⟩

include h e hz hk in
/-- Both original displaced paths satisfy all shifted comparisons, or each
has an actual midpoint-residual displacement of its reverse-kernel section.
Each pair of sections intersects in the midpoint seed and spans index four. -/
theorem plane_small_four_shifted_kernel_displacement
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
                ¬ F.map (MulAut.conj k).toMonoidHom ≤ N₀ ∧
                N₀ ⊓
                    (F.map (MulAut.conj k).toMonoidHom ⊔ Z Rg c₀) = Z Rg c₀ ∧
                (Z Rg c₀).relIndex (N₀ ⊔
                  (F.map (MulAut.conj k).toMonoidHom ⊔ Z Rg c₀)) = 4) ∧
                (∃ l ∈ Ltilde Rg c₁, act Rg l⁻¹ c₁ = c₁ ∧
                ¬ F₁.map (MulAut.conj l).toMonoidHom ≤ N₁ ∧
                N₁ ⊓
                    (F₁.map (MulAut.conj l).toMonoidHom ⊔ Z Rg c₁) = Z Rg c₁ ∧
                (Z Rg c₁).relIndex (N₁ ⊔
                  (F₁.map (MulAut.conj l).toMonoidHom ⊔ Z Rg c₁)) = 4)) ∨
                ((∀ d (r : CriticalPath Rg (sourceGeometry h) d (c₀)),
                    r.walk.getVert 2 = a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg (c₀) →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,F⁆ ⊔ T) ∧
                  (∀ d (r : CriticalPath Rg (sourceGeometry h) d (c₁)),
                    r.walk.getVert 2 = act Rg g⁻¹ a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg (c₁) →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,F₁⁆ ⊔
                        ⁅Z Rg (act Rg g⁻¹ a),Z Rg z⁆))) := by
  obtain ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,hcard,hstrict,hbig,hopp,halt⟩ :=
    plane_small_four_shifted_slice_comparison h e hz hk u hR hb4 hsmall
  refine ⟨a,z,p,s,hzs,hgen,g,hg,hfix,q,hverts,hgeom,hcard,hstrict,hbig,hopp,?_⟩
  rcases halt with hs | hcomp
  · have displace {v : Vertex Rg} (r : CriticalPath Rg (sourceGeometry h) v z)
        (hr : 2 < (B Rg (r.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg z)) := by
      have hrl : r.walk.length = 4 := r.length_eq_b.trans hb4
      have hs' : 2 < (B Rg (r.walk.getVert (r.walk.length-2))
          ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) := by
        simpa only [hrl,Nat.reduceSub] using hr
      have hh := plane_strict_predecessor_kernel_displacement h e hz hk u hR r (hsmall _ _ r) hs'
      simp only [hrl,Nat.reduceSub] at hh
      exact hh
    have hb := distance_gt_two h e hz hk
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
    exact Or.inl ⟨displace p hs,displace q hs'⟩
  · exact Or.inr hcomp


omit hk in
include h e hz in
/-- Whole-core application preserving the same original pair, both covers,
and the exact kernel sections in the remaining strict branch. -/
theorem coreExhaustion_or_cubic_shifted_kernel_displacement :
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
                ¬ F.map (MulAut.conj k).toMonoidHom ≤ N₀ ∧
                N₀ ⊓
                    (F.map (MulAut.conj k).toMonoidHom ⊔ Z Rg c₀) = Z Rg c₀ ∧
                (Z Rg c₀).relIndex (N₀ ⊔
                  (F.map (MulAut.conj k).toMonoidHom ⊔ Z Rg c₀)) = 4) ∧
                (∃ l ∈ Ltilde Rg c₁, act Rg l⁻¹ c₁ = c₁ ∧
                ¬ F₁.map (MulAut.conj l).toMonoidHom ≤ N₁ ∧
                N₁ ⊓
                    (F₁.map (MulAut.conj l).toMonoidHom ⊔ Z Rg c₁) = Z Rg c₁ ∧
                (Z Rg c₁).relIndex (N₁ ⊔
                  (F₁.map (MulAut.conj l).toMonoidHom ⊔ Z Rg c₁)) = 4)) ∨
                ((∀ d (r : CriticalPath Rg (sourceGeometry h) d (c₀)),
                    r.walk.getVert 2 = a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg (c₀) →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,F⁆ ⊔ T) ∧
                  (∀ d (r : CriticalPath Rg (sourceGeometry h) d (c₁)),
                    r.walk.getVert 2 = act Rg g⁻¹ a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg (c₁) →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,F₁⁆ ⊔
                        ⁅Z Rg (act Rg g⁻¹ a),Z Rg z⁆))))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_shifted_kernel_displacement h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application through the actual cubic projection, retaining
the original radical and the nontrivial odd quotient of its extension kernel. -/
theorem rankTwo_or_cubic_shifted_kernel_displacement :
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
                ¬ F.map (MulAut.conj k).toMonoidHom ≤ N₀ ∧
                N₀ ⊓
                    (F.map (MulAut.conj k).toMonoidHom ⊔ Z Rg c₀) = Z Rg c₀ ∧
                (Z Rg c₀).relIndex (N₀ ⊔
                  (F.map (MulAut.conj k).toMonoidHom ⊔ Z Rg c₀)) = 4) ∧
                (∃ l ∈ Ltilde Rg c₁, act Rg l⁻¹ c₁ = c₁ ∧
                ¬ F₁.map (MulAut.conj l).toMonoidHom ≤ N₁ ∧
                N₁ ⊓
                    (F₁.map (MulAut.conj l).toMonoidHom ⊔ Z Rg c₁) = Z Rg c₁ ∧
                (Z Rg c₁).relIndex (N₁ ⊔
                  (F₁.map (MulAut.conj l).toMonoidHom ⊔ Z Rg c₁)) = 4)) ∨
                ((∀ d (r : CriticalPath Rg (sourceGeometry h) d (c₀)),
                    r.walk.getVert 2 = a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg (c₀) →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,F⁆ ⊔ T) ∧
                  (∀ d (r : CriticalPath Rg (sourceGeometry h) d (c₁)),
                    r.walk.getVert 2 = act Rg g⁻¹ a →
                    ∀ K : Subgroup (FreeAmalgam Rg),
                      K ≤ Z Rg d ⊓ Q Rg (c₁) →
                      ⁅K,Z Rg z⁆ ≤ ⁅K,F₁⁆ ⊔
                        ⁅Z Rg (act Rg g⁻¹ a),Z Rg z⁆))))) :=
  (coreExhaustion_or_cubic_shifted_kernel_displacement h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
