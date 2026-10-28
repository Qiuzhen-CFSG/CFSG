module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelThompson
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair
import all CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardKernel
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistinctShifts
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalJointStabilizers
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.Source

/-!
# Whole neighboring-core movement and the original Borel distance bound

The common edge normalizes the neighboring two-core and moves the last
critical line. Two conjugate critical hyperplanes therefore generate the
whole seed. Their common fixed subgroup is the critical line times the full
edge seed. Conjugating the restricted-core commutator through this product
shows that the whole core movement is its join with the critical line.
Edge invariance is essential: an arbitrary subgroup of the proper mover
does not satisfy this decomposition.

The full endpoint omega group normalizes both terms of that join. The
common edge and endpoint seed generate the intermediate stabilizer, so the
whole core movement is invariant under that stabilizer. It lies in the
proper mover's fixed subgroup on the full moving cover, hence has order
dividing eight for both cover orders 16 and 32. The original A6 component,
using its prime five, fixes such a small invariant subgroup. This contradicts
the previously constructed escaping critical line.

Thus every original cubic Borel graph has distance four, including exclusion
of distance six. The original Sylow reduction retains only this distance-four
branch before CoreExhaustion and full exceptional reconstruction. The literal
c.L,d.S consumer is OriginalSylowExceptional. Both full central attachments
and the cubic kernel E with its odd quotient E/Q are retained.

The natural-branch import supplies only the group-theoretic two-hyperplane
lemma; no replacement graph or identification of its radical is used.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.9)--(5.11), printed pp.921--924; Aschbacher--Smith C.1.31--32,
printed pp.135--136. The prime-five argument specializes the terminal step
to the actual binary six-letter covers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk


private theorem conjugate_kernel_movement {F : Type*} [Group F]
    (V K A B D C : Subgroup F) [IsMulCommutative V]
    (x : F) (hK : K ≤ V) (hBA : B ≤ A)
    (hAV : A ≤ normalizer (V : Set F))
    (hxV : x ∈ normalizer (V : Set F))
    (hxA : x ∈ normalizer (A : Set F))
    (hgen : K ⊔ K.map (MulAut.conj x).toMonoidHom = V)
    (hKB : K ≤ centralizer (B : Set F))
    (hD : D = ⁅V,B⁆) (hDC : D ⊔ C ≤ V)
    (hCx : x ∈ centralizer (C : Set F))
    (hbound : ⁅V,A⁆ ≤ D ⊔ C) :
    ⁅V,A⁆ = D ⊔ ⁅K,A⁆ := by
  let f := (MulAut.conj x).toMonoidHom
  let K' := K.map f
  let B' := B.map f
  let E := ⁅K,A⁆
  let N := D ⊔ E
  have hV : V.map f = V := mem_normalizer_iff_map_conj_eq.mp hxV
  have hA : A.map f = A := mem_normalizer_iff_map_conj_eq.mp hxA
  have hEV : E ≤ V := (commutator_mono hK le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hAV)
  have hNV : N ≤ V := sup_le (le_sup_left.trans hDC) hEV
  have hVN : V ≤ normalizer (N : Set F) :=
    ((le_centralizer V).trans (centralizer_le hNV)).trans (Subgroup.centralizer_le_normalizer _)
  have hVE : V ≤ normalizer (E : Set F) :=
    ((le_centralizer V).trans (centralizer_le hEV)).trans (Subgroup.centralizer_le_normalizer _)
  have hK' : K' ≤ V := (map_mono hK).trans_eq hV
  have hB' : B' ≤ A := (map_mono hBA).trans_eq hA
  have hzero : ⁅K',B'⁆ = ⊥ := by
    rw [show K' = K.map f from rfl,show B' = B.map f from rfl,←map_commutator,
      commutator_eq_bot_iff_le_centralizer.mpr hKB,Subgroup.map_bot]
  have hD' : D.map f ≤ E := by
    rw [hD,map_commutator,hV]
    rw [←hgen]
    exact commutator_sup_le_of_relative_normal V K K' B' E hVE hK hK'
      (commutator_mono le_rfl hB') (hzero.le.trans bot_le)
  have hCN : C ≤ normalizer (D : Set F) :=
    (((show C ≤ V from le_sup_right.trans hDC).trans ((le_centralizer V).trans
      (centralizer_le (show D ≤ V from le_sup_left.trans hDC)))).trans
        (Subgroup.centralizer_le_normalizer _))
  have hEmap : E.map f ≤ N := by
    rintro _ ⟨y,hy,rfl⟩
    have hyDC : y ∈ (D : Set F) * (C : Set F) := by
      rw [←coe_mul_of_right_le_normalizer_left D C hCN]
      exact hbound (commutator_mono hK le_rfl hy)
    obtain ⟨d,hd,c,hc,he⟩ := hyDC
    have hfc : f c = c := by
      change x*c*x⁻¹=c
      rw [←hCx c hc,mul_inv_cancel_right]
    have hfe : f y = f d * d⁻¹ * y := by
      rw [←he,map_mul,hfc]
      group
    rw [hfe]
    exact N.mul_mem (N.mul_mem (mem_sup_right (hD' (mem_map_of_mem f hd)))
      (mem_sup_left (D.inv_mem hd))) (mem_sup_right hy)
  apply le_antisymm
  · rw [←hgen]
    apply commutator_sup_le_of_relative_normal V K K' A N hVN hK hK'
      le_sup_right
    have hm : ⁅K',A⁆ = E.map f := by rw [show E = ⁅K,A⁆ from rfl,map_commutator,hA]
    exact hm.trans_le hEmap
  · exact sup_le (hD ▸ commutator_mono le_rfl hBA) (commutator_mono hK le_rfl)


include h e hz hk in
/-- Edge invariance and movement of the critical line recover the entire
neighboring-core commutator from the restricted kernel and that line. -/
theorem borel_three_shift_whole_core_decomposition
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let v := r.path.walk.getVert (r.path.walk.length-2)
    ⁅Z Rg t.start,Q Rg r.start⁆ = ⁅Z Rg t.start,Z Rg v⁆ ⊔
      ⁅Z Rg t.start ⊓ Q Rg v,Q Rg r.start⁆ := by
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let V := Z Rg t.start
  let K := V ⊓ Q Rg v
  let A := Q Rg r.start
  let T := Q Rg t.edge
  let J := edgeOffenderJoin t.start t.edge
  let D := ⁅V,Z Rg v⁆
  let C := Z Rg t.edge
  have ht := two_borel_backward_shifts_small_moving h e hz hk hb q.path r t
  have hs : (Q Rg v).relIndex V < 4 := by rw [ht.2.1]; decide
  have hcommon := borel_moving_common_kernel h e hz hk u hR t.path hs ht.2.2.2.2
  dsimp only at hcommon
  rw [t.first] at hcommon
  have hmove : ¬ T ≤ centralizer (D : Set (FreeAmalgam Rg)) := by
    simpa only [t.first] using ht.2.2.2.2
  have hcol : color Rg t.edge = true := by
    have hh := adjacent_color_ne Rg t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color Rg t.edge <;> simp_all
  have hTG : T ≤ stabilizer Rg t.start := fun _ hx => hx.2 _ (adjacent_symm Rg t.adjacent_shift)
  have hTr : T ≤ stabilizer Rg r.start := fun _ hx => hx.2 _ (adjacent_symm Rg t.adjacent_start)
  have hTV : T ≤ normalizer (V : Set (FreeAmalgam Rg)) := hTG.trans (Z_normalized Rg t.start)
  have hTA : T ≤ normalizer (A : Set (FreeAmalgam Rg)) := hTr.trans (Q_normalized Rg r.start)
  have hAJ : A ≤ J := (borel_three_shift_endpoint_normalization h e hz hk hb u hR p q r t).2
  obtain ⟨J₀,_,hJ₀,_,hJT,_⟩ := borel_edge_maximal_offenders h e hz hk u hR
    t.path.start_color t.adjacent_shift
  have hAT : A ≤ T := (hAJ.trans hJ₀.le).trans hJT
  have hAV := hAT.trans hTV
  have hvA : Z Rg v ≤ A := by
    apply Z_le_Q_of_dist_lt Rg v ((sourceGeometry h).exists_critical v t.path.end_color)
    rw [SimpleGraph.dist_comm,r.path.dist_start (Nat.sub_le _ _),
      (sourceGeometry h).distance_constant _ t.path.end_color]
    have hl : r.path.walk.length = sourceDistance h := r.path.length_eq_b
    change r.path.walk.length-2 < sourceDistance h
    omega
  obtain ⟨x,hx,hxmove⟩ := SetLike.not_le_iff_exists.mp hmove
  have hxn : x ∉ normalizer (K : Set (FreeAmalgam Rg)) := by
    intro hn
    have hh : x ∈ stabilizer Rg t.start ⊓ normalizer (K : Set (FreeAmalgam Rg)) := ⟨hTG hx,hn⟩
    rw [small_critical_kernel_normalizer_eq_line_centralizer h e hz hk t.path hs] at hh
    exact hxmove hh.2
  let f := (MulAut.conj x).toMonoidHom
  have hV : V.map f = V := mem_normalizer_iff_map_conj_eq.mp (hTV hx)
  have hKi : K.relIndex V = 2 := by
    rw [show K = V ⊓ Q Rg v from rfl,inf_relIndex_left]
    exact ht.2.1
  let := finite_Z Rg t.start
  have hgen : K ⊔ K.map f = V :=
    (Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair.two_hyperplanes V K (K.map f)
      inf_le_left ((map_mono (show K ≤ V from inf_le_left)).trans_eq hV) hKi
      (by rw [←hV,relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]; exact hKi)
      (fun he => hxn (mem_normalizer_iff_map_conj_eq.mpr he.symm))).1
  have hKB : K ≤ centralizer (Z Rg v : Set (FreeAmalgam Rg)) :=
    (critical_seed_centralizer_intersection h e t.path).symm.le.trans inf_le_right
  have hDC : D ⊔ C ≤ V := sup_le (critical_seed_commutator_le h t.path)
    (adjacent_Z_le Rg t.path.start_color t.adjacent_shift)
  have hCT : C ≤ centralizer (T : Set (FreeAmalgam Rg)) := terminal_edge_seed_central hcol
  have hbound : ⁅V,A⁆ ≤ D ⊔ C :=
    ((commutator_mono le_rfl (borel_three_shift_endpoint_normalization h e hz hk hb u hR p q r t).2).trans
      hcommon.2.2.2.2.2.2).trans_eq hcommon.2.2.2.1
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) t.start t.path.start_color
  exact conjugate_kernel_movement V K A (Z Rg v) D C x inf_le_left hvA hAV
    (hTV hx) (hTA hx) hgen hKB rfl hDC (le_centralizer_iff.mp hCT hx) hbound

include h e hz hk in
/-- The full endpoint omega group normalizes the whole neighboring-core
commutator, using the full critical line and the actual restricted kernel. -/
theorem borel_three_shift_whole_core_omega_normalization
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    X Rg (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      ((⁅Z Rg t.start,Q Rg r.start⁆ : Subgroup (FreeAmalgam Rg)) : Set _) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let D := ⁅Z Rg t.start,Z Rg v⁆
  have hDv : D ≤ Z Rg v := by
    rw [show D = ⁅Z Rg t.start,Z Rg v⁆ from rfl,commutator_comm]
    exact critical_seed_commutator_le h (CriticalPath.ofPair t.path.end_color (reverse_pair h e t.path))
  have hvz : (cosetGraph Rg).dist v z = 2 := by
    rw [show v = r.path.walk.getVert (r.path.walk.length-2) from rfl,r.path.dist_end]
    have hl : r.path.walk.length = sourceDistance h := r.path.length_eq_b
    omega
  have hvQ : Z Rg v ≤ Q Rg z := by
    apply Z_le_Q_of_dist_lt Rg v ((sourceGeometry h).exists_critical v t.path.end_color)
    rw [hvz,(sourceGeometry h).distance_constant _ t.path.end_color]
    change 2 < sourceDistance h
    omega
  have hDX : D ≤ centralizer (X Rg z : Set (FreeAmalgam Rg)) :=
    (hDv.trans hvQ).trans (Q_le_centralizer_X Rg z)
  rw [borel_three_shift_whole_core_decomposition h e hz hk hb u hR p q r t]
  exact (le_inf ((le_centralizer_iff.mp hDX).trans (Subgroup.centralizer_le_normalizer _))
    (borel_three_shift_restricted_core_movement h e hz hk hb u hR p q r t).2.2).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

include h e hz hk in
/-- The whole neighboring-core movement has order dividing eight on either
full cover, using its containment in the proper mover's fixed subgroup. -/
theorem borel_three_shift_whole_core_card_dvd
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    Nat.card (⁅Z Rg t.start,Q Rg r.start⁆ : Subgroup (FreeAmalgam Rg)) ∣ 8 := by
  let H := ⁅Z Rg t.start,Q Rg r.start⁆
  let J := edgeOffenderJoin t.start t.edge
  let F := U Rg t.start ⊓ centralizer (J : Set (FreeAmalgam Rg))
  have ht := two_borel_backward_shifts_small_moving h e hz hk hb q.path r t
  have hs : (Q Rg (r.path.walk.getVert (r.path.walk.length-2))).relIndex (Z Rg t.start) < 4 := by
    rw [ht.2.1]; decide
  have hcommon := borel_moving_common_kernel h e hz hk u hR t.path hs ht.2.2.2.2
  dsimp only at hcommon
  rw [t.first] at hcommon
  have hHU := (borel_three_shift_core_movement h e hz hk hb u hR p q r t).2.1.trans inf_le_right
  have hHF : H ≤ F := le_inf hHU
    (((commutator_mono le_rfl (borel_three_shift_endpoint_normalization h e hz hk hb u hR p q r t).2).trans
      hcommon.2.2.2.2.2.2).trans (le_centralizer_iff.mp hcommon.2.2.2.2.2.1))
  obtain ⟨J₀,_,hJ₀,_,_,_,_,hfix,_⟩ := borel_edge_maximal_offenders h e hz hk u hR
    t.path.start_color t.adjacent_shift
  have hindex : F.relIndex (U Rg t.start) = 4 := by
    rw [show F = U Rg t.start ⊓ centralizer (J : Set (FreeAmalgam Rg)) from rfl,inf_relIndex_left]
    simpa only [J,hJ₀] using hfix
  have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam Rg)) F (U Rg t.start) bot_le inf_le_left
  simp only [relIndex_bot_left,hindex] at hm
  have hcard : Nat.card F ∣ 8 := by
    rcases graph_U_card h e hz hk t.start t.path.start_color with hc | hc
    · have he : Nat.card F = 4 := by omega
      rw [he]; decide
    · have he : Nat.card F = 8 := by omega
      rw [he]
  let := finite_Z Rg t.start
  let : Finite F := Finite.of_injective
    (inclusion (inf_le_left.trans (DistanceEight.U_le_Z Rg t.start))) (inclusion_injective _)
  exact (card_dvd_of_le hHF).trans hcard

include h e hz hk in
/-- The original component fixes every invariant two-core subgroup whose
order divides eight. This uses the genuine A6 quotient and its prime five. -/
theorem small_invariant_core_le_fixed
    {a : Vertex Rg} (ha : color Rg a = false)
    (D : Subgroup (FreeAmalgam Rg)) (hDQ : D ≤ Q Rg a)
    (hDN : stabilizer Rg a ≤ normalizer (D : Set (FreeAmalgam Rg)))
    (hsmall : Nat.card D ∣ 8) : D ≤ fixedCore Rg a := by
  obtain ⟨i,hi,hir,hiQ,_⟩ := graph_cover h e hz hk a ha
  let D₀ := D.comap i
  have hDG : D ≤ stabilizer Rg a := hDQ.trans (fun _ hx => hx.1)
  have hDm : D₀.map i = D := map_comap_eq_self (hDG.trans_eq hir.symm)
  have hg (m : (L ⊔ R : Subgroup G)) : i m ∈ stabilizer Rg a := hir ▸ ⟨m,rfl⟩
  let : D₀.Normal := ⟨by
    intro x hx m
    change i (m*x*m⁻¹) ∈ D
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hDN (hg m)) (i x)).mp hx⟩
  have hs : (⊥ : Subgroup (L ⊔ R : Subgroup G)).relIndex D₀ ∣ 8 := by
    rw [relIndex_bot_left,←card_map_of_injective hi,hDm]
    exact hsmall
  have hm := map_mono (f := i) (small_normal_section_commutator h e hz hk D₀ ⊥ hs)
  let j : (L ⊔ R : Subgroup G) →* stabilizer Rg a := i.codRestrict _ hg
  have hjs : Function.Surjective j := by
    intro x
    have hx : (x : FreeAmalgam Rg) ∈ i.range := hir.symm ▸ x.property
    obtain ⟨m,hm⟩ := hx
    exact ⟨m,Subtype.ext hm⟩
  have hj : (stabilizer Rg a).subtype.comp j = i := rfl
  have hLm : (L.subgroupOf (L ⊔ R)).map i = Ltilde Rg a := by
    rw [←h.relative_residual,←hj,←map_map,map_pResidual_of_surjective 2 j hjs]
    rfl
  rw [map_commutator,hDm,hLm,Subgroup.map_bot] at hm
  exact le_inf hDQ (commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hm))

include h e hz hk in
/-- The original Borel configuration cannot have distance greater than four.
Whole-core normalization and the full-cover bound force residual fixedness,
contradicting the last escaping critical line. -/
theorem borel_distance_le_four
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    sourceDistance h ≤ 4 := by
  by_contra! hb
  obtain ⟨z,p,_⟩ := borel_small_critical_at h e hz hk hb u hR (alpha Rg) rfl
  obtain ⟨q,_⟩ := borel_backwardShift h e hz hk hb u hR p
  obtain ⟨r,_⟩ := borel_backwardShift h e hz hk hb u hR q.path
  obtain ⟨t,_⟩ := borel_backwardShift h e hz hk hb u hR r.path
  let H := ⁅Z Rg t.start,Q Rg r.start⁆
  have hm := borel_three_shift_core_movement h e hz hk hb u hR p q r t
  have hZX : Z Rg (q.path.walk.getVert (q.path.walk.length-2)) ≤
      X Rg (q.path.walk.getVert (q.path.walk.length-2)) :=
    (sourceGeometry h).omega_bound _ r.path.end_color (by
      rw [(sourceGeometry h).distance_constant _ r.path.end_color]
      exact sourceDistance_pos h)
  have hnormal : stabilizer Rg r.start ≤ normalizer (H : Set (FreeAmalgam Rg)) := by
    rw [←t.generation]
    exact sup_le hm.2.2.1 (hZX.trans
      (borel_three_shift_whole_core_omega_normalization h e hz hk hb u hR p q r t))
  exact hm.2.2.2.2.2 (small_invariant_core_le_fixed h e hz hk r.path.start_color H
    (hm.2.1.trans inf_le_left |>.trans (omegaCenter_le _)) hnormal
    (borel_three_shift_whole_core_card_dvd h e hz hk hb u hR p q r t))

include h e hz hk in
/-- The surviving original cubic Borel graph has critical distance four;
this includes exclusion of distance six with both full covers retained. -/
theorem borel_distance_eq_four
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    sourceDistance h = 4 := by
  have hle := borel_distance_le_four h e hz hk u hR
  have hgt := distance_gt_two h e hz hk
  have he := sourceDistance_even h
  rw [Nat.even_iff] at he
  omega

omit hk in
/-- Original Sylow removes the plane branch, and the whole neighboring-core
argument removes every Borel distance above four. Distance four remains a
source obligation before the full intrinsic core can be reconstructed. -/
theorem coreExhaustion_or_borel_distance_four
    (hSyl : Chapter1.IsSylowIn 2 R (L ⊔ R)) :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      sourceDistance h = 4 ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_borel_generating_edges h hSyl e hz with
    hx | ⟨hk,hs,_,hcovers,u,hR,_⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,borel_distance_eq_four h e hz hk u hR,hcovers,u,hR⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
