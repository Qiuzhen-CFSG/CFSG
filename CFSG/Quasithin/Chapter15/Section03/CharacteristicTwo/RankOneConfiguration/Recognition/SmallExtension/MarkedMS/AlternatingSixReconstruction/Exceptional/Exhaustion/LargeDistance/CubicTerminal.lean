module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicCoreControl

/-!
# The cubic midpoint terminal contradiction

For the original selected span P, its component-moved subgroup has the
same derived subgroup when P' is fixed by the component. Two-perfectness
makes the moved action idempotent, and the three-subgroups lemma removes
the cross commutator with the seed. The previously proved core supplement
therefore identifies P' with the whole core's derived subgroup.

Enlarging the common two-core intersection by the whole core gives a
normal subgroup. The seed centralizes the intersection, so normal generation
bounds the cross commutator by the same derived line. The two literal
midpoint slices supply the supplement and all these bounds. Transporting
them along the constructed conjugate critical path gives the opposite-core
estimates consumed by the terminal contradiction, without identifying the
cubic graph with a natural replacement or assuming a natural selected module.

Endpoint control also supplies nonabelianness: an abelian selected span
would lie in the two-core despite the odd extension kernel, and then in
the Baumann slice, contradicting forward escape. Thus every critical
midpoint orbit has a slice of index greater than two. The actual selected
radius-line span has a strict reciprocal slice, and both the whole-core
and literal C.1.32 consumers retain that alternative, both moving covers,
and the plane and Sylow radical images. Excluding these remaining alternatives
and both final reconstruction branches is still required.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.10), pp.879--881, and the final paragraph of (5.12), p.927;
Aschbacher--Smith C.1.31--32, pp.135--136. The algebra adapts this project's
Natural.Exhaustion.LargeDistance.SectionFive.CoreBounds, CoreSlice and
EndpointSpan to the original cubic projection, retaining its kernel E and E/Q.
-/

public noncomputable section
open CFSG.Quasithin.ChapterB.Offenders.Six
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
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
private theorem normalizes_commutator {F : Type*} [Group F] (J A B : Subgroup F)
    (hA : J ≤ normalizer (A : Set F)) (hB : J ≤ normalizer (B : Set F)) :
    J ≤ normalizer ((⁅A,B⁆ : Subgroup F) : Set F) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅A,B⁆ : Subgroup F).map (MulAut.conj g).toMonoidHom = ⁅A,B⁆
  rw [map_commutator]
  exact congrArg₂ (fun X Y : Subgroup F => ⁅X,Y⁆)
    (mem_normalizer_iff_map_conj_eq.mp (hA hg))
    (mem_normalizer_iff_map_conj_eq.mp (hB hg))

private theorem conjugate_span_commutator_le {F : Type*} [Group F]
    (J A N H : Subgroup F) (hAJ : A ≤ J)
    (hJN : J ≤ normalizer (N : Set F)) (hJH : J ≤ normalizer (H : Set F))
    (hAN : ⁅A,N⁆ ≤ H) :
    ⁅⨆ g : J, A.map (MulAut.conj (g : F)⁻¹).toMonoidHom,N⁆ ≤ H := by
  apply commutator_iSup_le_of_relative_normal J N H _ hJH
  · intro g x hx
    obtain ⟨a,ha,rfl⟩ := hx
    exact J.mul_mem (J.mul_mem (J.inv_mem g.property) (hAJ ha))
      (J.inv_mem (J.inv_mem g.property))
  · intro g
    have hm := map_mono (f := (MulAut.conj (g : F)⁻¹).toMonoidHom) hAN
    have hnN : N.map (MulAut.conj (g : F)⁻¹).toMonoidHom = N :=
      mem_normalizer_iff_map_conj_eq.mp (hJN (J.inv_mem g.property))
    have hnH : H.map (MulAut.conj (g : F)⁻¹).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (hJH (J.inv_mem g.property))
    rwa [map_commutator,hnN,hnH] at hm

private theorem core_cross_commutator_of_span {F : Type*} [Group F]
    (J A B K T Z S P W : Subgroup F)
    (hKJ : K ≤ J) (hAJ : A ≤ J) (hTJ : T ≤ J) (hZJ : Z ≤ J)
    (hPA : P ≤ A) (hWP : W ≤ P) (hSP : S ≤ P)
    (hJA : J ≤ normalizer (A : Set F)) (hJK : J ≤ normalizer (K : Set F))
    (hTB : T ≤ normalizer (B : Set F)) (hgen : K ⊔ T = J)
    (hZA : Z ≤ centralizer (A : Set F)) (hSB : S ≤ centralizer (B : Set F))
    (hspan : P = ⨆ g : J, S.map (MulAut.conj (g : F)⁻¹).toMonoidHom)
    (hder : ⁅P,P⁆ ≤ ⁅⁅A,K⁆,⁅A,K⁆⁆) (hsupp : ⁅A,K⁆ ≤ Z ⊔ W) :
    ⁅A ⊓ B,⁅A,K⁆⁆ ≤ ⁅⁅A,K⁆,⁅A,K⁆⁆ := by
  let C := ⁅A,K⁆
  let D := A ⊓ B
  let N := D ⊔ C
  let H := ⁅C,C⁆
  have hCA : C ≤ A := le_normalizer_iff_commutator_le_left.mp (hKJ.trans hJA)
  have hJC : J ≤ normalizer (C : Set F) := normalizes_commutator J A K hJA hJK
  have hJH : J ≤ normalizer (H : Set F) := normalizes_commutator J C C hJC hJC
  have hCP : ⁅C,P⁆ ≤ H := by
    apply (commutator_mono hsupp le_rfl).trans
    apply commutator_sup_le_of_relative_normal J Z W P H hJH hZJ
      (hWP.trans (hPA.trans hAJ))
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
        (hZA.trans (centralizer_le hPA))).le.trans bot_le
    · exact (commutator_mono hWP le_rfl).trans hder
  have hNA : N ≤ A := sup_le inf_le_left hCA
  have hKN : K ≤ normalizer (N : Set F) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono hNA le_rfl).trans (show C ≤ N from le_sup_right))
  have hTN : T ≤ normalizer (N : Set F) :=
    (le_inf
      ((le_inf (hTJ.trans hJA) hTB).trans inf_normalizer_le_normalizer_inf)
      (hTJ.trans hJC)).trans (normalizer_inf_normalizer_le_normalizer_sup D C)
  have hJN : J ≤ normalizer (N : Set F) := by
    rw [←hgen]
    exact sup_le hKN hTN
  have hSN : ⁅S,N⁆ ≤ H := by
    rw [commutator_comm]
    apply commutator_sup_le_of_relative_normal J D C S H hJH
      (inf_le_left.trans hAJ) (hCA.trans hAJ)
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
        (inf_le_right.trans (le_centralizer_iff.mp hSB))).le.trans bot_le
    · exact (commutator_mono le_rfl hSP).trans hCP
  have hPN : ⁅P,N⁆ ≤ H := by
    rw [hspan]
    exact conjugate_span_commutator_le J S N H (hSP.trans (hPA.trans hAJ))
      hJN hJH hSN
  rw [commutator_comm]
  apply (commutator_mono hsupp le_rfl).trans
  apply commutator_sup_le_of_relative_normal J Z W D H hJH hZJ
    (hWP.trans (hPA.trans hAJ))
  · exact (commutator_eq_bot_iff_le_centralizer.mpr
      (hZA.trans (centralizer_le inf_le_left))).le.trans bot_le
  · exact (commutator_mono hWP le_sup_left).trans hPN

include h in
private theorem selected_moved_span_idempotent
    (hb : 2 < sourceDistance h) (c : Vertex Rg)
    (hd : (cosetGraph Rg).dist c (alpha Rg) ≤ 2) :
    ⁅forwardMovedSpan Rg c,Ltilde Rg (alpha Rg)⁆ = forwardMovedSpan Rg c := by
  let P := localZSpan Rg c (alpha Rg)
  let W := P.comap (embedM Rg)
  have hPQ : P ≤ Q Rg (alpha Rg) :=
    (localZSpan_le_V Rg hd).trans (V_le_Q Rg (geometry := sourceGeometry h) rfl hb)
  have hPG : P ≤ (embedM Rg).range :=
    (hPQ.trans (fun _ hx => hx.1)).trans_eq (stabilizer_m_base Rg)
  have hmW : W.map (embedM Rg) = P := map_comap_eq_self hPG
  let : W.Normal := by
    refine ⟨?_⟩
    intro x hx g
    change embedM Rg (g*x*g⁻¹) ∈ P
    rw [map_mul,map_mul,map_inv]
    apply le_normalizer_iff.mp (localZSpan_normalized Rg c (alpha Rg))
    · change embedM Rg g ∈ stabilizer Rg (mVertex Rg 1)
      rw [stabilizer_m_base]
      exact ⟨g,rfl⟩
    · exact hx
  have hWQ : W ≤ pCore 2 M := by
    intro x hx
    have hxQ := hPQ hx
    rw [Q_alpha Rg (h.relative_radical.isPGroup) (h.relative_radical.twoCore_le)] at hxQ
    obtain ⟨y,hy,he⟩ := hxQ
    exact (embedM_injective Rg he) ▸ hy
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hres : pResidual 2 M = L.subgroupOf M := h.relative_residual
  have hK : IsPPerfect 2 (L.subgroupOf M) :=
    hres ▸ isPPerfect_pResidual 2
  have hi := commutator_isPPerfect_idempotent (L.subgroupOf M) W hK
    (pCore_isPGroup.to_le hWQ) le_normalizer_of_normal
  have hm := congrArg (Subgroup.map (embedM Rg)) hi
  rw [map_commutator,map_commutator,hmW,←hres,←Ltilde_alpha] at hm
  exact hm

include h in
/-- The component-moved selected span retains the entire original derived
subgroup. Coprime generation makes its residual action idempotent; the
three-subgroups lemma controls the cross commutator with the seed. -/
theorem selected_span_derived_eq_moved
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hfixed : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≤
      centralizer (Ltilde Rg (alpha Rg) : Set (FreeAmalgam Rg))) :
    ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ =
    ⁅forwardMovedSpan Rg (p.walk.getVert 2),forwardMovedSpan Rg (p.walk.getVert 2)⁆ := by
  let c := p.walk.getVert 2
  let P := localZSpan Rg c (alpha Rg)
  let P₀ := forwardMovedSpan Rg c
  let J := stabilizer Rg (alpha Rg)
  let C := ⁅P₀,P₀⁆
  have hd : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by have hh : p.walk.length = sourceDistance h := p.length_eq_b; omega)]
  have hP₀P : P₀ ≤ P := forwardMovedSpan_le Rg c
  have hPG : P ≤ J := (localZSpan_le_V Rg hd).trans
    ((sourceGeometry h).V_local _ rfl hb)
  have hSG : Z Rg c ≤ J := (Z_le_localZSpan Rg _ _).trans hPG
  have hNG : J ≤ normalizer (C : Set (FreeAmalgam Rg)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅P₀,P₀⁆).map (MulAut.conj g).toMonoidHom = _
    have hn : P₀.map (MulAut.conj g).toMonoidHom = P₀ :=
      mem_normalizer_iff_map_conj_eq.mp (forwardMovedSpan_normalized Rg c hg)
    rw [map_commutator,hn]
  have hcross : ⁅P₀,P⁆ ≤ C := by
    have hi : ⁅P₀,Ltilde Rg (alpha Rg)⁆ = P₀ :=
      selected_moved_span_idempotent (h := h) hb c hd
    conv_lhs => rw [←hi]
    apply commutator_commutator_le_of_rotate_of_le_normalizer
      ((hP₀P.trans hPG).trans hNG) ((Ltilde_le_stabilizer _).trans hNG) (hPG.trans hNG)
    · rw [commutator_comm (Ltilde Rg (alpha Rg))]
      exact le_rfl
    · have hz : ⁅⁅P,P₀⁆,Ltilde Rg (alpha Rg)⁆ = ⊥ :=
        commutator_eq_bot_iff_le_centralizer.mpr ((commutator_mono le_rfl hP₀P).trans hfixed)
      exact hz.le.trans bot_le
  have hgen : P = Z Rg c ⊔ P₀ := selected_span_eq_seed_sup_moved (h := h) hb p
  have hSP : ⁅Z Rg c,P⁆ ≤ C := by
    rw [hgen,commutator_comm]
    apply commutator_sup_le_of_relative_normal J _ _ _ C hNG hSG (hP₀P.trans hPG)
    · have hc : color Rg c = false :=
        (p.vertex_color (by have hh : p.walk.length = sourceDistance h := p.length_eq_b; omega)).mpr (by decide)
      let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c hc
      exact (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff_isMulCommutative.mpr inferInstance)).le.trans bot_le
    · exact (commutator_mono le_rfl (Z_le_localZSpan Rg _ _)).trans hcross
  apply le_antisymm _ (commutator_mono hP₀P hP₀P)
  calc
    ⁅P,P⁆ = ⁅Z Rg c ⊔ P₀,P⁆ := by rw [←hgen]
    _ ≤ C := commutator_sup_le_of_relative_normal J _ _ _ C hNG hSG (hP₀P.trans hPG) hSP hcross

include h in
/-- The common two-core intersection centralizes the actual core modulo its
derived subgroup, using the selected span's fixed derived subgroup and the
proved core supplement. -/
theorem selected_core_cross_commutator_of_supplement
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hfixed : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≤
      centralizer (Ltilde Rg (alpha Rg) : Set (FreeAmalgam Rg)))
    (hsupp : ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆ ≤
      Z Rg (alpha Rg) ⊔ forwardMovedSpan Rg (p.walk.getVert 2)) :
    let C := ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆
    ⁅Q Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert 2),C⁆ ≤ ⁅C,C⁆ := by
  let a := alpha Rg
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let J := stabilizer Rg a
  let P := localZSpan Rg c a
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg a t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hQa : Q Rg t ≤ J := fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  have hQc : Q Rg t ≤ stabilizer Rg c :=
    fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have hQJ : Q Rg a ≤ J := fun _ hx => hx.1
  have hPQ : P ≤ Q Rg a := by
    apply (localZSpan_le_V Rg _).trans
      (V_le_Q Rg (geometry := sourceGeometry h) rfl hb)
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)]
  have hJL : J ≤ normalizer (Ltilde Rg a : Set (FreeAmalgam Rg)) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    obtain ⟨z,hz,rfl⟩ := hx
    refine ⟨⟨g,hg⟩ * z * ⟨g,hg⟩⁻¹,?_,rfl⟩
    exact (inferInstance : (pResidual 2 (stabilizer Rg a)).Normal).conj_mem z hz ⟨g,hg⟩
  have he : ⁅P,P⁆ =
      ⁅⁅Q Rg a,Ltilde Rg a⁆,⁅Q Rg a,Ltilde Rg a⁆⁆ :=
    (selected_span_derived_eq_moved h hb p hfixed).trans
      (core_derived_eq_of_supplement h hb p hsupp).symm
  exact core_cross_commutator_of_span J (Q Rg a) (Q Rg c)
    (Ltilde Rg a) (Q Rg t) (Z Rg a) (Z Rg c) P
    (forwardMovedSpan Rg c) (Ltilde_le_stabilizer _) hQJ hQa
    (Z_le_stabilizer Rg a) hPQ (forwardMovedSpan_le Rg c)
    (Z_le_localZSpan Rg c a) (Q_normalized Rg a) hJL
    (hQc.trans (Q_normalized Rg c)) (CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
      (by rw [h.relative_residual]; exact (codisjoint_subgroupOf_sup L R).eq_top) rfl hat)
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a rfl))
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c hc))
    (localZSpan_eq_conjugates Rg c a) he.le hsupp

include h e hz hk in
/-- Both common-core estimates follow from the literal midpoint slices.
The selected derived line is fixed by the original stabilizer, so its
component-moved subgroup has the same derived subgroup. -/
theorem selected_core_bounds_of_midpoint_slices
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hnonabelian : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g (alpha Rg) = a')
    (hopposite : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a') ≤ 2) :
    let C := ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆
    Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 ∧
      ⁅Q Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert 2),C⁆ ≤ ⁅C,C⁆ := by
  have hb := distance_gt_two h e hz hk
  have hb4 := (selected_span_conjugate_critical_path h hb p hnonabelian).1
  have hs := midpoint_slice_eq_reverse_kernel h e hz hk hb4 p g hg he hopposite
  have hd := small_selected_span_derived h e hz hk hb p
    (by rw [hs.2.2.1]; decide) hslice hnonabelian
  have hc := selected_core_derived_of_midpoint_slices h e hz hk p
    hnonabelian hslice g hg he hopposite
  exact ⟨hc.2.2.1,selected_core_cross_commutator_of_supplement h hb p
    (hd.2.2.trans (centralizer_le (Ltilde_le_stabilizer _))) hc.1⟩

include h e hz hk in
/-- Both core bounds transport together with the literal midpoint orbit,
the two slices and the selected span. -/
theorem selected_core_bounds_of_midpoint_slices_at
    (hb : sourceDistance h = 4)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hnonabelian : ⁅localZSpan Rg (p.walk.getVert 2) a,
      localZSpan Rg (p.walk.getVert 2) a⁆ ≠ ⊥)
    (hslice : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g a = a')
    (hopposite : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a') ≤ 2) :
    let C := ⁅Q Rg a,Ltilde Rg a⁆
    Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 ∧
      ⁅Q Rg a ⊓ Q Rg (p.walk.getVert 2),C⁆ ≤ ⁅C,C⁆ := by
  obtain ⟨x,rfl⟩ := exists_mVertex_of_color Rg p.start_color
  have hxbase : act Rg x⁻¹ (mVertex Rg x) = alpha Rg := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have base := selected_core_bounds_of_midpoint_slices
    h e hz hk (a' := act Rg x⁻¹ a')
  rw [←hxbase] at base
  let k := x*g*x⁻¹
  have hrestore (v : Vertex Rg) : act Rg x (act Rg x⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hkg : k ∈ stabilizer Rg ((p.act x⁻¹).walk.getVert 2) := by
    change k ∈ stabilizer Rg ((actWalk Rg x⁻¹ p.walk).getVert 2)
    rw [actWalk_getVert,stabilizer_act]
    exact ⟨g,hg,by simp only [inv_inv]; rfl⟩
  have hke : act Rg k (act Rg x⁻¹ (mVertex Rg x)) = act Rg x⁻¹ a' := by
    simp only [k,act_mul]
    rw [hrestore,he]
  have hci : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by have hl : p.walk.length = sourceDistance h := p.length_eq_b; omega)).mpr (by decide)
  have hnon : ⁅localZSpan Rg ((p.act x⁻¹).walk.getVert 2)
        (act Rg x⁻¹ (mVertex Rg x)),
      localZSpan Rg ((p.act x⁻¹).walk.getVert 2)
        (act Rg x⁻¹ (mVertex Rg x))⁆ ≠ ⊥ := by
    change ⁅localZSpan Rg ((actWalk Rg x⁻¹ p.walk).getVert 2) _,
      localZSpan Rg ((actWalk Rg x⁻¹ p.walk).getVert 2) _⁆ ≠ ⊥
    rw [actWalk_getVert,LocalCommutator.CriticalCase.localZSpan_act,←map_commutator]
    intro hh
    exact hnonabelian (map_eq_bot_iff_of_injective _ (MulAut.conj _).injective |>.mp hh)
  have hsi : (B Rg (act Rg x⁻¹ (mVertex Rg x))
        ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg ((p.act x⁻¹).walk.getVert 2)) ≤ 2 := by
    change (B Rg _ _).relIndex
      (U Rg ((actWalk Rg x⁻¹ p.walk).getVert 2)) ≤ 2
    rw [actWalk_getVert,Escape.PairingControl.FirstPairing.B_act
      (by omega : 2 < sourceDistance h) _ _ p.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hslice
  have hki : (B Rg ((p.act x⁻¹).walk.getVert 2)
        ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg x⁻¹ a')) ≤ 2 := by
    change (B Rg ((actWalk Rg x⁻¹ p.walk).getVert 2) _).relIndex _ ≤ 2
    simp only [actWalk_getVert]
    rw [Escape.PairingControl.FirstPairing.B_act
      (by omega : 2 < sourceDistance h) _ _ hci,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hopposite
  have hh := base (p.act x⁻¹) hnon hsi k hkg hke hki
  dsimp only at hh
  change Nat.card (⁅⁅Q Rg (act Rg x⁻¹ (mVertex Rg x)),
      Ltilde Rg (act Rg x⁻¹ (mVertex Rg x))⁆,
      ⁅Q Rg (act Rg x⁻¹ (mVertex Rg x)),
      Ltilde Rg (act Rg x⁻¹ (mVertex Rg x))⁆⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 ∧
    ⁅Q Rg (act Rg x⁻¹ (mVertex Rg x)) ⊓
      Q Rg ((actWalk Rg x⁻¹ p.walk).getVert 2),
      ⁅Q Rg (act Rg x⁻¹ (mVertex Rg x)),
        Ltilde Rg (act Rg x⁻¹ (mVertex Rg x))⁆⁆ ≤
      ⁅⁅Q Rg (act Rg x⁻¹ (mVertex Rg x)),
        Ltilde Rg (act Rg x⁻¹ (mVertex Rg x))⁆,
        ⁅Q Rg (act Rg x⁻¹ (mVertex Rg x)),
        Ltilde Rg (act Rg x⁻¹ (mVertex Rg x))⁆⁆ at hh
  simpa only [actWalk_getVert,Q_act,Ltilde_act,inv_inv,
    ←Subgroup.map_inf _ _ (MulAut.conj x).toMonoidHom (MulAut.conj x).injective,←map_commutator,
    card_map_of_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective,
    map_le_map_iff_of_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective] using hh

include h e hz hk in
/-- The source distance-four contradiction on the same selected span and
midpoint orbit. Both opposite-core bounds are now consequences of the two
literal slice bounds; no natural marking of either span is used. -/
theorem point_selected_terminal_false_of_midpoint_slices
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hnonabelian : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g (alpha Rg) = a')
    (hopposite : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a') ≤ 2) : False := by
  have hb := distance_gt_two h e hz hk
  have hb4 := point_image_distance_eq_four h e hz hk u hR
  let c := p.walk.getVert 2
  have hci : color Rg c = false :=
    (p.vertex_color (by have hl := p.length_eq_b; change p.walk.length = sourceDistance h at hl; omega)).mpr (by decide)
  have hs := midpoint_slice_eq_reverse_kernel h e hz hk hb4 p g hg he hopposite
  have hd := small_selected_span_derived h e hz hk hb p
    (by rw [hs.2.2.1]; decide) hslice hnonabelian
  have hPQ := (selected_span_le_forward_kernel (h := h) hb p).trans inf_le_left
  have hnonOpp : ⁅localZSpan Rg (alpha Rg) c,localZSpan Rg (alpha Rg) c⁆ ≠ ⊥ := by
    have hstart : Z Rg (alpha Rg) ≤ localZSpan Rg (alpha Rg) c := Z_le_localZSpan Rg _ _
    have hend : Z Rg a' ≤ localZSpan Rg (alpha Rg) c := by
      rw [←he,Z_act]
      exact (map_mono hstart).trans_eq (mem_normalizer_iff_map_conj_eq.mp
        (localZSpan_normalized Rg (alpha Rg) c ((stabilizer Rg c).inv_mem hg)))
    intro hn
    exact critical_commutator_not_central h e hz hk p
      (((commutator_mono hstart hend).trans_eq hn).trans bot_le)
  obtain ⟨_,x,hx,q,_,hq,_⟩ := selected_span_conjugate_critical_path h hb p hnonabelian
  have hBn := Escape.Propagation.Rigidity.B_normalized (geometry := sourceGeometry h) hb c hci
  have hBm : (B Rg c ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg c ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (hBn ((stabilizer Rg c).inv_mem hg))
  have hforwardOpp : (B Rg c ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (q.walk.getVert 2)) ≤ 2 := by
    rw [hq]
    have hh := hopposite
    have hUe : U Rg a' = (U Rg (alpha Rg)).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [←he,U_act]
    rw [hUe,←hBm,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hh
    exact hh
  have hBma : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := sourceGeometry h)
        hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hx))
  have hoppositeOpp : (B Rg (q.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg x c)) ≤ 2 := by
    rw [hq,U_act,←hBma,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hslice
  have hbounds := selected_core_bounds_of_midpoint_slices_at h e hz hk hb4 q
    (by simpa only [hq] using hnonOpp) hforwardOpp x (hq.symm ▸ hx) rfl hoppositeOpp
  dsimp only at hbounds
  rw [hq] at hbounds
  exact point_selected_terminal_false_of_opposite_core_bounds h e hz hk u hR p hd.2.1
    hbounds.1 ((commutator_mono (le_inf inf_le_right (inf_le_left.trans hPQ)) le_rfl).trans hbounds.2)


include h e hz hk in
/-- Endpoint control forces nonabelianness of the original selected span.
An abelian span is a two-subgroup of the full seed centralizer, hence lies
in Q even though that full centralizer may contain the cubic kernel. -/
theorem point_selected_span_nonabelian_of_endpoint
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hcomm : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓
      Q Rg (p.walk.getVert 2),Z Rg a'⁆ ≤ Z Rg (alpha Rg)) :
    ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ := by
  intro he
  have hb := distance_gt_two h e hz hk
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan Rg c (alpha Rg)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases hh' : color Rg t <;> simp_all
  have hPQ := (selected_span_le_forward_kernel (h := h) hb p).trans inf_le_left
  have hPG : P ≤ stabilizer Rg c :=
    (hPQ.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hPc : P ≤ Q Rg c := two_subgroup_seed_centralizer_le_core h e hz hcol P
    ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
      (alpha Rg) rfl).to_le hPQ)
    (le_inf hPG ((commutator_eq_bot_iff_le_centralizer.mp he).trans
      (centralizer_le (Z_le_localZSpan Rg c (alpha Rg)))))
  have hPV : P ≤ V Rg (alpha Rg) := localZSpan_le_V Rg (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  change ⁅P ⊓ Q Rg c,Z Rg a'⁆ ≤ Z Rg (alpha Rg) at hcomm
  have hPB := normalized_radius_le_slice_of_critical_commutator h e hz hb p P hPV
    (localZSpan_normalized Rg _ _) (by simpa only [inf_eq_left.mpr hPc] using hcomm)
  exact full_point_critical_forward_eligible h e hz hk hb u
    (full_point_image_of_contained h e hz hk u hR) p
    ((DistanceEight.U_le_Z Rg _).trans ((Z_le_localZSpan Rg _ _).trans hPB))

include h e hz hk in
/-- On a literal midpoint-conjugate critical path, at least one of the two
Baumann slices is larger than two. Endpoint control supplies nonabelianness;
the two core estimates and terminal contradiction are both discharged. -/
theorem point_midpoint_slice_alternative
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g (alpha Rg) = a') :
    2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2)) ∨
      2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg a') := by
  by_contra! hs
  have hb := distance_gt_two h e hz hk
  have hb4 := point_image_distance_eq_four h e hz hk u hR
  have hPQ := (selected_span_le_forward_kernel (h := h) hb p).trans inf_le_left
  have hm := (midpoint_common_kernel_endpoint_commutator h e hz hk hb4 p g hg he hs.2).2
  have hcomm : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓
      Q Rg (p.walk.getVert 2),Z Rg a'⁆ ≤ Z Rg (alpha Rg) :=
    ((commutator_mono (inf_le_inf_right _ hPQ) le_rfl).trans_eq hm).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
          (sourceDistance_pos h) p.critical).trans (Z_normalized Rg _)))
  exact point_selected_terminal_false_of_midpoint_slices h e hz hk u hR p
    (point_selected_span_nonabelian_of_endpoint h e hz hk u hR p hcomm) hs.1 g hg he hs.2

include h e hz hk in
/-- The midpoint slice obstruction transports along the original graph,
retaining the same critical path and its actual conjugator. -/
theorem point_midpoint_slice_alternative_at
    (u : S)
    (hR : (Rg).map π ≤
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g a = a') :
    2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2)) ∨
      2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg a') := by
  have hb := point_image_distance_eq_four h e hz hk u hR
  obtain ⟨x,rfl⟩ := exists_mVertex_of_color Rg p.start_color
  have hxbase : act Rg x⁻¹ (mVertex Rg x) = alpha Rg := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have base := point_midpoint_slice_alternative h e hz hk u hR
    (a' := act Rg x⁻¹ a')
  rw [←hxbase] at base
  let k := x*g*x⁻¹
  have hrestore (v : Vertex Rg) : act Rg x (act Rg x⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hkg : k ∈ stabilizer Rg ((p.act x⁻¹).walk.getVert 2) := by
    change k ∈ stabilizer Rg ((actWalk Rg x⁻¹ p.walk).getVert 2)
    rw [actWalk_getVert,stabilizer_act]
    exact ⟨g,hg,by simp only [inv_inv]; rfl⟩
  have hke : act Rg k (act Rg x⁻¹ (mVertex Rg x)) = act Rg x⁻¹ a' := by
    simp only [k,act_mul]
    rw [hrestore,he]
  have hci : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by have hl : p.walk.length = sourceDistance h := p.length_eq_b; omega)).mpr (by decide)
  have hh := base (p.act x⁻¹) k hkg hke
  change 2 < (B Rg (act Rg x⁻¹ (mVertex Rg x))
      ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg ((actWalk Rg x⁻¹ p.walk).getVert 2)) ∨
    2 < (B Rg ((actWalk Rg x⁻¹ p.walk).getVert 2)
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg x⁻¹ a')) at hh
  rw [actWalk_getVert,
    Escape.PairingControl.FirstPairing.B_act (by omega : 2 < sourceDistance h) _ _ p.start_color,
    Escape.PairingControl.FirstPairing.B_act (by omega : 2 < sourceDistance h) _ _ hci,
    U_act,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective,
    relIndex_map_map_of_injective _ _ (MulAut.conj _).injective] at hh
  exact hh

include h e hz hk in
/-- A nonabelian selected span constructs its own conjugate critical path.
Consequently its two reciprocal slices cannot both be small, without any
extra midpoint-conjugator hypothesis on the original path. -/
theorem point_selected_reciprocal_slice_alternative
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hnon : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥) :
    2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2)) ∨
      2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (alpha Rg)) := by
  have hb := distance_gt_two h e hz hk
  obtain ⟨_,x,hx,q,_,hq,_⟩ := selected_span_conjugate_critical_path h hb p hnon
  have hh := point_midpoint_slice_alternative_at h e hz hk u hR q x (hq.symm ▸ hx) rfl
  have hBm : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := sourceGeometry h)
        hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hx))
  rw [hq,U_act,←hBm,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective] at hh
  exact hh.symm

include h e hz hk in
/-- The original selected span retains its radius line and now has a strict
reciprocal slice. The chosen path, core and full covers are unchanged. -/
theorem point_image_selected_radius_line_and_strict_slice
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
      let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
      Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
      (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (p.walk.getVert 2)) ∨
        2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (alpha Rg))) := by
  obtain ⟨a',p,hcard,hcentral,hradius⟩ := point_image_selected_span_radius_line h e hz hk u hR
  have hn : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hcard
    omega
  exact ⟨a',p,hcard,hcentral,hradius,point_selected_reciprocal_slice_alternative h e hz hk u hR p hn⟩

omit hk in
include h e hz in
/-- Whole-core application of the terminal midpoint contradiction. The
point-core branch has a strict slice on the actual selected span; plane
and Sylow images remain separate alternatives, with both covers retained. -/
theorem coreExhaustion_or_cubic_terminal_slices :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a')
              (g : FreeAmalgam Rg), g ∈ stabilizer Rg (p.walk.getVert 2) →
              act Rg g a = a' →
            2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
                (U Rg (p.walk.getVert 2)) ∨
              2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
                (U Rg a')) ∧
          ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
            let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
            Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
            (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
                (U Rg (p.walk.getVert 2)) ∨
              2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
                (U Rg (alpha Rg)))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_radical_cases h e hz with
    hx | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ?_⟩
    exact ⟨hpoint.2,hpoint.1,
      fun _ _ p g hg he => point_midpoint_slice_alternative_at h e hz hk u hpoint.2.le p g hg he,
      point_image_selected_radius_line_and_strict_slice h e hz hk u hpoint.2.le⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application with the same original cubic projection,
critical paths and selected radius line. It does not yet exclude the
strict-slice, plane or Sylow alternatives. -/
theorem rankTwo_or_cubic_terminal_slices :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a')
              (g : FreeAmalgam Rg), g ∈ stabilizer Rg (p.walk.getVert 2) →
              act Rg g a = a' →
            2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
                (U Rg (p.walk.getVert 2)) ∨
              2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
                (U Rg a')) ∧
          ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
            let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
            Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
            (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
                (U Rg (p.walk.getVert 2)) ∨
              2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
                (U Rg (alpha Rg)))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_terminal_slices h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
