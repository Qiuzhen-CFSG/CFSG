module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSelectedFour

public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardMovedSpanNatural

/-!
# Excluding large critical images at distance four in the cubic graph

The selected span has elementary abelian central quotient. Radius centrality
makes the original two-core act trivially on this quotient. If the component
also acted trivially, its action modulo the span center and the incident edge
would normalize an abelian seed-center join, forcing the whole span abelian.
Thus a nonabelian span has action kernel contained in the original extension
kernel E. This does not assume that E/Q acts trivially on the quotient.

For a large critical image, the actual controlled reverse subactor supplies a
generating edge. The original forward seed is eligible, so its conjugate gives
a backward critical path with all overlapping vertices retained. The selected
line is central and has order two. Its full critical kernel is normalized by
the generating edge; the controlled subactor then puts that kernel in the
starting Baumann slice. Consequently the forward slice has index at most two,
and the two conjugate critical seeds make its selected span nonabelian.

An even involution in the controlled actor's marked image fixes a subgroup of
index at most two in this selected central quotient. EvenLift gives displacement
at least two because the action kernel lies in E. This contradiction excludes
large critical images at distance four, without discarding the cubic kernel or
the central attachment in either moving cover. All critical images and lines
in the full point-core branch therefore have order two.

The whole-core and literal C.1.32 consumers retain the plane and Sylow images.
The remaining small-image distance-four contradiction, other radical branches,
natural exhaustion and both intrinsic block reconstructions are not asserted.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.10) and (5.12)(2), printed pp.879--881 and 925--926;
Aschbacher--Smith C.1.31--32, printed pp.135--136. The selected-span arguments
adapt Natural.Exhaustion.LargeDistance.SectionFive.SelectedSpan and SelectedFour
to the original cubic graph. The even-lift argument permits the retained odd
kernel, and the backward selection uses the actual restricted even subactor.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
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
omit [Finite G] in
private theorem span_core_le_action_kernel (K : Subgroup M) (c : Vertex Rg)
    (hK : K.map (embedM Rg) ≤ Q Rg (alpha Rg))
    (hcentral : ⁅localZSpan Rg c (alpha Rg),Q Rg (alpha Rg)⁆ ≤
      centralizer (localZSpan Rg c (alpha Rg) : Set (FreeAmalgam Rg))) :
    K ≤ (forwardSpanCentralAction Rg c).ker := by
  let P := localZSpan Rg c (alpha Rg)
  intro m hm
  have hmQ : embedM Rg m ∈ Q Rg (alpha Rg) := hK (mem_map_of_mem (embedM Rg) hm)
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro v
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center P) v
  rw [forwardSpanCentralAction_apply]
  apply QuotientGroup.eq_iff_div_mem.mpr
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  have hmem : ⁅embedM Rg m,(x:FreeAmalgam Rg)⁆ ∈ ⁅P,Q Rg (alpha Rg)⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hmQ x.property
  change (y:FreeAmalgam Rg) * (embedM Rg m*(x:FreeAmalgam Rg)*(embedM Rg m)⁻¹/(x:FreeAmalgam Rg)) =
    (embedM Rg m*(x:FreeAmalgam Rg)*(embedM Rg m)⁻¹/(x:FreeAmalgam Rg))*(y:FreeAmalgam Rg)
  simpa only [div_eq_mul_inv,commutatorElement_def] using hcentral hmem y y.property


include h e hz hk in
/-- The actual selected span has elementary abelian central quotient. -/
theorem selected_span_central_quotient_elementary (hb : 2 < sourceDistance h) (c : Vertex Rg)
    (hd : (cosetGraph Rg).dist c (alpha Rg) ≤ 2) :
    IsElementaryAbelian 2 ((localZSpan Rg c (alpha Rg)) ⧸
      center (localZSpan Rg c (alpha Rg))) := by
  let P := localZSpan Rg c (alpha Rg)
  have hPV : P ≤ V Rg (alpha Rg) := localZSpan_le_V Rg hd
  have hs (x : P) : x^2 ∈ center P := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hVV : ⁅V Rg (alpha Rg),V Rg (alpha Rg)⁆ ≤
        centralizer (V Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
      (commutator_mono le_rfl (V_le_Q Rg (geometry := sourceGeometry h) rfl hb)).trans
        (radius_commutator_central h e hz hk)
    exact hVV (radius_sq_mem_derived (sourceGeometry h) (sourceDistance_pos h)
      (alpha Rg) rfl ⟨x,hPV x.property⟩) y (hPV y.property)
  have hp (x : P ⧸ center P) : x^2 = 1 := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center P) x
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hs x)
  let : IsMulCommutative (P ⧸ center P) :=
    ⟨⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun z => orderOf_dvd_of_pow_eq_one (hp z)) x y).eq⟩⟩
  exact ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp⟩

include h e hz hk in
/-- The original two-core fixes the selected central quotient. -/
theorem selected_span_central_action_kills_core (_hb : 2 < sourceDistance h) (c : Vertex Rg)
    (hd : (cosetGraph Rg).dist c (alpha Rg) ≤ 2) :
    pCore 2 M ≤ (forwardSpanCentralAction Rg c).ker := by
  apply span_core_le_action_kernel
  · rw [Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le]
  · have hPV := localZSpan_le_V Rg hd
    exact ((commutator_mono hPV le_rfl).trans (radius_commutator_central h e hz hk)).trans
      (centralizer_le hPV)

include h e hz hk in
/-- Nonabelianness detects the component on the selected central quotient.
Its kernel is contained in E, with no assertion that it kills E/Q. -/
theorem selected_span_central_action_kernel_le_extension
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hnonabelian : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥) :
    (forwardSpanCentralAction Rg (p.walk.getVert 2)).ker ≤ extensionKernel h := by
  have hd : (cosetGraph Rg).dist (p.walk.getVert 2) (alpha Rg) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by have hh := p.length_eq_b; change p.walk.length = sourceDistance h at hh; omega)]
  rcases normal_over_core_dichotomy h e
      (forwardSpanCentralAction Rg (p.walk.getVert 2)).ker
      (selected_span_central_action_kills_core h e hz hk hb _ hd) with hE | hK
  · exact hE
  exfalso
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan Rg c (alpha Rg)
  let C := (center P).map P.subtype
  let B := Z Rg c⊔C
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color Rg c=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent Rg c t :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hZP : Z Rg c≤P := Z_le_localZSpan Rg _ _
  have hCP : C≤P := map_subtype_le _
  have hCC : C≤centralizer (P:Set (FreeAmalgam Rg)) := by
    rintro _ ⟨z,hz,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)
  have hBP : B≤P := sup_le hZP hCP
  have hPL : ⁅P,Ltilde Rg (alpha Rg)⁆≤C := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl z hz
    rw [Ltilde_alpha,h.relative_residual] at hl
    obtain ⟨m,hm,rfl⟩ := hl
    have he : (1 : MulAut (P ⧸ center P)) = forwardSpanCentralAction Rg c m :=
      (MonoidHom.mem_ker.mp (hK hm)).symm
    have hh := DFunLike.congr_fun he (QuotientGroup.mk' (center P) ⟨z,hz⟩)
    have hq : QuotientGroup.mk' (center P)
        (forwardSpanAction Rg c m ⟨z,hz⟩) = QuotientGroup.mk' (center P) ⟨z,hz⟩ := by
      exact (forwardSpanCentralAction_apply Rg c m ⟨z,hz⟩).symm.trans
        (by simpa only [MulAut.one_apply] using hh.symm)
    have hmem := QuotientGroup.eq_iff_div_mem.mp hq
    refine ⟨forwardSpanAction Rg c m ⟨z,hz⟩/⟨z,hz⟩,hmem,?_⟩
    change embedM Rg m*z*(embedM Rg m)⁻¹/z=⁅embedM Rg m,z⁆
    rw [div_eq_mul_inv,commutatorElement_def]
  have hLB : Ltilde Rg (alpha Rg)≤normalizer (B:Set (FreeAmalgam Rg)) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono hBP le_rfl).trans (hPL.trans le_sup_right))
  have hQtG : Q Rg t≤stabilizer Rg (alpha Rg) := fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  have hQtGc : Q Rg t≤stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have hGC : stabilizer Rg (alpha Rg)≤normalizer (C:Set (FreeAmalgam Rg)) :=
    (localZSpan_normalized Rg _ _).trans
      (normalizer_le_normalizer_characteristic_image P (center P))
  have hQtB : Q Rg t≤normalizer (B:Set (FreeAmalgam Rg)) :=
    (le_inf (hQtGc.trans (Z_normalized Rg c)) (hQtG.trans hGC)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hGB : stabilizer Rg (alpha Rg)≤normalizer (B:Set (FreeAmalgam Rg)) := by
    have hgen : Ltilde Rg (alpha Rg) ⊔ Q Rg t = stabilizer Rg (alpha Rg) := by
      apply CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
      · rw [h.relative_residual]
        exact (codisjoint_subgroupOf_sup L R).eq_top
      · rfl
      · exact hat
    rw [←hgen]
    exact sup_le hLB hQtB
  have hPB : P≤B := by
    dsimp only [P]
    rw [localZSpan_eq_conjugates]
    apply iSup_le
    intro g
    rintro _ ⟨z,hz,rfl⟩
    exact (mem_normalizer_iff.mp (hGB ((stabilizer Rg (alpha Rg)).inv_mem g.property)) z).mp
      ((show Z Rg c≤B from le_sup_left) hz)
  have hBC : B≤centralizer (B:Set (FreeAmalgam Rg)) := by
    apply sup_le
    · apply le_centralizer_iff.mpr
      let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c hc
      exact sup_le (le_centralizer_iff_isMulCommutative.mpr inferInstance)
        (hCC.trans (centralizer_le hZP))
    · exact hCC.trans (centralizer_le hBP)
  have hab : ⁅P,P⁆=⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((hPB.trans hBC).trans (centralizer_le hPB))
  exact hnonabelian hab


include h in
/-- An actor controlling the common-core commutator fixes a subgroup of
index at most two in the selected central quotient. -/
theorem selected_span_actor_fixed_index
    (hb : 2 < sourceDistance h)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hd : (cosetGraph Rg).dist (p.walk.getVert 2) (alpha Rg) ≤ 2)
    (hindex : (Q Rg (p.walk.getVert 2)).relIndex
      (localZSpan Rg (p.walk.getVert 2) (alpha Rg)) ≤ 2)
    (A : Subgroup (FreeAmalgam Rg))
    (hcomm : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓
        Q Rg (p.walk.getVert 2), A⁆ ≤ Z Rg (alpha Rg))
    (m : M) (hm : embedM Rg m ∈ A) :
    (forwardSpanCentralAction Rg (p.walk.getVert 2) m).fixedSubgroup.index ≤ 2 := by
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  let C := Q Rg (p.walk.getVert 2)
  let q : P →* P ⧸ center P := QuotientGroup.mk' (center P)
  have hPQ : P ≤ Q Rg (alpha Rg) :=
    (localZSpan_le_V Rg hd).trans
      (V_le_Q Rg (geometry := sourceGeometry h) rfl hb)
  have hPG : P ≤ stabilizer Rg (alpha Rg) := hPQ.trans (by intro x hx; exact hx.1)
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  have hZaC : Z Rg (alpha Rg) ≤ centralizer (P : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg _ rfl)).trans
      (centralizer_le hPQ)
  have hfix : (C.subgroupOf P).map q ≤
      (forwardSpanCentralAction Rg (p.walk.getVert 2) m).fixedSubgroup := by
    rintro _ ⟨x,hx,rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [forwardSpanCentralAction_apply]
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hz : ⁅embedM Rg m,(x:FreeAmalgam Rg)⁆ ∈ Z Rg (alpha Rg) := by
      apply hcomm
      rw [commutator_comm]
      exact commutator_mem_commutator hm ⟨x.property,hx⟩
    change (y:FreeAmalgam Rg)*(embedM Rg m*(x:FreeAmalgam Rg)*(embedM Rg m)⁻¹/(x:FreeAmalgam Rg)) =
      (embedM Rg m*(x:FreeAmalgam Rg)*(embedM Rg m)⁻¹/(x:FreeAmalgam Rg))*(y:FreeAmalgam Rg)
    simpa only [div_eq_mul_inv,commutatorElement_def] using hZaC hz y y.property
  have hi : ((C.subgroupOf P).map q).index ≤ C.relIndex P := Nat.le_of_dvd
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    ((C.subgroupOf P).index_map_dvd (QuotientGroup.mk'_surjective (center P)))
  exact (index_antitone hfix).trans (hi.trans hindex)


private theorem linearized_cyclic_codim_le_one
    {Y : Type*} [Group Y] [Finite Y] [IsElementaryAbelian 2 Y]
    {D : Type*} [Group D] (ρ : D→*MulAut Y)
    (a : D) (hi : (ρ a).fixedSubgroup.index≤2) :
    fixedCodim (Offenders.linearize ρ) (zpowers a)≤1 := by
  let σ := Offenders.linearize ρ
  change fixedCodim σ (zpowers a)≤1
  let e : fixedSpace σ (zpowers a) ≃ (ρ a).fixedSubgroup := {
    toFun := fun v => ⟨v.val.toMul, (MulAut.mem_fixedSubgroup _ _).mpr
      (congrArg Additive.toMul ((mem_fixedSpace_zpowers_iff σ a v.val).mp v.property))⟩
    invFun := fun v => ⟨Additive.ofMul v.val,(mem_fixedSpace_zpowers_iff σ a _).mpr
      (congrArg Additive.ofMul ((MulAut.mem_fixedSubgroup _ _).mp v.property))⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcard : Nat.card Y≤Nat.card ((ρ a).fixedSubgroup)*2 := by
    rw [←(ρ a).fixedSubgroup.card_mul_index]
    exact Nat.mul_le_mul_left _ hi
  rw [←Nat.card_congr e] at hcard
  change Nat.card (Additive Y)≤_ at hcard
  have hV := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive Y)
  have hF := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=fixedSpace σ (zpowers a))
  rw [Nat.card_zmod] at hV hF
  rw [hV,hF] at hcard
  have hd : Module.finrank (ZMod 2) (Additive Y)≤
      Module.finrank (ZMod 2) (fixedSpace σ (zpowers a))+1 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    simpa only [pow_succ] using hcard
  have hs := fixedCodim_add_finrank σ (zpowers a)
  omega



include h e hz in
private theorem controlled_backward_kernel_le_slice
    (hb : 2 < sourceDistance h) {a' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (A : Subgroup (FreeAmalgam Rg)) (hAG : A ≤ stabilizer Rg (alpha Rg))
    (htwo : IsPGroup 2 A) (hAn : ¬ A ≤ Q Rg (alpha Rg))
    (hdisp : ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),A⁆ ≤ Z Rg (alpha Rg))
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ A = stabilizer Rg (alpha Rg))
    (K : Subgroup (FreeAmalgam Rg)) (hKc : K ≤ Z Rg c)
    (hKQ : K ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hKn : Q Rg t ≤ normalizer (K : Set (FreeAmalgam Rg))) :
    K ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  let Y := K ⊔ Z Rg (alpha Rg)
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    le_sup_left.trans (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hct)
  have hKV : K ≤ V Rg (alpha Rg) := hKc.trans hZV
  have hKG := hKV.trans ((sourceGeometry h).V_local _ rfl hb)
  have hKA : ⁅K,A⁆ ≤ Z Rg (alpha Rg) :=
    (commutator_mono (le_inf hKV hKQ) le_rfl).trans hdisp
  have hYA : ⁅Y,A⁆ ≤ Z Rg (alpha Rg) :=
    commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg)) K
      (Z Rg (alpha Rg)) A (Z Rg (alpha Rg)) (Z_normalized Rg _)
      hKG (Z_le_stabilizer Rg _) hKA
      (le_normalizer_iff_commutator_le_left.mp (hAG.trans (Z_normalized Rg _)))
  have hYN : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    apply sup_le
    · exact (le_inf hKn ((show Q Rg t ≤ stabilizer Rg (alpha Rg) from
        fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr (hYA.trans le_sup_right)
  exact le_sup_left.trans (normalized_radius_le_slice_of_controlled_actor h e hz hb rfl
    Y A (sup_le hKV (Z_le_VBall Rg _ 2)) hYN hAG htwo hAn hYA)

include h e hz hk in
/-- At distance four a large critical image has a small forward slice and
nonabelian selected span. The backward construction uses the actual controlled
subactor, the same local conjugator and its complete path overlap. -/
theorem large_image_four_span_estimates
    (hb : sourceDistance h = 4) (u : S)
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg))) :
    (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2 ∧
    ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ := by
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hat₁ : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hdelta : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨A,hAU,htwo,hAn,hdisp,t,hat,hgen⟩ :=
    large_full_point_generating_actor h e hz hk u hfull p hlarge
  have hAZ : A ≤ Z Rg a' := hAU.trans (DistanceEight.U_le_Z Rg a')
  have hZG : Z Rg a' ≤ stabilizer Rg (alpha Rg) :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical
  have hAG := hAZ.trans hZG
  have hgenZ : Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) :=
    le_antisymm (sup_le (le_sup_left.trans hgen.le) hZG)
      (hgen.symm.le.trans (sup_le_sup_left hAZ _))
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hat₁ hat
  let c := act Rg g (p.walk.getVert 2)
  have hct : Adjacent Rg c t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hdelta
  have hcol : color Rg c = false := by
    rw [action_preserves_color]
    exact (p.vertex_color (by omega)).mpr (by decide)
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
  have hel := full_point_critical_forward_eligible h e hz hk hb2 u hfull p
  have helc : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    intro hh
    apply hel
    change U Rg (act Rg g (p.walk.getVert 2)) ≤ _ at hh
    rw [U_act,←hB] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  have hbad : ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    intro hh
    apply helc
    exact (DistanceEight.U_le_Z Rg c).trans
      (controlled_backward_kernel_le_slice h e hz hb2 p A hAG htwo hAn hdisp hat hct
        hgen (Z Rg c) le_rfl hh ((show Q Rg t ≤ stabilizer Rg c from
          fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg c)))
  let w : (cosetGraph Rg).Walk c (alpha Rg) :=
    .cons ((cosetGraph_adj Rg _ _).mpr hct)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (Nat.le_of_lt hb2) hcol w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  have hq2 : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
      p.prepend_two_overlap (Nat.le_of_lt hb2) hcol w hw hbad (i := 0) (Nat.zero_le _)
  have hgen' : Q Rg (q.walk.getVert 1) ⊔ Z Rg a' = stabilizer Rg (alpha Rg) := by rwa [hqt]
  have hi := selected_backward_indices_two_of_distance_four h e hz hk u hfull hb p q hq2 hgen'
  have hcentral := selected_critical_commutator_central h e hz hk u hfull.le q p
    (by simpa only [hq2] using (q.dist_start (i := 2) (by have hh := q.length_eq_b; change q.walk.length = sourceDistance h at hh; omega)).le)
    (by have hh := (p.dist_start (i := p.walk.length-2) (Nat.sub_le _ _)).le
        simpa only [SimpleGraph.dist_comm,hl,Nat.reduceSub] using hh)
    (by rw [p.dist_end,hl,hb]; decide) hgen'
  let K := Z Rg c ⊓ Q Rg (p.walk.getVert (p.walk.length-2))
  have hKn : Q Rg t ≤ normalizer (K : Set (FreeAmalgam Rg)) := by
    have hcG : Q Rg t ≤ stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hct)
    have haG : Q Rg t ≤ stabilizer Rg (alpha Rg) := fun _ hx => hx.2 _ (adjacent_symm Rg hat)
    have he := small_critical_kernel_normalizer_eq_line_centralizer h e hz hk q (by omega)
    exact (le_inf hcG (haG.trans (le_centralizer_iff.mp hcentral))).trans
      (he.symm.le.trans inf_le_right)
  have hKB : K ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    controlled_backward_kernel_le_slice h e hz hb2 p A hAG htwo hAn hdisp hat hct
      hgen K inf_le_left inf_le_right hKn
  let := finite_Z Rg c
  have hidx := relIndex_le_of_le_left hKB
    (index_ne_zero_of_finite (H := K.subgroupOf (Z Rg c)))
  change (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (Z Rg c) ≤ K.relIndex (Z Rg c) at hidx
  have hidx' : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2 := by
    have hh := ((relIndex_le_of_le_right (DistanceEight.U_le_Z Rg c)
      index_ne_zero_of_finite).trans hidx)
    simpa only [K,inf_relIndex_left,hi.1] using hh
  change (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg g (p.walk.getVert 2))) ≤ 2 at hidx'
  rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hidx'
  refine ⟨hidx',?_⟩
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  have hcP : Z Rg (p.walk.getVert 2) ≤ P := Z_le_localZSpan Rg _ _
  have hgP : Z Rg c ≤ P := by
    rw [Z_act]
    exact (map_mono hcP).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized Rg _ _ ((stabilizer Rg (alpha Rg)).inv_mem hg)))
  intro hn
  apply critical_commutator_not_central h e hz hk q
  exact (commutator_mono hgP (by simpa only [hl,Nat.reduceSub] using hcP)).trans (hn ▸ bot_le)

include h e hz hk in
/-- Large critical images at distance four are impossible in the full point-core
branch. The controlled even actor would move at least two binary dimensions
on the nonabelian selected central quotient, but its fixed index is at most two.
The argument retains the action of the cubic kernel on that quotient. -/
theorem large_critical_image_four_false
    (hb : sourceDistance h = 4) (u : S)
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg))) : False := by
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨hslice,hnon⟩ := large_image_four_span_estimates h e hz hk hb u hfull p hlarge
  have hd : (cosetGraph Rg).dist (p.walk.getVert 2) (alpha Rg) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)]
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  have hPG : P ≤ stabilizer Rg (alpha Rg) :=
    (localZSpan_le_V Rg hd).trans ((sourceGeometry h).V_local _ rfl hb2)
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  let := selected_span_central_quotient_elementary h e hz hk hb2 (p.walk.getVert 2) hd
  let ρ := forwardSpanCentralAction Rg (p.walk.getVert 2)
  let σ := Offenders.linearize ρ
  have hker : σ.ker ≤ (π).ker := by
    rw [CubicAction.projection_kernel]
    apply le_trans ?_ (selected_span_central_action_kernel_le_extension h e hz hk hb2 p hnon)
    intro m hm
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro v
    exact congrArg Additive.toMul (LinearMap.congr_fun hm (Additive.ofMul v))
  obtain ⟨A,hAU,hdisp,a,haA,ha,heven⟩ := critical_radius_even_actor h e hz hk p hlarge
  obtain ⟨m,hm,rfl⟩ := haA
  have hindex := (selected_span_index_of_forward_slice h e hz hk hb2 p hslice).2
  have hcomm : ⁅P ⊓ Q Rg (p.walk.getVert 2),A⁆ ≤ Z Rg (alpha Rg) := by
    have he : p.walk.length-2 = 2 := by omega
    rw [he] at hdisp
    exact (commutator_mono (inf_le_inf_right _ (localZSpan_le_V Rg hd)) le_rfl).trans hdisp
  have hfixed := selected_span_actor_fixed_index h hb2 p hd hindex A hcomm m hm
  have hup := linearized_cyclic_codim_le_one ρ m hfixed
  change fixedCodim σ (zpowers m) ≤ 1 at hup
  have hlo := EvenLift.fixedCodim_lower π (CubicEven.projection_surjective h e hz hk)
    σ hker m heven ha
  omega

include h e hz hk in
/-- Every original critical path in the full point-core branch has small
images at distance four. -/
theorem full_point_four_critical_indices_two
    (hb : sourceDistance h = 4) (u : S)
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    (Q Rg a').relIndex (Z Rg (alpha Rg)) = 2 ∧
      (Q Rg (alpha Rg)).relIndex (Z Rg a') = 2 := by
  apply small_critical_indices h e hz hk p
  by_contra! hlarge
  exact large_critical_image_four_false h e hz hk hb u hfull p hlarge

include h e hz hk in
/-- Both seed indices and the literal critical commutator have order two
at every vertex of the original cubic graph. -/
theorem full_point_four_critical_indices_two_at
    (hb : sourceDistance h = 4) (u : S)
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a') :
    (Q Rg a').relIndex (Z Rg a) = 2 ∧ (Q Rg a).relIndex (Z Rg a') = 2 ∧
      Nat.card (⁅Z Rg a,Z Rg a'⁆ : Subgroup (FreeAmalgam Rg)) = 2 := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := full_point_four_critical_indices_two h e hz hk hb u hfull
    (a' := act Rg g⁻¹ a')
  rw [←hbase] at base
  have hi := base (p.act g⁻¹)
  simp only [Q_act,Z_act,inv_inv,relIndex_map_map_of_injective
    (f := (MulAut.conj g).toMonoidHom) _ _ (MulAut.conj g).injective] at hi
  exact ⟨hi.1,hi.2,small_critical_commutator_card h e hz hk p (by omega)⟩

include h e hz hk in
/-- Point-core containment now forces every critical image and line to have
order two, on the same graph with the same projection and full covers. -/
theorem point_image_critical_indices_two
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a') :
    (Q Rg a').relIndex (Z Rg a) = 2 ∧ (Q Rg a).relIndex (Z Rg a') = 2 ∧
      Nat.card (⁅Z Rg a,Z Rg a'⁆ : Subgroup (FreeAmalgam Rg)) = 2 :=
  full_point_four_critical_indices_two_at h e hz hk
    (point_image_distance_eq_four h e hz hk u hR) u
    (full_point_image_of_contained h e hz hk u hR) p

omit hk in
include h e hz in
/-- Whole-core application of the large-image distance-four exclusion.
The remaining point branch has uniformly small critical images; plane and
Sylow images and both moving central covers remain literal alternatives. -/
theorem coreExhaustion_or_cubic_point_small_images :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          ∀ (a a' : Vertex Rg) (_p : CriticalPath Rg (sourceGeometry h) a a'),
            (Q Rg a').relIndex (Z Rg a) = 2 ∧
            (Q Rg a).relIndex (Z Rg a') = 2 ∧
            Nat.card (⁅Z Rg a,Z Rg a'⁆ : Subgroup (FreeAmalgam Rg)) = 2) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_radical_cases h e hz with
    hx | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ?_⟩
    exact ⟨hpoint.2,hpoint.1,fun _ _ p => point_image_critical_indices_two h e hz hk u hpoint.2.le p⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the uniform critical-image reduction,
retaining the original nonsylow radical and cubic kernel. -/
theorem rankTwo_or_cubic_point_small_images :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          ∀ (a a' : Vertex Rg) (_p : CriticalPath Rg (sourceGeometry h) a a'),
            (Q Rg a').relIndex (Z Rg a) = 2 ∧
            (Q Rg a).relIndex (Z Rg a') = 2 ∧
            Nat.card (⁅Z Rg a,Z Rg a'⁆ : Subgroup (FreeAmalgam Rg)) = 2) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_point_small_images h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
