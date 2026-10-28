module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MidpointSlice
public import Theory.GroupAction.FaithfulSixteen

/-!
# The full original core in the forward slice kernel

The forward slice kernel is normal in the starting stabilizer and contains
the common two-kernel. Its quotient in the starting two-core is therefore
a quotient of a two-subgroup of the neighboring marked S₆. Such a quotient
has no automorphism of order five: below order sixteen this follows from
orbit counting; at order sixteen it is a nonabelian Sylow subgroup, whereas
a nontrivial five-action would make its nontrivial center the whole group.
The symmetric-six action theorem consequently makes the original component
fix that quotient. Thus the entire component commutator lies in the forward
kernel, for every radical image and either central cover.

The source forward slice now bounds the full core's second-vertex image by
two and bounds its commutator with the selected span by the starting seed.
Together with the midpoint calculation this removes the separate core-index
premise from the full-core supplement and common-core commutator bound.
Transport to the opposite critical path retains its actual conjugators:
the original midpoint orbit gives its nonabelian span, and the same two
slices give its core supplement. The terminal application therefore needs
no separate core-index, endpoint-action or opposite-supplement hypotheses.

The source orbit and slice selection, and fixedness of the two selected
derived subgroups, remain explicit. Neither terminal distance exclusion nor
the unconditional replacement-distance theorem is proved here. These and
the shifted-path and R₄/R₆ arguments remain with this task; unconditional
whole-core reconstruction remains with qt-e-ms-small-a6-reconstruction.

Source: MS93 (3.10), pp.879--881, and (5.12), pp.925--927. The core-kernel
argument extends the project's SymplecticSetup.ForwardCoreKernel to all
radical images by replacing its order-eight estimate with the literal
symmetric-six two-section calculation. The original core, natural quotient
and possible central line of the order-thirty-two cover are preserved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders.Six
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

private theorem sylow_noncommutative : ¬ IsMulCommutative sylowCarrier := by
  intro hc
  let := hc
  have ha : sylowWords 1 ∈ sylowCarrier := (mem_sylowCarrier_iff _).mpr ⟨1,rfl⟩
  have hb : sylowWords 8 ∈ sylowCarrier := (mem_sylowCarrier_iff _).mpr ⟨8,rfl⟩
  have he := congrArg (fun x : sylowCarrier => (x : Equiv.Perm (Fin 6)))
    (mul_comm (⟨sylowWords 1,ha⟩ : sylowCarrier) ⟨sylowWords 8,hb⟩)
  exact (by decide : sylowWords 1 * sylowWords 8 ≠ sylowWords 8 * sylowWords 1) he

private theorem two_subgroup_card_le_sixteen (A : Subgroup (Equiv.Perm (Fin 6)))
    (hA : IsPGroup 2 A) : Nat.card A ≤ 16 := by
  obtain ⟨P,hAP⟩ := hA.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 6)) P sylow
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ sylowCarrier := by
    rintro _ ⟨a,ha,rfl⟩
    change (MulAut.conj g) a ∈ (sylow : Subgroup (Equiv.Perm (Fin 6)))
    rw [←hg]
    exact mem_map_of_mem _ (hAP ha)
  have hh := card_le_of_le hle
  rwa [card_map_of_injective (MulAut.conj g).injective,card_sylowCarrier] at hh

private theorem two_subgroup_sixteen_noncommutative (A : Subgroup (Equiv.Perm (Fin 6)))
    (hA : IsPGroup 2 A) (hcard : Nat.card A = 16) : ¬ IsMulCommutative A := by
  intro hc
  let := hc
  obtain ⟨P,hAP⟩ := hA.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 6)) P sylow
  let f := (MulAut.conj g).toMonoidHom
  have hle : A.map f ≤ sylowCarrier := by
    rintro _ ⟨a,ha,rfl⟩
    change (MulAut.conj g) a ∈ (sylow : Subgroup (Equiv.Perm (Fin 6)))
    rw [←hg]
    exact mem_map_of_mem _ (hAP ha)
  have he : A.map f = sylowCarrier := eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective (MulAut.conj g).injective,card_sylowCarrier,hcard])
  have hcm : IsMulCommutative (A.map f) := by
    refine ⟨⟨?_⟩⟩
    rintro ⟨a,aa,ha,rfl⟩ ⟨b,bb,hb,rfl⟩
    apply Subtype.ext
    change f aa * f bb = f bb * f aa
    rw [←map_mul,←map_mul]
    exact congrArg f (congrArg Subtype.val (mul_comm (⟨aa,ha⟩ : A) ⟨bb,hb⟩))
  exact sylow_noncommutative (he ▸ hcm)

private theorem no_five_aut_of_symmetric_two_image
    (A : Subgroup (Equiv.Perm (Fin 6))) (hA : IsPGroup 2 A)
    {W : Type*} [Group W] [Finite W] (f : A →* W) (hf : Function.Surjective f) :
    ¬ 5 ∣ Nat.card (MulAut W) := by
  have hW := hA.of_surjective f hf
  have hWA : Nat.card W ≤ Nat.card A := Nat.card_le_card_of_surjective f hf
  have hA16 := two_subgroup_card_le_sixteen A hA
  by_cases hW8 : Nat.card W ≤ 8
  · exact MulAut.not_five_dvd_card_of_twoGroup_card_le_eight hW hW8
  have hW16 : Nat.card W = 16 := by
    obtain ⟨n,hn⟩ := hW.exists_card_eq
    have hnle : n ≤ 4 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      (by simpa only [←hn] using hWA.trans hA16)
    have hnge : 4 ≤ n := by
      by_contra! hh
      have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show n ≤ 3 by omega)
      omega
    norm_num [hn,show n=4 by omega]
  have hAcard : Nat.card A = 16 := by omega
  let := Fintype.ofFinite W
  let := Fintype.ofFinite A
  have hfi : Function.Injective f :=
    hf.injective_of_finite (Fintype.equivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card] using hAcard.trans hW16.symm))
  intro hfive
  have hcent := Theory.GroupAction.invariant_eq_bot_or_top_of_faithful_five
    (A := MulAut W) hfive hW16 (center W)
  have hnontrivial : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let := hnontrivial
  have hne : center W ≠ ⊥ := ne_of_gt hW.bot_lt_center
  have he : center W = ⊤ := hcent.resolve_left hne
  let := center_eq_top_iff.mp he
  apply two_subgroup_sixteen_noncommutative A hA hAcard
  refine ⟨⟨?_⟩⟩
  intro a b
  apply hfi
  simp only [map_mul,mul_comm]

private theorem residual_fixes_symmetric_two_section
    {M : Type*} [Group M] [Finite M]
    (q : M →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker) (D T : Subgroup M) [D.Normal] [T.Normal]
    (hD : D ≤ q.ker) (ψ : D →* Equiv.Perm (Fin 6))
    (hk : ψ.ker ≤ T.subgroupOf D) : ⁅D,pResidual 2 M⁆ ≤ T := by
  let W := D ⧸ T.subgroupOf D
  let π := QuotientGroup.mk' (T.subgroupOf D)
  have hπ : ψ.rangeRestrict.ker ≤ π.ker := by
    rwa [MonoidHom.ker_rangeRestrict,QuotientGroup.ker_mk']
  let f := ψ.rangeRestrict.liftOfSurjective ψ.rangeRestrict_surjective ⟨π,hπ⟩
  have hf (x : D) : f (ψ.rangeRestrict x) = π x := by
    simp [f,MonoidHom.liftOfSurjective]
  have hfs : Function.Surjective f := by
    intro w
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (T.subgroupOf D) w
    exact ⟨ψ.rangeRestrict x,hf x⟩
  have hψ : IsPGroup 2 ψ.range :=
    (hker.to_le hD).of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hno : ¬ 5 ∣ Nat.card (MulAut W) :=
    no_five_aut_of_symmetric_two_image ψ.range hψ f hfs
  obtain ⟨a,ha⟩ := exists_quotient_conjugation_action (⊤ : Subgroup M) D T
    le_normalizer_of_normal le_normalizer_of_normal inferInstance
  let action := a.comp (topEquiv : (⊤ : Subgroup M) ≃* M).symm.toMonoidHom
  have hp := MonoidHom.isPGroup_range_of_symmetricSix_quotient q hq hker action hno
  have hres := pResidual_le_ker_of_isPGroup 2 action.rangeRestrict hp
  rw [MonoidHom.ker_rangeRestrict] at hres
  rw [commutator_comm]
  apply commutator_le.mpr
  intro m hm x hx
  have htriv : a ⟨m,mem_top _⟩ = 1 := hres hm
  have hfix := ha ⟨m,mem_top _⟩ ⟨x,hx⟩
  rw [htriv] at hfix
  have hmem := QuotientGroup.eq_iff_div_mem.mp hfix.symm
  change m*x*m⁻¹/x ∈ T at hmem
  simpa only [div_eq_mul_inv,commutatorElement_def] using hmem

omit [Finite G] in
private theorem core_slice_comap_normal (J : Subgroup (FreeAmalgam d.radical))
    (hJ : stabilizer d.radical (alpha d.radical) ≤ normalizer (J : Set (FreeAmalgam d.radical))) :
    (J.comap (embedM d.radical)).Normal := by
  constructor
  intro n hn g
  change embedM d.radical (g*n*g⁻¹) ∈ J
  rw [map_mul,map_mul,map_inv]
  exact (le_normalizer_iff.mp hJ (embedM d.radical g)
    (by change embedM d.radical g ∈ stabilizer d.radical (mVertex d.radical 1)
        rw [stabilizer_m_base]; exact ⟨g,rfl⟩)) _ hn

include s in
/-- The full component commutator fixes the forward Baumann slice, for all
radical images and both central covers. -/
theorem core_commutator_le_forward_kernel
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤
      Q d.radical (alpha d.radical) ⊓ centralizer
        (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
          ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert 2
  let T₀ := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical (p.walk.getVert 1) = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical (p.walk.getVert 1) at hh
    cases he : color d.radical (p.walk.getVert 1) <;> simp_all
  have hQaGc : Q d.radical (alpha d.radical) ≤ stabilizer d.radical c :=
    (Q_le_adjacent_h d.radical ht hat).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hQT : Q d.radical (alpha d.radical) ⊓ Q d.radical c ≤ T₀ := by
    apply le_inf inf_le_left
    exact (inf_le_right.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c hcol)))).trans
        (centralizer_le (inf_le_left.trans (DistanceEight.U_le_Z d.radical c)))
  let f := embedM d.radical
  let D := (Q d.radical (alpha d.radical)).comap f
  let T := T₀.comap f
  let : D.Normal := core_slice_comap_normal _ (Q_normalized d.radical _)
  let : T.Normal := core_slice_comap_normal _ (selected_forward_kernel_normalized hb rfl hat hct)
  have hDm : D.map f = Q d.radical (alpha d.radical) := map_comap_eq_self
    ((show Q d.radical (alpha d.radical) ≤ stabilizer d.radical (alpha d.radical)
      from fun _ hx => hx.1).trans_eq (stabilizer_m_base d.radical))
  have hTm : T.map f = T₀ := map_comap_eq_self
    ((show T₀ ≤ Q d.radical (alpha d.radical) from inf_le_left).trans
      ((show Q d.radical (alpha d.radical) ≤ stabilizer d.radical (alpha d.radical)
        from fun _ hx => hx.1).trans_eq (stabilizer_m_base d.radical)))
  have hD : D ≤ s.projection.ker := by
    rw [s.projection_kernel]
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rw [hDm,←Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)]
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc c hcol
  let j : d.overgroup →* stabilizer d.radical c :=
    i.codRestrict _ (fun x => hir ▸ (show i x ∈ i.range from ⟨x,rfl⟩))
  have hj : Function.Bijective j := by
    constructor
    · intro x y he
      exact hi (congrArg Subtype.val he)
    · rintro ⟨x,hx⟩
      obtain ⟨y,hy⟩ := (show x ∈ i.range from hir.symm ▸ hx)
      exact ⟨y,Subtype.ext hy⟩
  let E := MulEquiv.ofBijective j hj
  let k : D →* stabilizer d.radical c :=
    (f.comp D.subtype).codRestrict _ (fun x => hQaGc x.property)
  let ψ : D →* Equiv.Perm (Fin 6) := s.projection.comp (E.symm.toMonoidHom.comp k)
  have hk : ψ.ker ≤ T.subgroupOf D := by
    intro x hx
    have hproj : E.symm (k x) ∈ pCore 2 d.overgroup := by
      rw [←s.projection_kernel]
      exact hx
    have he : i (E.symm (k x)) = f x.val :=
      congrArg Subtype.val (E.apply_symm_apply (k x))
    have hQc : f x.val ∈ Q d.radical c := by
      rw [←hiQ,←he]
      exact mem_map_of_mem i hproj
    exact hQT ⟨x.property,hQc⟩
  have hp : IsPGroup 2 s.projection.ker := s.projection_kernel.symm ▸ pCore_isPGroup
  have hh := map_mono (f := f)
    (residual_fixes_symmetric_two_section s.projection s.surjective hp D T hD ψ hk)
  rw [map_commutator,hDm,hTm] at hh
  simpa only [f,Ltilde_alpha] using hh

include s in
/-- The source forward slice controls the second-vertex image of the full
original component commutator; no additional core-index premise is needed. -/
theorem core_index_le_two_of_forward_slice
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    (Q d.radical (p.walk.getVert 2)).relIndex
      ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤ 2 := by
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  have hCT := core_commutator_le_forward_kernel s hc hb p
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite T := Finite.of_injective
    (inclusion (inf_le_left.trans (show Q d.radical (alpha d.radical) ≤
      stabilizer d.radical (alpha d.radical) from fun _ hx => hx.1))) (inclusion_injective _)
  exact (relIndex_le_of_le_right hCT index_ne_zero_of_finite).trans
    (selected_span_index_of_forward_slice s hc hb p hslice).1

/-- The selected span commutes with the full original core modulo the
starting seed. The source forward slice is the only extra input. -/
theorem selected_span_core_commutator_le_seed_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆⁆ ≤
        Z d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  exact (commutator_mono le_rfl (core_commutator_le_forward_kernel s hc hb p)).trans
    (selected_span_kernel_commutator_knownSimple (e := e) (hz := hz) (hn := hn) hb p hslice).1

/-- The two actual midpoint slices supply both the full-core index and its
endpoint action. The source-selected span then supplements the entire core
and has the same moved derived subgroup. -/
theorem selected_core_supplement_of_midpoint_slices_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (he : act d.radical g (alpha d.radical) = a')
    (hopposite : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    let C := ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆
    let W := forwardMovedSpan d.radical (p.walk.getVert 2)
    C ≤ Z d.radical (alpha d.radical) ⊔ W ∧ ⁅C,C⁆ = ⁅W,W⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  exact selected_core_supplement_of_midpoint_slice_knownSimple (e := e) (hz := hz) (hn := hn)
    hb p hnonabelian (core_index_le_two_of_forward_slice s hc hb2 p hslice) g hg he hopposite

/-- The literal common-kernel commutator estimate uses both midpoint slices;
the separate index and endpoint-action assumptions have been discharged. -/
theorem selected_core_cross_bound_of_midpoint_slices_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (he : act d.radical g (alpha d.radical) = a')
    (hopposite : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    let C := ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆
    ⁅Q d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2),C⁆ ≤ ⁅C,C⁆ := by
  apply selected_core_cross_commutator_of_supplement (by omega : 2 < replacementDistance h d) p hfixed
  exact (selected_core_supplement_of_midpoint_slices_knownSimple (e := e) (hz := hz) (hn := hn)
    hb p hnonabelian hslice g hg he hopposite).1

/-- Transport of the full-core supplement retains the literal midpoint orbit,
both slices and the selected span at an arbitrary starting vertex. -/
theorem selected_core_supplement_of_midpoint_slices_at_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) a,
      localZSpan d.radical (p.walk.getVert 2) a⁆ ≠ ⊥)
    (hslice : (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (he : act d.radical g a = a')
    (hopposite : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    ⁅Q d.radical a,Ltilde d.radical a⁆ ≤ Z d.radical a ⊔
      ⁅localZSpan d.radical (p.walk.getVert 2) a,Ltilde d.radical a⁆ := by
  obtain ⟨x,rfl⟩ := exists_mVertex_of_color d.radical p.start_color
  have hxbase : act d.radical x⁻¹ (mVertex d.radical x) = alpha d.radical := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have base := selected_core_supplement_of_midpoint_slices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb (a' := act d.radical x⁻¹ a')
  dsimp only [forwardMovedSpan] at base
  rw [←hxbase] at base
  let k := x*g*x⁻¹
  have hrestore (v : Vertex d.radical) : act d.radical x (act d.radical x⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hkg : k ∈ stabilizer d.radical ((p.act x⁻¹).walk.getVert 2) := by
    change k ∈ stabilizer d.radical ((actWalk d.radical x⁻¹ p.walk).getVert 2)
    rw [actWalk_getVert,stabilizer_act]
    exact ⟨g,hg,by simp only [inv_inv]; rfl⟩
  have hke : act d.radical k (act d.radical x⁻¹ (mVertex d.radical x)) = act d.radical x⁻¹ a' := by
    simp only [k,act_mul]
    rw [hrestore,he]
  have hci : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by have hl : p.walk.length = replacementDistance h d := p.length_eq_b; omega)).mpr (by decide)
  have hnon : ⁅localZSpan d.radical ((p.act x⁻¹).walk.getVert 2)
        (act d.radical x⁻¹ (mVertex d.radical x)),
      localZSpan d.radical ((p.act x⁻¹).walk.getVert 2)
        (act d.radical x⁻¹ (mVertex d.radical x))⁆ ≠ ⊥ := by
    change ⁅localZSpan d.radical ((actWalk d.radical x⁻¹ p.walk).getVert 2) _,
      localZSpan d.radical ((actWalk d.radical x⁻¹ p.walk).getVert 2) _⁆ ≠ ⊥
    rw [actWalk_getVert,LocalCommutator.CriticalCase.localZSpan_act,←map_commutator]
    intro hh
    exact hnonabelian (map_eq_bot_iff_of_injective _ (MulAut.conj _).injective |>.mp hh)
  have hsi : (B d.radical (act d.radical x⁻¹ (mVertex d.radical x))
        ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical ((p.act x⁻¹).walk.getVert 2)) ≤ 2 := by
    change (B d.radical _ _).relIndex
      (U d.radical ((actWalk d.radical x⁻¹ p.walk).getVert 2)) ≤ 2
    rw [actWalk_getVert,Escape.PairingControl.FirstPairing.B_act
      (by omega : 2 < replacementDistance h d) _ _ p.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hslice
  have hki : (B d.radical ((p.act x⁻¹).walk.getVert 2)
        ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical x⁻¹ a')) ≤ 2 := by
    change (B d.radical ((actWalk d.radical x⁻¹ p.walk).getVert 2) _).relIndex _ ≤ 2
    simp only [actWalk_getVert]
    rw [Escape.PairingControl.FirstPairing.B_act
      (by omega : 2 < replacementDistance h d) _ _ hci,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hopposite
  have hh := (base (p.act x⁻¹) hnon hsi k hkg hke hki).1
  change ⁅Q d.radical (act d.radical x⁻¹ (mVertex d.radical x)),
      Ltilde d.radical (act d.radical x⁻¹ (mVertex d.radical x))⁆ ≤
    Z d.radical (act d.radical x⁻¹ (mVertex d.radical x)) ⊔
      ⁅localZSpan d.radical ((actWalk d.radical x⁻¹ p.walk).getVert 2)
        (act d.radical x⁻¹ (mVertex d.radical x)),
        Ltilde d.radical (act d.radical x⁻¹ (mVertex d.radical x))⁆ at hh
  rw [actWalk_getVert] at hh
  have hm := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hh
  simpa only [map_commutator,Subgroup.map_sup,←Q_act,←Ltilde_act,←Z_act,
    ←LocalCommutator.CriticalCase.localZSpan_act,hrestore] using hm

/-- Both opposite core estimates follow from the original midpoint orbit
and its two slices. The source still has to select that orbit and those
slices, and to prove fixedness of the two selected derived subgroups. -/
theorem selected_terminal_false_of_midpoint_slices_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hfixed : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≤
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hfixedOpp : ⁅localZSpan d.radical (alpha d.radical) (p.walk.getVert 2),
      localZSpan d.radical (alpha d.radical) (p.walk.getVert 2)⁆ ≤
      centralizer (Ltilde d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)))
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (he : act d.radical g (alpha d.radical) = a')
    (hopposite : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let c := p.walk.getVert 2
  have hci : color d.radical c = false :=
    (p.vertex_color (by have hl : p.walk.length = replacementDistance h d := p.length_eq_b; omega)).mpr (by decide)
  have hi := (midpoint_slice_eq_reverse_kernel s hc hb p g hg he hopposite).2.2.1
  have hcomm := (midpoint_common_kernel_endpoint_commutator s hc hb p g hg he hopposite).2.le
  have hcommZ := hcomm.trans (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
    (DistanceEight.U_le_Z d.radical _))
  have hPQ := (selected_span_le_forward_kernel (h := h) hb2 p).trans inf_le_left
  have hCQ : ⁅Q d.radical (alpha d.radical),Ltilde d.radical (alpha d.radical)⁆ ≤
      Q d.radical (alpha d.radical) := (core_commutator_le_forward_kernel s hc hb2 p).trans inf_le_left
  have hnonOpp : ⁅localZSpan d.radical (alpha d.radical) c,
      localZSpan d.radical (alpha d.radical) c⁆ ≠ ⊥ := by
    have hstart : Z d.radical (alpha d.radical) ≤ localZSpan d.radical (alpha d.radical) c :=
      Z_le_localZSpan d.radical _ _
    have hend : Z d.radical a' ≤ localZSpan d.radical (alpha d.radical) c := by
      rw [←he,Z_act]
      exact (map_mono hstart).trans_eq (mem_normalizer_iff_map_conj_eq.mp
        (localZSpan_normalized d.radical (alpha d.radical) c
          ((stabilizer d.radical c).inv_mem hg)))
    intro hn
    have hcrit := critical_noncommutation d.radical (replacementGeometry h d)
      (edgeCentralizerCondition s hc) (alpha d.radical) rfl
      (by rw [(replacementGeometry h d).distance_constant _ rfl]; exact replacementDistance_pos h d)
      p.critical
    exact hcrit (le_bot_iff.mp ((commutator_mono hstart hend).trans_eq hn))
  obtain ⟨_,x,hx,q,_,hq,_⟩ := selected_span_conjugate_critical_path (h := h) hb2 p hnonabelian
  have hBn := Escape.Propagation.Rigidity.B_normalized
    (geometry := replacementGeometry h d) hb2 c hci
  have hBm : (B d.radical c ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical c ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (hBn ((stabilizer d.radical c).inv_mem hg))
  have hforwardOpp : (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (q.walk.getVert 2)) ≤ 2 := by
    rw [hq]
    have hh := hopposite
    have hUe : U d.radical a' = (U d.radical (alpha d.radical)).map
        (MulAut.conj g⁻¹).toMonoidHom := by rw [←he,U_act]
    rw [hUe,←hBm,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hh
    exact hh
  have hBna := Escape.Propagation.Rigidity.B_normalized
    (geometry := replacementGeometry h d) hb2 (alpha d.radical) rfl
  have hBma : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (hBna ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  have hoppositeOpp : (B d.radical (q.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x c)) ≤ 2 := by
    rw [hq,U_act,←hBma,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hslice
  have hsupp := selected_core_supplement_of_midpoint_slices_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q (by simpa only [hq] using hnonOpp)
    hforwardOpp x (hq.symm ▸ hx) rfl hoppositeOpp
  rw [hq] at hsupp
  exact selected_natural_terminal_false_of_core_estimates_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 p hnonabelian (by omega) hfixed
    (selected_span_index_of_forward_slice s hc hb2 p hslice).2
    ((commutator_mono (inf_le_inf_right _ hPQ) le_rfl).trans hcommZ)
    (core_index_le_two_of_forward_slice s hc hb2 p hslice)
    ((commutator_mono (inf_le_inf_right _ hCQ) le_rfl).trans hcommZ)
    hfixedOpp hsupp

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
