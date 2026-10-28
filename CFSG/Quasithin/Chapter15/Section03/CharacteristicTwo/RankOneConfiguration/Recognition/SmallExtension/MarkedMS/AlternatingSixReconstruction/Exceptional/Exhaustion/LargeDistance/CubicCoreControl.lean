module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOppositeTransfer
public import Theory.GroupAction.SymmetricSixSmallSection
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupAction.FaithfulSixteen
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport
/-!
# Whole-core comparison on the original cubic graph

The full component commutator lies in the forward Baumann-slice kernel
at every critical path, for every radical image and both moving covers.
The kernel contains the common two-core intersection. Its quotient in the
starting two-core is a quotient of a two-subgroup of the neighboring S₆,
and therefore has no automorphism of order five. The normal-over-core
dichotomy and two-perfectness force the original component to fix it.
Only a two-subgroup's intersection with the projection kernel E is placed
in Q; the nontrivial cubic quotient E/Q is retained.

A small forward slice consequently controls the full core's opposite image
and its action on the selected span. For the core supplement, write the
selected span as its seed times its component-moved subgroup. Nonabelianness
forces the latter to escape the opposite core. The index-two endpoint
action then contracts the whole core into the starting seed times that
moved subgroup. The original cubic no-supplement theorem supplies this
contraction without treating E as a two-group or assuming a natural marking
of the selected span.

Two literal midpoint slices discharge the index and endpoint-action inputs.
The entire core's derived subgroup is then contained in the selected
central line and has order at most two. The whole-core and literal C.1.32
consumers keep the same projection, embeddings and both full covers.
Coordinated slice selection, the opposite common-core commutator bound,
the terminal contradictions and both final reconstructions remain required.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.10)(i)--(ii), printed pp.879--881, and (5.12), pp.925--927;
Aschbacher--Smith C.1.31--32, pp.135--136.
The two-section model calculation adapts Natural.Exhaustion.LargeDistance.
SectionFive.CoreSlice; the selected supplement adapts its SelectedSpan
argument to the actual cubic kernel and original graph.
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
include h e hz hk in
private theorem component_le_kernel_of_no_five
    {A : Type*} [Group A] [Finite A] (f : M →* A)
    (hfive : ¬ 5 ∣ Nat.card A) : L.subgroupOf M ≤ f.ker := by
  let N := f.ker ⊔ pCore 2 M
  rcases normal_over_core_dichotomy h e N le_sup_right with hsmall | hcomp
  · have hi : (π).ker.index ∣ f.ker.index := index_dvd_of_le (by
      rw [CubicAction.projection_kernel]
      exact le_sup_left.trans hsmall)
    rw [index_ker,index_ker,MonoidHom.range_eq_top.mpr
      (CubicEven.projection_surjective h e hz hk),card_top,
      Nat.card_perm,Nat.card_fin] at hi
    exact (hfive ((show 5 ∣ Nat.factorial 6 by decide).trans
      (hi.trans f.range.card_subgroup_dvd_card))).elim
  · apply le_normal_of_isPPerfect_of_le_sup_pGroup (L.subgroupOf M) f.ker
      (pCore 2 M) _ pCore_isPGroup hcomp
    rw [←h.relative_residual]
    exact isPPerfect_pResidual 2

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

omit [Finite G] in
private theorem core_kernel_comap_normal (N : Subgroup (FreeAmalgam Rg))
    (hN : stabilizer Rg (alpha Rg) ≤ normalizer (N : Set (FreeAmalgam Rg))) :
    (N.comap (embedM Rg)).Normal := by
  constructor
  intro n hn g
  change embedM Rg (g*n*g⁻¹) ∈ N
  rw [map_mul,map_mul,map_inv]
  exact le_normalizer_iff.mp hN (embedM Rg g)
    (by rw [show alpha Rg = mVertex Rg 1 from rfl,stabilizer_m_base]; exact ⟨g,rfl⟩) _ hn

include h e hz hk in
private theorem component_fixes_symmetric_two_section
    (D T : Subgroup M) [D.Normal] [T.Normal]
    (hD : D ≤ pCore 2 M) (ψ : D →* S)
    (hψ : ψ.ker ≤ T.subgroupOf D) : ⁅D,L.subgroupOf M⁆ ≤ T := by
  let W := D ⧸ T.subgroupOf D
  let q := QuotientGroup.mk' (T.subgroupOf D)
  have hq : ψ.rangeRestrict.ker ≤ q.ker := by
    rwa [MonoidHom.ker_rangeRestrict,QuotientGroup.ker_mk']
  let f := ψ.rangeRestrict.liftOfSurjective ψ.rangeRestrict_surjective ⟨q,hq⟩
  have hf (x : D) : f (ψ.rangeRestrict x) = q x := by
    simp [f,MonoidHom.liftOfSurjective]
  have hfs : Function.Surjective f := by
    intro w
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (T.subgroupOf D) w
    exact ⟨ψ.rangeRestrict x,hf x⟩
  have htwo : IsPGroup 2 ψ.range :=
    (pCore_isPGroup.to_le hD).of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hno := no_five_aut_of_symmetric_two_image ψ.range htwo f hfs
  obtain ⟨a,ha⟩ := exists_quotient_conjugation_action (⊤ : Subgroup M) D T
    le_normalizer_of_normal le_normalizer_of_normal inferInstance
  let action := a.comp (topEquiv : (⊤ : Subgroup M) ≃* M).symm.toMonoidHom
  have hker := component_le_kernel_of_no_five h e hz hk action hno
  rw [commutator_comm]
  apply commutator_le.mpr
  intro m hm x hx
  have htriv : a ⟨m,mem_top _⟩ = 1 := hker hm
  have hfix := ha ⟨m,mem_top _⟩ ⟨x,hx⟩
  rw [htriv] at hfix
  have hmem := QuotientGroup.eq_iff_div_mem.mp hfix.symm
  change m*x*m⁻¹/x ∈ T at hmem
  simpa only [div_eq_mul_inv,commutatorElement_def] using hmem

include h e hz hk in
/-- The whole original component commutator fixes the selected forward slice,
 for every radical image and both central covers. -/
theorem core_commutator_le_forward_kernel
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆ ≤
      Q Rg (alpha Rg) ⊓ centralizer
        (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
          ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let T₀ := Q Rg (alpha Rg) ⊓ centralizer
    (U Rg c ⊓ B Rg (alpha Rg)
      ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
  have hb := distance_gt_two h e hz hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent Rg c (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have ht : color Rg (p.walk.getVert 1) = true := by
    have hn := adjacent_color_ne Rg hat
    change false ≠ color Rg (p.walk.getVert 1) at hn
    cases hh : color Rg (p.walk.getVert 1) <;> simp_all
  have hQaGc : Q Rg (alpha Rg) ≤ stabilizer Rg c :=
    (Q_le_adjacent_h Rg ht hat).trans (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hQT : Q Rg (alpha Rg) ⊓ Q Rg c ≤ T₀ := by
    apply le_inf inf_le_left
    exact (inf_le_right.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c hc)))).trans
        (centralizer_le (inf_le_left.trans (DistanceEight.U_le_Z Rg c)))
  let f := embedM Rg
  let D₀ := (Q Rg (alpha Rg)).comap f
  let T := T₀.comap f
  let : D₀.Normal := core_kernel_comap_normal _ (Q_normalized Rg _)
  let : T.Normal := core_kernel_comap_normal _
    (selected_forward_kernel_normalized (h := h) hb rfl hat hct)
  have hDm : D₀.map f = Q Rg (alpha Rg) := map_comap_eq_self
    ((show Q Rg (alpha Rg) ≤ stabilizer Rg (alpha Rg) from fun _ hx => hx.1).trans_eq
      (stabilizer_m_base Rg))
  have hTm : T.map f = T₀ := map_comap_eq_self
    ((show T₀ ≤ Q Rg (alpha Rg) from inf_le_left).trans
      ((show Q Rg (alpha Rg) ≤ stabilizer Rg (alpha Rg) from fun _ hx => hx.1).trans_eq
        (stabilizer_m_base Rg)))
  have hD : D₀ ≤ pCore 2 M := by
    apply (map_le_map_iff_of_injective (embedM_injective Rg)).mp
    rw [hDm,←Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le]
  obtain ⟨i,hi,hir,hiQ,_,_,_⟩ := graph_cover h e hz hk c hc
  let j : M →* stabilizer Rg c :=
    i.codRestrict _ (fun x => hir ▸ (show i x ∈ i.range from ⟨x,rfl⟩))
  have hj : Function.Bijective j := by
    constructor
    · intro x y he
      exact hi (congrArg Subtype.val he)
    · rintro ⟨x,hx⟩
      obtain ⟨y,hy⟩ := (show x ∈ i.range from hir.symm ▸ hx)
      exact ⟨y,Subtype.ext hy⟩
  let E := MulEquiv.ofBijective j hj
  let k : D₀ →* stabilizer Rg c :=
    (f.comp D₀.subtype).codRestrict _ (fun x => hQaGc x.property)
  let τ := E.symm.toMonoidHom.comp k
  let ψ : D₀ →* S := (π).comp τ
  have hτtwo : IsPGroup 2 τ.range :=
    (pCore_isPGroup.to_le hD).of_surjective τ.rangeRestrict τ.rangeRestrict_surjective
  have hτQ : τ.range ⊓ extensionKernel h ≤ pCore 2 M :=
    two_subgroup_le_core_of_le_extensionKernel h hz _
      (hτtwo.to_le inf_le_left) inf_le_right
  have hψ : ψ.ker ≤ T.subgroupOf D₀ := by
    intro x hx
    have hproj : τ x ∈ extensionKernel h := by
      rw [←CubicAction.projection_kernel h e hz hk]
      exact hx
    have hxQ : τ x ∈ pCore 2 M := hτQ ⟨⟨x,rfl⟩,hproj⟩
    have he : i (τ x) = f x.val := congrArg Subtype.val (E.apply_symm_apply (k x))
    have hQc : f x.val ∈ Q Rg c := by
      rw [←hiQ,←he]
      exact mem_map_of_mem i hxQ
    exact hQT ⟨x.property,hQc⟩
  have hh := map_mono (f := f)
    (component_fixes_symmetric_two_section h e hz hk D₀ T hD ψ hψ)
  rw [map_commutator,hDm,hTm] at hh
  simpa only [f,←h.relative_residual,←Ltilde_alpha] using hh

include h e hz hk in
/-- The same whole-core containment at every component vertex, transported
 along the literal critical path and the original conjugation action. -/
theorem core_commutator_le_forward_kernel_at
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a') :
    ⁅Q Rg a,Ltilde Rg a⁆ ≤ Q Rg a ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg a ((sourceGeometry h).Z_normal _) :
        Set (FreeAmalgam Rg)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := core_commutator_le_forward_kernel h e hz hk
    (a' := act Rg g⁻¹ a')
  rw [←hbase] at base
  have hh := base (p.act g⁻¹)
  have hb := distance_gt_two h e hz hk
  simp only [CriticalPath.act,actWalk_getVert,Q_act,Ltilde_act,U_act,
    Escape.PairingControl.FirstPairing.B_act hb g⁻¹ a p.start_color,inv_inv] at hh
  rw [←map_commutator] at hh
  have hc := hh.trans inf_le_right
  change (⁅Q Rg a,Ltilde Rg a⁆).map (MulAut.conj g).toMonoidHom ≤
    centralizer (((U Rg (p.walk.getVert 2)).map (MulAut.conj g).toMonoidHom ⊓
      (B Rg a ((sourceGeometry h).Z_normal _)).map (MulAut.conj g).toMonoidHom :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) at hc
  rw [←Subgroup.map_inf _ _ _ (MulAut.conj g).injective] at hc
  apply le_inf
  · exact (map_le_map_iff_of_injective (MulAut.conj g).injective).mp (hh.trans inf_le_left)
  · change ⁅Q Rg a,Ltilde Rg a⁆ ≤ centralizer
      ((U Rg (p.walk.getVert 2) ⊓ B Rg a ((sourceGeometry h).Z_normal _) :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply (map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)
    rw [Subgroup.map_bot,map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc


include h e hz hk in
/-- A small source slice now bounds the full component commutator's opposite
 image and its action on the same selected span. No whole-core bound is
 assumed. -/
theorem core_estimates_of_forward_slice
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    let C := ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆
    (Q Rg (p.walk.getVert 2)).relIndex C ≤ 2 ∧
      ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),C⁆ ≤ Z Rg (alpha Rg) ∧
      Nat.card (⁅U Rg (p.walk.getVert 2),C⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 ∧
      ⁅U Rg (p.walk.getVert 2),C⁆ ≤ Z Rg (p.walk.getVert 1) := by
  let C := ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆
  let T := Q Rg (alpha Rg) ⊓ centralizer
    (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
      ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
  have hb := distance_gt_two h e hz hk
  have hCT := core_commutator_le_forward_kernel h e hz hk p
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite T := Finite.of_injective
    (inclusion (inf_le_left.trans (show Q Rg (alpha Rg) ≤
      stabilizer Rg (alpha Rg) from fun _ hx => hx.1))) (inclusion_injective _)
  have hUG : U Rg (p.walk.getVert 2) ≤ stabilizer Rg (alpha Rg) :=
    (DistanceEight.U_le_Z Rg _).trans ((Z_le_localZSpan Rg _ _).trans
      ((localZSpan_le_V Rg (by
        rw [SimpleGraph.dist_comm,p.dist_start (by
          have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
          omega)])).trans ((sourceGeometry h).V_local _ rfl hb)))
  have hTG : T ≤ stabilizer Rg (alpha Rg) :=
    inf_le_left.trans (show Q Rg (alpha Rg) ≤ stabilizer Rg (alpha Rg) from fun _ hx => hx.1)
  let : Finite (⁅U Rg (p.walk.getVert 2),T⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion ((Subgroup.commutator_le_sup _ _).trans
      (sup_le hUG hTG))) (inclusion_injective _)
  have hline := selected_forward_kernel_line h e hz hk hb p hslice
  have hcomm := commutator_mono (le_rfl (a := U Rg (p.walk.getVert 2))) hCT
  refine ⟨(relIndex_le_of_le_right hCT index_ne_zero_of_finite).trans
    (selected_span_index_of_forward_slice h e hz hk hb p hslice).1,?_,?_,?_⟩
  · exact (commutator_mono le_rfl hCT).trans
      (selected_span_kernel_commutator h e hz hk hb p hslice).1
  · exact (card_le_of_le hcomm).trans hline.1
  · exact hcomm.trans hline.2

include h e hz hk in
private theorem cubic_residual_moved_le_of_odd_small_index
    (Q₀ U W D₀ A : Subgroup M) [Q₀.Normal] [U.Normal] [W.Normal]
    (hWQ : W ≤ Q₀) (hDQ : D₀ ≤ Q₀) (hi : D₀.relIndex Q₀ ≤ 2)
    (hmove : ⁅Q₀,L.subgroupOf M⁆ = Q₀)
    (hDA : ⁅D₀,A⁆ ≤ U) (hnot : ¬ W ≤ D₀)
    (hodd : ¬ A.map π ≤ alternatingGroup (Fin 6)) : Q₀ ≤ U ⊔ W := by
  have hjoin : D₀⊔W≤Q₀ := sup_le hDQ hWQ
  have hlow : 2≤D₀.relIndex (D₀⊔W) := by
    have h0 : D₀.relIndex (D₀⊔W)≠0 := index_ne_zero_of_finite
    have h1 : D₀.relIndex (D₀⊔W)≠1 := fun he =>
      hnot (le_sup_right.trans (relIndex_eq_one.mp he))
    omega
  have hgen : D₀⊔W=Q₀ := by
    have he := relIndex_mul_relIndex D₀ (D₀⊔W) Q₀ le_sup_left hjoin
    have hi' : 2*(D₀⊔W).relIndex Q₀≤2 := (Nat.mul_le_mul_right _ hlow).trans (by rw [he]; exact hi)
    have h0 : (D₀⊔W).relIndex Q₀≠0 := index_ne_zero_of_finite
    exact le_antisymm hjoin (relIndex_eq_one.mp (by omega))
  let N := U⊔W
  let q := QuotientGroup.mk' N
  let C := (centralizer (Q₀.map q:Set (M⧸N))).comap q
  let : (Q₀.map q).Normal := (inferInstance : Q₀.Normal).map q (QuotientGroup.mk'_surjective N)
  let : C.Normal := inferInstance
  have hDAq : D₀.map q≤centralizer (A.map q:Set (M⧸N)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    exact hDA.trans le_sup_left
  have hWq : W.map q=⊥ := (Subgroup.map_eq_bot_iff _).mpr (by
    rw [QuotientGroup.ker_mk']
    exact le_sup_right)
  have hQAq : Q₀.map q≤centralizer (A.map q:Set (M⧸N)) := by
    rw [←hgen,Subgroup.map_sup,hWq,sup_bot_eq]
    exact hDAq
  have hAC : A≤C := (map_le_iff_le_comap).mp (le_centralizer_iff.mpr hQAq)
  let : (C.map π).Normal := (inferInstance : C.Normal).map π (CubicEven.projection_surjective h e hz hk)
  have hoddC : ¬C.map π≤alternatingGroup (Fin 6) := fun he => hodd ((map_mono hAC).trans he)
  have hne : C.map π≠⊥ := fun he => hoddC (he ▸ bot_le)
  have hAlt : alternatingGroup (Fin 6)≤C.map π :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) ((nontrivial_iff_ne_bot _).mpr hne)
  have htop : C.map π=⊤ := by
    have hd : (C.map π).index∣2 :=
      (alternatingGroup.index_eq_two (α:=Fin 6)) ▸ index_dvd_of_le hAlt
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1|h2
    · exact index_eq_one.mp h1
    · exact (hoddC ((Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2) ▸ le_rfl)).elim
  have hcover : C⊔(π).ker=⊤ := by
    have hh := congrArg (fun J:Subgroup (Equiv.Perm (Fin 6)) => J.comap π) htop
    simpa only [comap_map_eq,comap_top] using hh
  have hNE : C ⊔ extensionKernel h = ⊤ := by
    rwa [CubicAction.projection_kernel h e hz hk] at hcover
  have hE := extensionKernel_no_supplement h C (hNE ▸ le_top)
  rw [extensionKernel_twoCore h] at hE
  have hCQtop : C ⊔ pCore 2 M = ⊤ := by
    apply top_unique
    rw [←hNE]
    exact sup_le le_sup_left hE
  have hLC : L.subgroupOf M ≤ C :=
    le_normal_of_isPPerfect_of_le_sup_pGroup _ _ _
      (by rw [←h.relative_residual]; exact isPPerfect_pResidual 2)
      pCore_isPGroup (hCQtop ▸ le_top)
  have hCQ : C.map q≤centralizer (Q₀.map q:Set (M⧸N)) := map_comap_le _ _
  have hQC : ⁅Q₀,C⁆≤N := by
    have he := commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hCQ)
    rw [←map_commutator] at he
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
  rw [←hmove]
  exact (commutator_mono le_rfl hLC).trans hQC

include h in
/-- The selected seed and its component-moved span generate the full orbit span. -/
theorem selected_span_eq_seed_sup_moved
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    localZSpan Rg (p.walk.getVert 2) (alpha Rg) =
      Z Rg (p.walk.getVert 2) ⊔ forwardMovedSpan Rg (p.walk.getVert 2) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan Rg c (alpha Rg)
  let P₀ := forwardMovedSpan Rg c
  let B := Z Rg c ⊔ P₀
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent Rg c t :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hBP : B ≤ P := sup_le (Z_le_localZSpan Rg _ _) (forwardMovedSpan_le Rg _)
  have hLB : Ltilde Rg (alpha Rg) ≤ normalizer (B : Set (FreeAmalgam Rg)) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono hBP le_rfl).trans (show P₀ ≤ B from le_sup_right))
  have hQtG : Q Rg t ≤ stabilizer Rg (alpha Rg) :=
    fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  have hQtGc : Q Rg t ≤ stabilizer Rg c :=
    fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have hQtB : Q Rg t ≤ normalizer (B : Set (FreeAmalgam Rg)) :=
    (le_inf (hQtGc.trans (Z_normalized Rg c))
      (hQtG.trans (forwardMovedSpan_normalized Rg c))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hGB : stabilizer Rg (alpha Rg) ≤ normalizer (B : Set (FreeAmalgam Rg)) := by
    rw [←CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
      (by rw [h.relative_residual]; exact (codisjoint_subgroupOf_sup L R).eq_top) rfl hat]
    exact sup_le hLB hQtB
  apply le_antisymm _ hBP
  dsimp only [P]
  rw [localZSpan_eq_conjugates]
  apply iSup_le
  intro g
  rintro _ ⟨z,hz,rfl⟩
  exact (mem_normalizer_iff.mp (hGB ((stabilizer Rg (alpha Rg)).inv_mem g.property)) z).mp
    ((show Z Rg c ≤ B from le_sup_left) hz)

include h e hz hk in
/-- The original nonabelian selected span supplies the escape needed for the
 whole-core supplement. No natural-module marking of that span is assumed. -/
theorem selected_core_le_seed_sup_moved_span
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hnonabelian : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hindex : (Q Rg (p.walk.getVert 2)).relIndex
      ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆ ≤ 2)
    (hactor : ⁅⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆ ⊓
      Q Rg (p.walk.getVert 2),Z Rg a'⁆ ≤ Z Rg (alpha Rg)) :
    ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆ ≤
      Z Rg (alpha Rg) ⊔ forwardMovedSpan Rg (p.walk.getVert 2) := by

  have hPQall : localZSpan Rg (p.walk.getVert 2) (alpha Rg) ≤ Q Rg (alpha Rg) := by
    apply (localZSpan_le_V Rg _).trans
      (V_le_Q Rg (geometry := sourceGeometry h) rfl hb)
    rw [SimpleGraph.dist_comm,p.dist_start (by
      have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
      omega)]
  let c := p.walk.getVert 2
  let Q₀ := ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆
  let P₀ := forwardMovedSpan Rg c
  let D := Q₀⊓Q Rg c
  let f := embedM Rg
  let Qm := ⁅pCore 2 M,pResidual 2 M⁆
  let Um := (Z Rg (alpha Rg)).comap f
  let Wm := P₀.comap f
  let Dm := D.comap f
  let Am := (Z Rg a').comap f
  have hQf : Qm.map f=Q₀ := by
    dsimp only [Qm,Q₀,f]
    rw [map_commutator,←Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le,←Ltilde_alpha]
  have hGa : stabilizer Rg (alpha Rg)=f.range := stabilizer_m_base Rg
  have hQGa : Q Rg (alpha Rg)≤stabilizer Rg (alpha Rg) := fun _ hx => hx.1
  have hPQ : P₀≤Q Rg (alpha Rg) := (forwardMovedSpan_le Rg c).trans
    hPQall
  have hP₀Q₀ : P₀≤Q₀ := commutator_mono
    hPQall le_rfl
  have hPf : Wm.map f=P₀ := map_comap_eq_self (hPQ.trans (hQGa.trans_eq hGa))
  have hUf : Um.map f=Z Rg (alpha Rg) := map_comap_eq_self
    ((Z_le_stabilizer Rg _).trans_eq hGa)
  have hQ₀Ga : Q₀≤stabilizer Rg (alpha Rg) :=
    (le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer _).trans (Q_normalized Rg _))).trans hQGa
  have hDf : Dm.map f=D := map_comap_eq_self (inf_le_left.trans (hQ₀Ga.trans_eq hGa))
  have hAf : Am.map f=Z Rg a' := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl (sourceDistance_pos h) p.critical).trans_eq hGa)
  have hQm : Q₀.comap f=Qm := by
    rw [←hQf,comap_map_eq_self_of_injective (embedM_injective Rg)]
  let : Um.Normal := core_kernel_comap_normal _ (Z_normalized Rg _)
  let : Wm.Normal := core_kernel_comap_normal _ (forwardMovedSpan_normalized Rg _)
  have hWQ : Wm≤Qm := by rw [←hQm]; exact comap_mono hP₀Q₀
  have hDQ : Dm≤Qm := by rw [←hQm]; exact comap_mono inf_le_left
  have hi : Dm.relIndex Qm≤2 := by
    rw [relIndex_comap,hQf]
    simpa only [D,inf_relIndex_left] using hindex
  have hmove : ⁅Qm,pResidual 2 M⁆=Qm :=
    commutator_isPPerfect_idempotent _ _ (isPPerfect_pResidual 2) pCore_isPGroup le_normalizer_of_normal
  have hDA : ⁅Dm,Am⁆≤Um := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,hDf,hAf]
    exact hactor
  have hnot : ¬Wm≤Dm := by
    intro hh
    have hWD : P₀ ≤ D := by rw [←hPf,←hDf]; exact map_mono hh
    have hPc : localZSpan Rg c (alpha Rg) ≤ Q Rg c := by
      rw [selected_span_eq_seed_sup_moved (h := h) hb p]
      exact sup_le ((Z_le_VBall Rg c 2).trans
        (V_le_Q Rg (geometry := sourceGeometry h)
          ((p.vertex_color (by have hl : 2 < p.walk.length := p.length_eq_b ▸ hb; omega)).mpr
            (by decide)) hb)) (hWD.trans inf_le_right)
    obtain ⟨_,x,hx,q,_,_,_⟩ := selected_span_conjugate_critical_path h hb p hnonabelian
    have hxP : Z Rg (act Rg x c) ≤ localZSpan Rg c (alpha Rg) := by
      rw [Z_act]
      exact (map_mono (Z_le_localZSpan Rg c (alpha Rg))).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp
          (localZSpan_normalized Rg c (alpha Rg)
            ((stabilizer Rg (alpha Rg)).inv_mem hx)))
    exact critical_commutator_not_central h e hz hk q
      (((commutator_mono le_rfl (hxP.trans hPc)).trans_eq
        (Z_centralizes_Q Rg c q.start_color)).trans bot_le)
  obtain ⟨t,hswap,ht⟩ := small_critical_image_eq_swap h e hz hk p hsmall
  have hodd : ¬ Am.map π ≤ alternatingGroup (Fin 6) := by
    intro hh
    have hs := Equiv.Perm.mem_alternatingGroup.mp (hh (ht.symm ▸ mem_zpowers t))
    rw [hswap.sign_eq] at hs
    exact (by decide : (-1 : Units ℤ) ≠ 1) hs
  have hresult := cubic_residual_moved_le_of_odd_small_index h e hz hk
    Qm Um Wm Dm Am hWQ hDQ hi
    (by simpa only [h.relative_residual] using hmove) hDA hnot hodd
  have hh := map_mono (f:=f) hresult
  rwa [hQf,Subgroup.map_sup,hUf,hPf] at hh

include h in
/-- A central-seed supplement identifies the entire core's derived subgroup
with the derived subgroup of the selected moved span. -/
theorem core_derived_eq_of_supplement
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsupp : ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆ ≤
      Z Rg (alpha Rg) ⊔ forwardMovedSpan Rg (p.walk.getVert 2)) :
    ⁅⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆,
      ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆⁆ =
      ⁅forwardMovedSpan Rg (p.walk.getVert 2),
        forwardMovedSpan Rg (p.walk.getVert 2)⁆ := by
  have hPQall : localZSpan Rg (p.walk.getVert 2) (alpha Rg) ≤ Q Rg (alpha Rg) := by
    apply (localZSpan_le_V Rg _).trans
      (V_le_Q Rg (geometry := sourceGeometry h) rfl hb)
    rw [SimpleGraph.dist_comm,p.dist_start (by
      have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
      omega)]
  let A := Z Rg (alpha Rg)
  let W := forwardMovedSpan Rg (p.walk.getVert 2)
  let C := ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆
  let J := stabilizer Rg (alpha Rg)
  have hCQ : C ≤ Q Rg (alpha Rg) :=
    le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer _).trans (Q_normalized Rg _))
  have hWQ : W ≤ Q Rg (alpha Rg) :=
    (forwardMovedSpan_le Rg _).trans hPQall
  have hWC : W ≤ C := commutator_mono hPQall le_rfl
  have hAC : A ≤ centralizer (C : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg _ rfl)).trans
      (centralizer_le hCQ)
  have hAW : A ≤ centralizer (W : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg _ rfl)).trans
      (centralizer_le hWQ)
  have hJN : J ≤ normalizer ((⁅W,W⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (forwardMovedSpan_normalized Rg _ hg)]
  have hAJ : A ≤ J := Z_le_stabilizer Rg _
  have hWJ : W ≤ J := hWQ.trans (fun _ hx => hx.1)
  have hWCW : ⁅W,C⁆ ≤ ⁅W,W⁆ := by
    rw [commutator_comm]
    apply (commutator_mono hsupp le_rfl).trans
    exact commutator_sup_le_of_relative_normal J A W W ⁅W,W⁆ hJN hAJ hWJ
      ((commutator_eq_bot_iff_le_centralizer.mpr hAW).le.trans bot_le) le_rfl
  apply le_antisymm _ (commutator_mono hWC hWC)
  apply (commutator_mono hsupp le_rfl).trans
  exact commutator_sup_le_of_relative_normal J A W C ⁅W,W⁆ hJN hAJ hWJ
    ((commutator_eq_bot_iff_le_centralizer.mpr hAC).le.trans bot_le) hWCW


include h e hz hk in
/-- The two literal midpoint slices supply the core index and endpoint action
 needed by the whole-core supplement on the same nonabelian selected span. -/
theorem selected_core_supplement_of_midpoint_slices
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hnonabelian : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g (alpha Rg) = a')
    (hopposite : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a') ≤ 2) :
    ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆ ≤
      Z Rg (alpha Rg) ⊔ forwardMovedSpan Rg (p.walk.getVert 2) := by
  have hb := distance_gt_two h e hz hk
  have hb4 := (selected_span_conjugate_critical_path h hb p hnonabelian).1
  have hs := midpoint_slice_eq_reverse_kernel h e hz hk hb4 p g hg he hopposite
  have hm := (midpoint_common_kernel_endpoint_commutator h e hz hk hb4 p g hg he hopposite).2
  have hCQ : ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆ ≤ Q Rg (alpha Rg) :=
    le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer _).trans (Q_normalized Rg _))
  have hcomm : ⁅Z Rg (alpha Rg),Z Rg a'⁆ ≤ Z Rg (alpha Rg) :=
    le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
        (sourceDistance_pos h) p.critical).trans (Z_normalized Rg _))
  exact selected_core_le_seed_sup_moved_span h e hz hk hb p hnonabelian
    (by rw [hs.2.2.1]; decide)
    (core_estimates_of_forward_slice h e hz hk p hslice).1
    (((commutator_mono (inf_le_inf_right _ hCQ) le_rfl).trans_eq hm).trans hcomm)

include h e hz hk in
/-- The source midpoint slices bound the derived subgroup of the entire core
 by the same selected central line. Both the core supplement and its order
 bound are consequences, not extra premises. -/
theorem selected_core_derived_of_midpoint_slices
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
    let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
    C ≤ Z Rg (alpha Rg) ⊔ forwardMovedSpan Rg (p.walk.getVert 2) ∧
      ⁅C,C⁆ ≤ ⁅P,P⁆ ∧ Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 ∧
      ⁅C,C⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  have hb := distance_gt_two h e hz hk
  have hb4 := (selected_span_conjugate_critical_path h hb p hnonabelian).1
  have hs := midpoint_slice_eq_reverse_kernel h e hz hk hb4 p g hg he hopposite
  have hd := small_selected_span_derived h e hz hk hb p
    (by rw [hs.2.2.1]; decide) hslice hnonabelian
  have hsup := selected_core_supplement_of_midpoint_slices h e hz hk p
    hnonabelian hslice g hg he hopposite
  have hle : ⁅⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆,
      ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆⁆ ≤
      ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
        localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ := by
    rw [core_derived_eq_of_supplement (h := h) hb p hsup]
    exact commutator_mono (forwardMovedSpan_le Rg _) (forwardMovedSpan_le Rg _)
  let : Finite (⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ : Subgroup (FreeAmalgam Rg)) :=
    Nat.finite_of_card_ne_zero (by rw [hd.2.1]; decide)
  exact ⟨hsup,hle,(card_le_of_le hle).trans_eq hd.2.1,hle.trans hd.2.2⟩

omit hk in
include h e hz in
/-- Whole-core application of the full forward-kernel comparison, simultaneously
 for the point, plane and Sylow images of the original radical. -/
theorem coreExhaustion_or_cubic_core_kernel :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
        ⁅Q Rg a,Ltilde Rg a⁆ ≤ Q Rg a ⊓ centralizer
          (U Rg (p.walk.getVert 2) ⊓ B Rg a ((sourceGeometry h).Z_normal _) :
            Set (FreeAmalgam Rg))) ∧
      ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
        (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (p.walk.getVert 2)) ≤ 2 →
        let C := ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆
        (Q Rg (p.walk.getVert 2)).relIndex C ≤ 2 ∧
          ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),C⁆ ≤ Z Rg (alpha Rg) ∧
          Nat.card (⁅U Rg (p.walk.getVert 2),C⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 ∧
          ⁅U Rg (p.walk.getVert 2),C⁆ ≤ Z Rg (p.walk.getVert 1) ∧
          (⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
              localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ →
            ∀ g ∈ stabilizer Rg (p.walk.getVert 2),
              act Rg g (alpha Rg) = a' →
              (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
                (U Rg a') ≤ 2 →
              C ≤ Z Rg (alpha Rg) ⊔ forwardMovedSpan Rg (p.walk.getVert 2) ∧
                ⁅C,C⁆ ≤ ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
                  localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ∧
                Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 ∧
                ⁅C,C⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,
      fun _ _ p => core_commutator_le_forward_kernel_at h e hz hk p,?_⟩
    intro a' p hs
    have ht := core_estimates_of_forward_slice h e hz hk p hs
    exact ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2,
      fun hn g hg he ho => selected_core_derived_of_midpoint_slices h e hz hk p hn hs g hg he ho⟩

omit hk in
include h e hz in
/-- Literal C.1.32 consumer of the full-core comparison for the actual cubic
 projection and both full moving covers. No radical-image case is excluded. -/
theorem rankTwo_or_cubic_core_kernel :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
        ⁅Q Rg a,Ltilde Rg a⁆ ≤ Q Rg a ⊓ centralizer
          (U Rg (p.walk.getVert 2) ⊓ B Rg a ((sourceGeometry h).Z_normal _) :
            Set (FreeAmalgam Rg))) ∧
      ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
        (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (p.walk.getVert 2)) ≤ 2 →
        let C := ⁅Q Rg (alpha Rg),Ltilde Rg (alpha Rg)⁆
        (Q Rg (p.walk.getVert 2)).relIndex C ≤ 2 ∧
          ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),C⁆ ≤ Z Rg (alpha Rg) ∧
          Nat.card (⁅U Rg (p.walk.getVert 2),C⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 ∧
          ⁅U Rg (p.walk.getVert 2),C⁆ ≤ Z Rg (p.walk.getVert 1) ∧
          (⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
              localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ →
            ∀ g ∈ stabilizer Rg (p.walk.getVert 2),
              act Rg g (alpha Rg) = a' →
              (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
                (U Rg a') ≤ 2 →
              C ≤ Z Rg (alpha Rg) ⊔ forwardMovedSpan Rg (p.walk.getVert 2) ∧
                ⁅C,C⁆ ≤ ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
                  localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ∧
                Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 ∧
                ⁅C,C⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) :=
  (coreExhaustion_or_cubic_core_kernel h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
