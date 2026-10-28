module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ShiftedSpan

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreFixedLine

/-!
# Compatible edge kernels for the shifted central-cover configuration

A noncentral vector of the original moved cover has nonzero image in the
natural quotient. If an edge radical fixes it, its image is the unique
nonzero vector fixed by that full point core. This identifies the radical
and proves that its vector centralizer normalizes it. Two adjacent edge
seeds sharing a noncentral moving vector consequently have equal kernels.
The argument retains the central line of the order-32 cover.

Each noncentral vector belongs to an equivariant duad orbit in either
cover. Component transitivity moves it into the fixed space of a chosen
generating edge. For an order-two subgroup this supplies one component
conjugator giving edge placement, local generation and movement by the
opposite critical seed simultaneously.

The application uses the actual characteristic replacement and canonical
quotient. It retains the forward extension and every shared vertex, then
uses this one conjugator for both shifted spans and their edge kernel.
Every incident edge in the centralizer orbit has the same kernel, which
normalizes the seed span already contained in the old endpoint kernel.

Source: Meierfrankenfeld--Stellmacher (1993), (5.9), printed pp.920--922;
Aschbacher--Smith B.3.4 for the full point core and its natural fixed line.
This adapts SymplecticSetup.PointLineKernel and PointLineChoice to both
central covers. The common-kernel span contradiction still needs the
central attachment: in the augmentation cover the point-core displacement
of a transposition-fixed hyperplane can be the complementary line, so the
native zero-center argument cannot be used unchanged. The strict slice
estimate and final Section 5 distance exclusions are not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


private theorem point_core_fixed_nonzero (u : S) (v : natural (Fin 6))
    (hv : v ≠ 0)
    (hfix : ∀ g ∈ pointCore.map (MulAut.conj u).toMonoidHom,
      naturalRepresentation (Fin 6) g v = v) :
    v = naturalRepresentation (Fin 6) u (NaturalGeometry.pairVector 4 5) := by
  let A := pointCore.map (MulAut.conj u).toMonoidHom
  let F := fixedSpace (naturalRepresentation (Fin 6)) A
  have hdim : Module.finrank (ZMod 2) F = 1 := by
    have hcodim : fixedCodim (naturalRepresentation (Fin 6)) A = 3 := by
      dsimp only [A]
      rw [CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional,fixedCodim_map_conj]
      exact CFSG.Quasithin.ChapterB.Offenders.Six.fixedCodim_exceptional.2.2.2
    have hh := fixedCodim_add_finrank (naturalRepresentation (Fin 6)) A
    rw [hcodim,finrank_natural_even (Fin 6) (by decide)] at hh
    change 3 + Module.finrank (ZMod 2) F = 4 at hh
    omega
  have hcard : Nat.card F = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),hdim]
    norm_num
  let w := naturalRepresentation (Fin 6) u (NaturalGeometry.pairVector 4 5)
  have hwfix : w ∈ F := fun g => PointCoreFixedLine.conjugate_core_fixes u g g.property
  have hwne : w ≠ 0 := by
    intro hh
    have he := congrArg (naturalRepresentation (Fin 6) u⁻¹) hh
    dsimp only [w] at he
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply,map_zero] at he
    exact (NaturalGeometry.pairVector_ne_zero (by decide : (4 : Fin 6) ≠ 5)) he
  obtain ⟨x,hx,hu⟩ := (Nat.card_eq_two_iff' (0 : F)).mp hcard
  have hvx : (⟨v,fun g => hfix g g.property⟩ : F) = x := hu _ (fun he => hv (congrArg Subtype.val he))
  have hwx : (⟨w,hwfix⟩ : F) = x := hu _ (fun he => hwne (congrArg Subtype.val he))
  exact congrArg Subtype.val (hvx.trans hwx.symm)

include s in
private theorem cover_noncentral_image_ne_zero (v : replacementMoved d)
    (hv : (v : d.overgroup) ∉ center d.overgroup) :
    coverMap (h := h) (e := e) (hz := hz) (hn := hn) (Additive.ofMul v) ≠ 0 := by
  intro hh
  apply hv
  have hh' : v ∈ (coverProjection h e hz hn d).ker := hh
  rwa [coverProjection_kernel_center s] at hh'

private theorem cover_fixed_image (u : S)
    (hfull : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    (v : replacementMoved d) (hv : (v : d.overgroup) ∉ center d.overgroup)
    (hfix : (v : d.overgroup) ∈ centralizer (d.radical : Set d.overgroup)) :
    coverMap (h := h) (e := e) (hz := hz) (hn := hn) (Additive.ofMul v) =
      naturalRepresentation (Fin 6) u (NaturalGeometry.pairVector 4 5) := by
  apply point_core_fixed_nonzero u _ (cover_noncentral_image_ne_zero s v hv)
  intro g hg
  obtain ⟨r,hr,rfl⟩ := hfull.symm ▸ hg
  rw [←coverMap_equivariant s]
  congr 1
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coverAction_conjugate]
  exact mul_inv_eq_iff_eq_mul.mpr (hfix r hr)

/-- A noncentral cover vector fixed by the full point radical determines
its kernel through the original natural quotient. -/
theorem cover_vector_centralizer_normalizes_radical (u : S)
    (hfull : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    (v : replacementMoved d) (hv : (v : d.overgroup) ∉ center d.overgroup)
    (hfix : (v : d.overgroup) ∈ centralizer (d.radical : Set d.overgroup)) :
    centralizer ({(v : d.overgroup)} : Set d.overgroup) ≤ normalizer (d.radical : Set d.overgroup) := by
  have hpre : (pointCore.map (MulAut.conj u).toMonoidHom).comap s.projection = d.radical := by
    rw [←hfull,comap_map_eq,s.projection_kernel,sup_eq_left.mpr (replacement_core_le_radical h d)]
  have hw := cover_fixed_image s u hfull v hv hfix
  intro m hm
  have he : coverAction s (s.projection m) (Additive.ofMul v) = Additive.ofMul v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [coverAction_conjugate]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hm)
  have hh := coverMap_equivariant s (s.projection m) (Additive.ofMul v)
  rw [he,hw] at hh
  have hn := (pointCore.map (MulAut.conj u).toMonoidHom).le_normalizer_comap s.projection
    (PointCoreFixedLine.normalizes_core_of_fixes u (s.projection m) hh.symm)
  rwa [hpre] at hn

private theorem radical_conjugate_eq_of_common_fixed (u : S)
    (hfull : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    (v : replacementMoved d) (hv : (v : d.overgroup) ∉ center d.overgroup)
    (hfix : (v : d.overgroup) ∈ centralizer (d.radical : Set d.overgroup))
    (g : d.overgroup)
    (hfix' : (v : d.overgroup) ∈ centralizer
      (d.radical.map (MulAut.conj g).toMonoidHom : Set d.overgroup)) :
    d.radical.map (MulAut.conj g).toMonoidHom = d.radical := by
  let w := coverAction s (s.projection (g⁻¹)) (Additive.ofMul v)
  have hwval : (w.toMul : d.overgroup) = g⁻¹*(v:d.overgroup)*g := by
    dsimp only [w]
    rw [coverAction_conjugate,inv_inv,toMul_ofMul]
  have hwne : (w.toMul : d.overgroup) ∉ center d.overgroup := by
    intro hh
    apply hv
    have hz := (inferInstance : (center d.overgroup).Normal).conj_mem _ hh g
    rwa [hwval,show g*(g⁻¹*(v:d.overgroup)*g)*g⁻¹=(v:d.overgroup) by group] at hz
  have hwfix : (w.toMul : d.overgroup) ∈ centralizer (d.radical : Set d.overgroup) := by
    intro r hr
    have hh := hfix' _ (mem_map_of_mem (MulAut.conj g).toMonoidHom hr)
    change (g*r*g⁻¹)*(v:d.overgroup)=(v:d.overgroup)*(g*r*g⁻¹) at hh
    rw [hwval]
    calc
      r*(g⁻¹*(v:d.overgroup)*g) = g⁻¹*((g*r*g⁻¹)*(v:d.overgroup))*g := by group
      _ = g⁻¹*((v:d.overgroup)*(g*r*g⁻¹))*g := by rw [hh]
      _ = (g⁻¹*(v:d.overgroup)*g)*r := by group
  have hvimage := cover_fixed_image s u hfull v hv hfix
  have hwimage := cover_fixed_image s u hfull w.toMul hwne hwfix
  have he := coverMap_equivariant s (s.projection (g⁻¹)) (Additive.ofMul v)
  rw [hvimage] at he
  have he' : naturalRepresentation (Fin 6) (s.projection (g⁻¹))
      (naturalRepresentation (Fin 6) u (NaturalGeometry.pairVector 4 5)) =
      naturalRepresentation (Fin 6) u (NaturalGeometry.pairVector 4 5) := he.symm.trans hwimage
  have hn := (pointCore.map (MulAut.conj u).toMonoidHom).le_normalizer_comap s.projection
    (PointCoreFixedLine.normalizes_core_of_fixes u (s.projection (g⁻¹)) he')
  have hpre : (pointCore.map (MulAut.conj u).toMonoidHom).comap s.projection = d.radical := by
    rw [←hfull,comap_map_eq,s.projection_kernel,sup_eq_left.mpr (replacement_core_le_radical h d)]
  rw [hpre] at hn
  exact mem_normalizer_iff_map_conj_eq.mp (by simpa only [inv_inv] using (normalizer (d.radical : Set d.overgroup)).inv_mem hn)

private theorem edge_cover_coordinates (hc : DistanceTwo.CentralLayer d)
    {a t : Vertex d.radical} (ha : color d.radical a=false) (hat : Adjacent d.radical a t) :
    ∃ i : d.overgroup→*FreeAmalgam d.radical, Function.Injective i ∧
      i.range=stabilizer d.radical a ∧ d.radical.map i=Q d.radical t ∧
      (replacementMoved d).map i=U d.radical a := by
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_⟩
    · rw [MonoidHom.range_comp]
      exact (stabilizer_mVertex d.radical g).symm
    · have he := Q_act d.radical g (beta d.radical)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
    · have he := U_act d.radical g (alpha d.radical)
      rw [hc.U_eq_moved] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at ha
    cases ha

omit [Finite G] in
private theorem edge_seed_centralizes_kernel {a t : Vertex d.radical}
    (ha : color d.radical a=false) (hat : Adjacent d.radical a t) :
    Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
  have ht : color d.radical t≠false := by
    rw [←ha]
    exact Ne.symm (adjacent_color_ne d.radical hat)
  intro x hx
  rw [Z,if_neg ht] at hx
  exact (mem_omegaCenter_iff.mp hx).2.2

/-- A noncentral subgroup of a moving edge seed determines its actual
edge kernel, even when the moving cover has a central line. -/
theorem cover_edge_line_centralizer_normalizes_kernel (hc : DistanceTwo.CentralLayer d) (u : S)
    (hfull : d.radical.map s.projection=pointCore.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex d.radical} (ha : color d.radical a=false) (hat : Adjacent d.radical a t)
    (H : Subgroup (FreeAmalgam d.radical)) (hHU : H≤U d.radical a) (hHt : H≤Z d.radical t)
    (hnot : ¬ H≤centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    stabilizer d.radical a⊓centralizer (H:Set (FreeAmalgam d.radical))≤
      normalizer (Q d.radical t:Set (FreeAmalgam d.radical)) := by
  obtain ⟨z,hz,hzn⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨i,hi,hir,hiR,hiU⟩ := edge_cover_coordinates hc ha hat
  obtain ⟨v,hv,rfl⟩ := hiU.symm ▸ hHU hz
  have hvn : v∉center d.overgroup := by
    intro hvn
    apply hzn
    intro x hx
    obtain ⟨x,rfl⟩ := hir.symm ▸ hx
    simpa only [map_mul] using congrArg i (mem_center_iff.mp hvn x)
  have hvfix : v∈centralizer (d.radical:Set d.overgroup) := by
    intro r hr
    apply hi
    simp only [map_mul]
    exact edge_seed_centralizes_kernel ha hat (hHt hz) _ (hiR ▸ mem_map_of_mem i hr)
  intro m hm
  obtain ⟨m,rfl⟩ := hir.symm ▸ hm.1
  rw [←hiR]
  apply d.radical.le_normalizer_map i
  apply mem_map_of_mem
  apply cover_vector_centralizer_normalizes_radical s u hfull ⟨v,hv⟩ hvn hvfix
  rw [mem_centralizer_singleton_iff]
  apply hi
  simpa only [map_mul] using (hm.2 _ hz).symm

/-- Two adjacent edge seeds sharing a noncentral moving vector have the
same kernel. Noncentrality is measured in the whole starting stabilizer. -/
theorem cover_edge_kernel_eq_of_common_line (hc : DistanceTwo.CentralLayer d) (u : S)
    (hfull : d.radical.map s.projection=pointCore.map (MulAut.conj u).toMonoidHom)
    {a t t' : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hat' : Adjacent d.radical a t')
    (H : Subgroup (FreeAmalgam d.radical)) (hHU : H≤U d.radical a)
    (hHt : H≤Z d.radical t) (hHt' : H≤Z d.radical t')
    (hnot : ¬ H≤centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    Q d.radical t'=Q d.radical t := by
  obtain ⟨z,hz,hzn⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨i,hi,hir,hiR,hiU⟩ := edge_cover_coordinates hc ha hat
  obtain ⟨v,hv,rfl⟩ := hiU.symm ▸ hHU hz
  have hvn : v∉center d.overgroup := by
    intro hvn
    apply hzn
    intro x hx
    obtain ⟨x,rfl⟩ := hir.symm ▸ hx
    simpa only [map_mul] using congrArg i (mem_center_iff.mp hvn x)
  have hvfix : v∈centralizer (d.radical:Set d.overgroup) := by
    intro r hr
    apply hi
    simp only [map_mul]
    exact edge_seed_centralizes_kernel ha hat (hHt hz) _ (hiR ▸ mem_map_of_mem i hr)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical a hat hat'
  obtain ⟨m,hm⟩ := hir.symm ▸ hg
  have hQt' : Q d.radical t' = (d.radical.map (MulAut.conj m⁻¹).toMonoidHom).map i := by
    rw [←hgt,Q_act,←hiR,map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change g⁻¹*i x*(g⁻¹)⁻¹=i (m⁻¹*x*(m⁻¹)⁻¹)
    simp only [map_mul,map_inv,hm]
  have hvfix' : v∈centralizer
      (d.radical.map (MulAut.conj m⁻¹).toMonoidHom:Set d.overgroup) := by
    intro r hr
    apply hi
    simp only [map_mul]
    exact edge_seed_centralizes_kernel ha hat' (hHt' hz) _ (hQt'.symm ▸ mem_map_of_mem i hr)
  rw [hQt',radical_conjugate_eq_of_common_fixed s u hfull ⟨v,hv⟩ hvn hvfix m⁻¹ hvfix',hiR]

open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits
private theorem cover_vector_orbit (v : replacementMoved d)
    (hv : (v : d.overgroup) ∉ center d.overgroup) :
    ∃ f : Duad → Additive (replacementMoved d), Function.Injective f ∧
      (∀ g j, coverAction s g (f j) = f (g • j)) ∧
      ∃ j, f j = Additive.ofMul v := by
  have hnotfixed : ¬ ∀ g, coverAction s g (Additive.ofMul v) = Additive.ofMul v := by
    intro hh
    apply hv
    apply mem_center_iff.mpr
    intro m
    have he := congrArg (fun w : Additive (replacementMoved d) => (w.toMul : d.overgroup))
      (hh (s.projection m))
    rw [coverAction_conjugate] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  rcases cover_model s with ⟨E,hE⟩ | ⟨E,hE⟩
  · have hzero : E (Additive.ofMul v) ≠ 0 := by
      intro he
      apply hnotfixed
      intro g
      apply E.injective
      simpa only [MonoidHom.id_apply,he,map_zero] using hE g (Additive.ofMul v)
    obtain ⟨j,hj⟩ := natural_cases _ hzero
    refine ⟨fun j => E.symm (naturalDuad j),E.symm.injective.comp naturalDuad_injective,?_,j,?_⟩
    · intro g j
      apply E.injective
      rw [hE]
      simp only [MonoidHom.id_apply,LinearEquiv.apply_symm_apply,naturalDuad_map]
    · exact E.injective (by simpa only [LinearEquiv.apply_symm_apply] using hj)
  · rcases cover_cases (E (Additive.ofMul v)) with he | he | ⟨j,he | he⟩
    · exfalso
      apply hnotfixed
      intro g
      apply E.injective
      simpa only [MonoidHom.id_apply,he,map_zero] using hE g (Additive.ofMul v)
    · exfalso
      apply hnotfixed
      intro g
      apply E.injective
      simpa only [MonoidHom.id_apply,he,coverOne_map] using hE g (Additive.ofMul v)
    · refine ⟨fun j => E.symm (coverDuad j),E.symm.injective.comp coverDuad_injective,?_,j,?_⟩
      · intro g j
        apply E.injective
        rw [hE]
        simp only [MonoidHom.id_apply,LinearEquiv.apply_symm_apply,coverDuad_map]
      · exact E.injective (by simpa only [LinearEquiv.apply_symm_apply] using he.symm)
    · refine ⟨fun j => E.symm (complementaryDuad j),
        E.symm.injective.comp complementaryDuad_injective,?_,j,?_⟩
      · intro g j
        apply E.injective
        rw [hE]
        simp only [MonoidHom.id_apply,LinearEquiv.apply_symm_apply,complementaryDuad_map]
      · exact E.injective (by simpa only [LinearEquiv.apply_symm_apply,complementaryDuad] using he.symm)

private theorem exists_cover_conjugate_fixed_radical (u : S)
    (hfull : d.radical.map s.projection=pointCore.map (MulAut.conj u).toMonoidHom)
    (v : replacementMoved d) (hv : (v:d.overgroup)∉center d.overgroup) :
    ∃ g∈replacementComponent d,
      g*(v:d.overgroup)*g⁻¹∈centralizer (d.radical:Set d.overgroup) := by
  obtain ⟨f,hf,heq,j,hj⟩ := cover_vector_orbit s v hv
  let w := naturalRepresentation (Fin 6) u (NaturalGeometry.pairVector 4 5)
  have hwne : w≠0 := by
    intro hh
    have he := congrArg (naturalRepresentation (Fin 6) u⁻¹) hh
    dsimp only [w] at he
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply,map_zero] at he
    exact (NaturalGeometry.pairVector_ne_zero (by decide : (4:Fin 6)≠5)) he
  obtain ⟨k,hk⟩ := natural_cases w hwne
  obtain ⟨t,ht⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) j k
  have htL : t.val∈(replacementComponent d).map s.projection := by
    rw [s.component_image]
    exact t.property
  obtain ⟨g,hg,hgt⟩ := htL
  have hvg : coverAction s (s.projection g) (Additive.ofMul v)=f k := by
    rw [←hj,hgt,heq]
    exact congrArg f ht
  refine ⟨g,hg,?_⟩
  intro r hr
  have hrk : s.projection r • k = k := by
    apply naturalDuad_injective
    rw [←naturalDuad_map,hk]
    exact PointCoreFixedLine.conjugate_core_fixes u (s.projection r)
      (hfull ▸ mem_map_of_mem s.projection hr)
  have hfix : coverAction s (s.projection r) (f k)=f k := by rw [heq,hrk]
  have hval := coverAction_conjugate s g (Additive.ofMul v)
  rw [hvg] at hval
  have hh := coverAction_conjugate s r (f k)
  rw [hfix,hval] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh.symm

private theorem full_point_generating_neighbor_at
    (hc : DistanceTwo.CentralLayer d) (u : S)
    (hfull : d.radical.map s.projection=pointCore.map (MulAut.conj u).toMonoidHom)
    {a b : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a b) :
    ∃ t, Adjacent d.radical a t ∧ Q d.radical t⊔Z d.radical b=stabilizer d.radical a := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ (mVertex d.radical g)=alpha d.radical := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have base := full_point_generating_neighbor s hc u hfull
    (a' := act d.radical g⁻¹ b)
  rw [←hbase] at base
  obtain ⟨t,hat,hgen⟩ := base (p.act g⁻¹)
  have hback (z : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ z)=z := by
    rw [←act_mul,inv_mul_cancel,act_one]
  refine ⟨act d.radical g t,?_,?_⟩
  · have hh := (adjacent_act_iff d.radical g _ _).mpr hat
    rwa [hback] at hh
  · have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hback,hback] at hh
    exact hh

/-- A noncentral order-two subgroup in either moving cover has one component
conjugate lying in an actual generating edge seed. The same conjugate supplies
the generating line centralizer and is moved by the opposite critical seed. -/
theorem exists_cover_line_edge_generator (hc : DistanceTwo.CentralLayer d) (u : S)
    (hfull : d.radical.map s.projection=pointCore.map (MulAut.conj u).toMonoidHom)
    {a b : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a b)
    (H : Subgroup (FreeAmalgam d.radical)) (hHU : H≤U d.radical a)
    (hcard : Nat.card H=2)
    (hnot : ¬H≤centralizer (stabilizer d.radical a:Set (FreeAmalgam d.radical))) :
    ∃ t, Adjacent d.radical a t ∧ Q d.radical t⊔Z d.radical b=stabilizer d.radical a ∧
      ∃ y∈Ltilde d.radical a,
        H.map (MulAut.conj y).toMonoidHom≤U d.radical a⊓Z d.radical t ∧
        (stabilizer d.radical a⊓centralizer
          (H.map (MulAut.conj y).toMonoidHom:Set (FreeAmalgam d.radical)))⊔
            Z d.radical b=stabilizer d.radical a ∧
        ¬H.map (MulAut.conj y).toMonoidHom≤centralizer (Z d.radical b:Set (FreeAmalgam d.radical)) := by
  obtain ⟨t,hat,hgen⟩ := full_point_generating_neighbor_at s hc u hfull p
  obtain ⟨z,hzn,hu⟩ := (Nat.card_eq_two_iff' (1:H)).mp hcard
  have hznot : (z:FreeAmalgam d.radical)∉centralizer
      (stabilizer d.radical a:Set (FreeAmalgam d.radical)) := by
    intro hz
    apply hnot
    intro x hx
    by_cases hx1 : x=1
    · exact hx1 ▸ one_mem _
    · have he : (⟨x,hx⟩:H)=z := hu _ (fun he => hx1 (congrArg Subtype.val he))
      have hxz : x=(z:FreeAmalgam d.radical) := congrArg Subtype.val he
      rw [hxz]
      exact hz
  obtain ⟨i,hi,hir,hiR,hiU⟩ := edge_cover_coordinates hc p.start_color hat
  obtain ⟨v,hv,hvz⟩ := hiU.symm ▸ hHU z.property
  have hvn : v∉center d.overgroup := by
    intro hvn
    apply hznot
    intro x hx
    obtain ⟨x,rfl⟩ := hir.symm ▸ hx
    rw [←hvz,←map_mul,←map_mul]
    exact congrArg i (mem_center_iff.mp hvn x)
  obtain ⟨g,hg,hgfix⟩ := exists_cover_conjugate_fixed_radical s u hfull ⟨v,hv⟩ hvn
  let y := i g
  have hy : y∈Ltilde d.radical a := by
    let j : d.overgroup→*stabilizer d.radical a :=
      i.codRestrict _ (fun x => hir ▸ (show i x∈i.range from ⟨x,rfl⟩))
    have hg' : g∈pResidual 2 d.overgroup := (replacement_residual h d).symm ▸ hg
    exact mem_map_of_mem (stabilizer d.radical a).subtype
      ((map_pResidual_le 2 j) (mem_map_of_mem j hg'))
  have hyG := Ltilde_le_stabilizer a hy
  have hzfix : y*(z:FreeAmalgam d.radical)*y⁻¹∈centralizer (Q d.radical t:Set (FreeAmalgam d.radical)) := by
    intro r hr
    have hr' : r∈d.radical.map i := hiR.symm ▸ hr
    obtain ⟨r₀,hr₀,hr_eq⟩ := hr'
    rw [←hr_eq,←hvz]
    simpa only [y,map_mul,map_inv] using congrArg i (hgfix r₀ hr₀)
  have hHU' : H.map (MulAut.conj y).toMonoidHom≤U d.radical a :=
    (map_mono hHU).trans_eq (mem_normalizer_iff_map_conj_eq.mp (U_normalized a hyG))
  have hHfix : H.map (MulAut.conj y).toMonoidHom≤centralizer (Q d.radical t:Set (FreeAmalgam d.radical)) := by
    rintro _ ⟨x,hx,rfl⟩
    by_cases hx1 : x=1
    · simpa only [hx1,map_one] using (centralizer (Q d.radical t:Set (FreeAmalgam d.radical))).one_mem
    · have he : (⟨x,hx⟩:H)=z := hu _ (fun he => hx1 (congrArg Subtype.val he))
      rw [show x=(z:FreeAmalgam d.radical) from congrArg Subtype.val he]
      exact hzfix
  have ht : color d.radical t=true := by
    have hn := adjacent_color_ne d.radical hat
    rw [p.start_color] at hn
    cases he : color d.radical t <;> simp_all
  have hUQ : U d.radical a≤Q d.radical a :=
    (DistanceEight.U_le_Z d.radical a).trans (Z_le_Q_of_dist_lt d.radical a
      ((replacementGeometry h d).exists_critical a p.start_color) (by
        rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant a p.start_color]
        exact replacementDistance_pos h d))
  have hHseed : H.map (MulAut.conj y).toMonoidHom≤Z d.radical t := by
    intro x hx
    rw [Z,if_neg (by simp [ht])]
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
    exact mem_omegaCenter_iff.mpr
      ⟨(hHU'.trans (hUQ.trans (Q_le_adjacent_h d.radical ht hat))) hx,
        elemPow_eq_one_of_isElementaryAbelian x ((DistanceEight.U_le_Z d.radical a) (hHU' hx)),hHfix hx⟩
  refine ⟨t,hat,hgen,y,hy,le_inf hHU' hHseed,?_,?_⟩
  · apply le_antisymm (sup_le inf_le_left
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
        (by rw [(replacementGeometry h d).distance_constant a p.start_color]
            exact replacementDistance_pos h d) p.critical))
    conv_lhs => rw [←hgen]
    exact sup_le_sup_right (le_inf (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
      (le_centralizer_iff.mp hHfix)) _
  · intro hh
    have hfix : H.map (MulAut.conj y).toMonoidHom≤centralizer
        (stabilizer d.radical a:Set (FreeAmalgam d.radical)) := by
      apply le_centralizer_iff.mp
      rw [←hgen]
      exact sup_le (le_centralizer_iff.mp hHfix) (le_centralizer_iff.mp hh)
    apply hnot
    intro x hx r hr
    have hr' : y*r*y⁻¹∈stabilizer d.radical a :=
      (stabilizer d.radical a).mul_mem ((stabilizer d.radical a).mul_mem hyG hr)
        ((stabilizer d.radical a).inv_mem hyG)
    have he := hfix (mem_map_of_mem (MulAut.conj y).toMonoidHom hx) _ hr'
    apply (MulAut.conj y).injective
    change y*(r*x)*y⁻¹=y*(x*r)*y⁻¹
    calc
      y*(r*x)*y⁻¹ = (y*r*y⁻¹)*(y*x*y⁻¹) := by group
      _ = (y*x*y⁻¹)*(y*r*y⁻¹) := he
      _ = y*(x*r)*y⁻¹ := by group
/-- The literal full-point small-image configuration now retains a generating
edge containing the same shifted line. Its centralizer preserves that edge
kernel, every conjugated incident edge has that kernel, and the kernel
normalizes the shifted seed span already placed in the old endpoint. -/
theorem full_point_small_compatible_shifted_spans_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    let c := p.walk.getVert 2
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical c,T⁆
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) c z,
      (cosetGraph d.radical).dist a' z = 2 ∧
      (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
      q.walk.getVert (q.walk.length-2) = a' ∧
      ∃ t, Adjacent d.radical c t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical c ∧
      ∃ y ∈ Ltilde d.radical c,
        let a := act d.radical y⁻¹ (alpha d.radical)
        let T₂ := T.map (MulAut.conj y).toMonoidHom
        let H₂ := H.map (MulAut.conj y).toMonoidHom
        let Y := (localZSpan d.radical c (alpha d.radical)).map (MulAut.conj y).toMonoidHom
        let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
        P ⊔ Z d.radical z = stabilizer d.radical c ∧
        ¬ H₂ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) ∧
        T₂ = Q d.radical a ⊓ centralizer
          (U d.radical c ⊓ B d.radical a ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical)) ∧
        Z d.radical c ≤ Y ∧ Y ≤ V d.radical a ∧
        stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) ∧
        ¬ Y ≤ B d.radical a ((replacementGeometry h d).Z_normal _) ∧
        H₂ ≤ Z d.radical a ∧ Nat.card H₂ = 2 ∧
        H₂ ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
        ⁅Y,T₂⁆ ≤ H₂ ∧ Z d.radical a ≤ Q d.radical a' ∧ Y ≤ Q d.radical a' ∧
        conjugateSpanBy (Z d.radical a) P ≤ Q d.radical a' ∧
        conjugateSpanBy Y P ≤ Q d.radical a' ∧
        Z d.radical a ≤ V d.radical c ∧
        ¬ Z d.radical a ≤ B d.radical c ((replacementGeometry h d).Z_normal _) ∧
        H₂ ≤ U d.radical c ⊓ Z d.radical t ∧
        P ≤ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧
        Q d.radical (act d.radical y⁻¹ (p.walk.getVert 1)) = Q d.radical t ∧
        Q d.radical t ≤ normalizer
          (conjugateSpanBy (Z d.radical a) P : Set (FreeAmalgam d.radical)) ∧
        (∀ x ∈ P, Q d.radical (act d.radical x⁻¹
          (act d.radical y⁻¹ (p.walk.getVert 1))) = Q d.radical t) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  let c := p.walk.getVert 2
  let k := p.walk.getVert 1
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  have hl : 2 < p.walk.length := p.length_eq_b ▸ (show 2 < replacementDistance h d by omega)
  have hat : Adjacent d.radical (alpha d.radical) k := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hck : Adjacent d.radical c k := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hk : color d.radical k = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical k at hh
    cases he : color d.radical k <;> simp_all
  have hTG : T ≤ stabilizer d.radical c :=
    (inf_le_left.trans (Q_le_adjacent_h d.radical hk hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hck))
  have hHU : H ≤ U d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))
  have hline := full_point_small_forward_line_knownSimple (by omega) u hfull p hslice hsmall
  obtain ⟨_,_,z,q,haz,hover,hpre⟩ := full_point_forward_path_knownSimple (by omega) u hfull p
  obtain ⟨t,hct,hQtgen,y,hy,hHseed,hgen,hmove⟩ :=
    exists_cover_line_edge_generator s hc u hfull' q H hHU hline.2.1 hline.2.2.2.2
  have cfg := small_shifted_forward_configuration_of_choice s hc u hfull' hb p hsmall
    hline.1 z q.end_color haz y (Ltilde_le_stabilizer _ hy) hgen hmove
  obtain ⟨hPgen,hHmove,hT,hZcY,hYV,hYN,hYB,hHZa,hHcard,hHCa,hcomm,
    hZaQ,hYQ,hZspanQ,hYspanQ⟩ := cfg
  let a := act d.radical y⁻¹ (alpha d.radical)
  let H₂ := H.map (MulAut.conj y).toMonoidHom
  let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  have hnot : ¬H₂≤centralizer (stabilizer d.radical c:Set (FreeAmalgam d.radical)) := by
    intro hh
    exact hmove (hh.trans (centralizer_le (critical_Z_le_stabilizer d.radical
      (replacementGeometry h d) c q.start_color (by
        rw [(replacementGeometry h d).distance_constant c q.start_color]
        exact replacementDistance_pos h d) q.critical)))
  have hnorm : P≤normalizer (Q d.radical t:Set (FreeAmalgam d.radical)) :=
    cover_edge_line_centralizer_normalizes_kernel s hc u hfull' q.start_color hct H₂
      (hHseed.trans inf_le_left) (hHseed.trans inf_le_right) hnot
  have hfixc : act d.radical y⁻¹ c=c := (stabilizer d.radical c).inv_mem (Ltilde_le_stabilizer c hy)
  have hactck : Adjacent d.radical c (act d.radical y⁻¹ k) := by
    simpa only [hfixc] using (adjacent_act_iff d.radical y⁻¹ c k).mpr hck
  have hHk : H₂≤Z d.radical (act d.radical y⁻¹ k) := by
    rw [Z_act,inv_inv]
    exact map_mono hline.2.2.1
  have hkeq : Q d.radical (act d.radical y⁻¹ k)=Q d.radical t :=
    cover_edge_kernel_eq_of_common_line s hc u hfull' q.start_color hct hactck H₂
      (hHseed.trans inf_le_left) (hHseed.trans inf_le_right) hHk hnot
  have hQtP : Q d.radical t≤P :=
    le_inf (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
      (le_centralizer_iff.mp ((hHseed.trans inf_le_right).trans
        (edge_seed_centralizes_kernel q.start_color hct)))
  refine ⟨z,q,haz,hover,hpre,t,hct,hQtgen,y,hy,hPgen,hHmove,hT,hZcY,hYV,hYN,hYB,hHZa,?_,
    hHCa,hcomm,hZaQ,hYQ,hZspanQ,hYspanQ,?_,?_,hHseed,hnorm,hkeq,
    hQtP.trans (le_normalizer_conjugateSpanBy _ _),?_⟩
  · rw [card_map_of_injective (MulAut.conj y).injective]
    exact hline.2.1
  · have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    have hZV : Z d.radical (alpha d.radical) ≤ V d.radical (p.walk.getVert 2) :=
      le_iSup_of_le (alpha d.radical) (le_iSup_of_le
        (show (cosetGraph d.radical).dist (alpha d.radical) (p.walk.getVert 2) ≤ 2 from
          (p.dist_start (by omega)).le) le_rfl)
    rw [Z_act,inv_inv]
    exact (map_mono hZV).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (DistanceEight.V_normalized d.radical _ (Ltilde_le_stabilizer _ hy)))
  · have hcol : color d.radical (p.walk.getVert 2) = false :=
      (p.vertex_color (by have hl : p.walk.length = replacementDistance h d := p.length_eq_b; omega)).mpr
        (by decide)
    have hBm := mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (show 2 < replacementDistance h d by omega)
        _ hcol (Ltilde_le_stabilizer _ hy))
    intro hbad
    rw [Z_act,inv_inv,←hBm] at hbad
    have hstart := (map_le_map_iff_of_injective (MulAut.conj y).injective).mp hbad
    exact critical_start_not_le_second_slice s hc (by omega) p
      ((DistanceEight.U_le_Z d.radical _).trans hstart)

  · intro x hx
    rw [Q_act,inv_inv,hkeq]
    exact mem_normalizer_iff_map_conj_eq.mp (hnorm hx)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
