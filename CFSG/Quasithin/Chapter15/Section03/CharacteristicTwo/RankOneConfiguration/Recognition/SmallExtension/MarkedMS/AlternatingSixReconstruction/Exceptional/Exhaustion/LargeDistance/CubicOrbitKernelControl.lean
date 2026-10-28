module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRestrictedOrbit

/-!
# Full reverse-kernel control of the cubic centralizer orbits

The second two-core fixes the transported line and normalizes both literal
orbits. Their full join has the same commutator R₃ with the entire reverse
critical kernel. This places R₃ in the seed orbit and that kernel, makes
the kernel normal under the old endpoint core, and shows that R₃ centralizes
the old core, the new endpoint seed and the second radius. Both orbits lie
in the intersection of the old endpoint and second two-cores.

If the span orbit fixes the reverse kernel, the critical fixed-space
calculation makes it normal in the second local group. An escaping actor
then fixes its residual section modulo the second seed. The intervening
edge core normalizes the original shifted span, so local generation shows
that the orbit equals that span. In the remaining branch its commutator
with the full reverse kernel is exactly R₃, which lies in the span orbit.

The whole-core and literal C.1.32 applications construct this alternative
on the original graph, retaining both covers and the odd covering kernel.
Centrality of R₃ in the entire second local group, stabilization in the
nonzero branch, strict slices and the remaining source exclusions are
still required. This module does not assert either full reconstruction.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), pp.866--867,
and the centralizer-orbit and stabilization argument of (5.9), p.921.
The fixed-kernel branch here is a consequence of those local interfaces;
the source's Thompson case split proving R₃ central is not replaced.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
namespace SmallSliceShift
variable {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

/-- The second two-core fixes the transported line, so it normalizes both
literal centralizer orbits. -/
theorem second_core_le_lineCentralizer (hb : 2 < sourceDistance h) :
    Q Rg (p.walk.getVert 2) ≤ s.lineCentralizer := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hTG : forwardSliceKernel h (alpha Rg) c ≤ stabilizer Rg c :=
    (inf_le_left.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hHU : forwardSliceLine h (alpha Rg) c ≤ U Rg c :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))
  have hH : s.line ≤ Z Rg c := by
    have hm := map_mono (f := (MulAut.conj s.conjugator).toMonoidHom) hHU
    have he := mem_normalizer_iff_map_conj_eq.mp
      (U_normalized c (Ltilde_le_stabilizer _ s.residual))
    exact (hm.trans_eq he).trans (DistanceEight.U_le_Z Rg c)
  exact le_inf (fun _ hx => hx.1)
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg c s.path.start_color))).trans (centralizer_le hH))

include e hz in
/-- R₃ lies in the second radius and centralizes that entire radius.
This is centrality in the radius, not in the second local group. -/
theorem orbitDisplacement_second_radius (hb : 4 < sourceDistance h) :
    s.orbitDisplacement ≤ V Rg (p.walk.getVert 2) ⊓
      centralizer (V Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  have hD := (s.seedOrbit_radius_and_escape e hz (by omega)).1
  have hK : s.orbitKernel ≤ Q Rg (p.walk.getVert 2) := inf_le_right
  have hcomm : s.orbitDisplacement ≤ ⁅V Rg (p.walk.getVert 2),Q Rg (p.walk.getVert 2)⁆ :=
    commutator_mono hD hK
  refine le_inf ?_ ?_
  · exact hcomm.trans (le_normalizer_iff_commutator_le_left.mp
      ((show Q Rg (p.walk.getVert 2) ≤ stabilizer Rg (p.walk.getVert 2) from
        fun _ hx => hx.1).trans (V_normalized _)))
  · exact hcomm.trans
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.radius_commutator_central_of_four_lt
        Rg (sourceGeometry h) (by change 4 < sourceDistance h; exact hb) s.path.start_color)

include e hz hk in
/-- The entire reverse critical kernel is normalized by the old endpoint
core. R₃ lies in both the seed orbit and this full kernel, and fixes the
old core and the full new endpoint seed. -/
theorem orbitKernel_control
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) ≤
      pointCore.map (MulAut.conj u).toMonoidHom)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    s.orbitDisplacement ≤ s.seedOrbit ⊓ s.orbitKernel ∧
      Q Rg a' ≤ normalizer (s.orbitKernel : Set (FreeAmalgam Rg)) ∧
      s.orbitDisplacement ≤ centralizer
        ((Q Rg a' ⊔ Z Rg s.endpoint : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  have hf := s.orbitDisplacement_full_core e hz hk hb u hR hsmall hslice heligible
  have hnD := (s.second_core_le_lineCentralizer (by omega)).trans
    s.centralizer_orbits_normalized.1
  have hDD : s.orbitDisplacement ≤ s.seedOrbit :=
    le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hnD)
  have hDK : s.orbitDisplacement ≤ s.orbitKernel := le_inf
    (hf.2.2.trans inf_le_left)
    ((s.orbitDisplacement_second_radius e hz hb).trans
      (inf_le_left.trans ((sourceGeometry h).V_le_Q (by change 2 < sourceDistance h; omega) _ s.path.start_color)))
  refine ⟨le_inf hDD hDK,?_,?_⟩
  · apply le_normalizer_iff_commutator_le_left.mpr
    rw [←hf.1]
    exact hDK
  · apply le_centralizer_iff.mp
    apply sup_le
    · have hn : Q Rg a' ≤ normalizer (s.orbitDisplacement : Set (FreeAmalgam Rg)) := by
        rw [hf.1]
        exact normalizer_commutator_ge_right _ _
      exact hn.trans (normalizer_le_centralizer_of_card_two _ hf.2.1)
    · apply le_centralizer_iff.mp
      let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) s.endpoint s.path.end_color
      exact (hf.2.2.trans inf_le_left).trans
        (le_centralizer_iff_isMulCommutative.mpr inferInstance)

include e hz hk in
/-- Adjoining the whole shifted span orbit does not enlarge R₃.
The same reverse kernel normalizes both orbits separately. -/
theorem full_orbit_kernel_commutator
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) ≤
      pointCore.map (MulAut.conj u).toMonoidHom)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    ⁅s.seedOrbit ⊔ s.spanOrbit,s.orbitKernel⁆ = s.orbitDisplacement ∧
      s.orbitKernel ≤ normalizer (s.seedOrbit : Set (FreeAmalgam Rg)) ⊓
        normalizer (s.spanOrbit : Set (FreeAmalgam Rg)) := by
  have ho := s.centralizer_orbits_le_old_endpoint_core e hz hk hb hsmall hslice heligible
  have hf := s.orbitDisplacement_full_core e hz hk hb u hR hsmall hslice heligible
  have hKC : s.orbitKernel ≤ s.lineCentralizer :=
    inf_le_right.trans (s.second_core_le_lineCentralizer (by omega))
  refine ⟨le_antisymm ?_ (commutator_mono le_sup_left le_rfl),
    le_inf (hKC.trans s.centralizer_orbits_normalized.1)
      (hKC.trans s.centralizer_orbits_normalized.2.1)⟩
  rw [hf.1,commutator_comm s.orbitKernel]
  exact commutator_mono (sup_le ho.1 ho.2) le_rfl

private theorem old_core_le_endpoint_stabilizer (hb : 2 < sourceDistance h) :
    Q Rg a' ≤ stabilizer Rg s.endpoint := by
  have hl : s.path.walk.length = sourceDistance h := s.path.length_eq_b
  have hp : s.path.walk.getVert (s.path.walk.length-2) = a' := by
    have hq : p.walk.length = sourceDistance h := p.length_eq_b
    rw [show s.path.walk.length-2 = p.walk.length-2 by omega,
      s.overlap _ (Nat.le_refl _),show p.walk.length-2+2=p.walk.length by omega,
      p.walk.getVert_length]
  let t := s.path.walk.getVert (s.path.walk.length-1)
  have het : Adjacent Rg s.endpoint t := by
    have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-1) (by omega)
    rw [show s.path.walk.length-1+1=s.path.walk.length by omega,
      s.path.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hpt : Adjacent Rg a' t := by
    rw [←hp]
    have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-2) (by omega)
    rw [show s.path.walk.length-2+1=s.path.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg het
    rw [s.path.end_color] at hh
    cases he : color Rg t <;> simp_all
  exact (Q_le_adjacent_h Rg ht hpt).trans
    (fun _ hx => hx.2 _ (adjacent_symm Rg het))

include e hz hk in
/-- If the full span orbit fixes the reverse kernel, the endpoint actor
normalizes it. The generating centralizer then makes the entire orbit
normal in the actual second local group. -/
theorem spanOrbit_normalized_of_kernel_fixed
    (hb : 4 < sourceDistance h)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (hfix : ⁅s.spanOrbit,s.orbitKernel⁆ = ⊥) :
    stabilizer Rg (p.walk.getVert 2) ≤ normalizer (s.spanOrbit : Set (FreeAmalgam Rg)) := by
  have ho := s.centralizer_orbits_le_old_endpoint_core e hz hk hb hsmall hslice heligible
  have hs : (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) < 4 := by
    rw [(s.shifted_indices e hz hk hb hsmall hslice heligible).1]
    decide
  have hcomm := small_critical_kernel_commutator h e hz hk s.path hs
    s.spanOrbit (ho.2.trans (s.old_core_le_endpoint_stabilizer (by omega)))
    (commutator_eq_bot_iff_le_centralizer.mp hfix)
  have hZ : Z Rg (p.walk.getVert 2) ≤ s.spanOrbit :=
    (Z_le_localZSpan Rg _ _).trans (le_conjugateSpanBy s.span s.lineCentralizer)
  have heG := critical_Z_le_stabilizer Rg (sourceGeometry h) (p.walk.getVert 2)
    s.path.start_color (by
      rw [(sourceGeometry h).distance_constant _ s.path.start_color]
      exact sourceDistance_pos h) s.path.critical
  have hbound : ⁅Z Rg (p.walk.getVert 2),Z Rg s.endpoint⁆ ≤ Z Rg (p.walk.getVert 2) :=
    le_normalizer_iff_commutator_le_left.mp (heG.trans (Z_normalized Rg _))
  rw [←s.centralizer_orbits_normalized.2.2]
  exact sup_le s.centralizer_orbits_normalized.2.1
    (le_normalizer_iff_commutator_le_left.mpr ((hcomm.trans hbound).trans hZ))

include e hz in
/-- The complete shifted span orbit lies in the second two-core as well
as the old endpoint core. Its generators commute with the second seed. -/
theorem spanOrbit_le_second_core (hb : 4 < sourceDistance h) :
    s.spanOrbit ≤ Q Rg (p.walk.getVert 2) := by
  let c := p.walk.getVert 2
  let t := act Rg s.conjugator⁻¹ (p.walk.getVert 1)
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hat : Adjacent Rg s.centerVertex t := by
    apply (adjacent_act_iff Rg s.conjugator⁻¹ _ _).mpr
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := by
    have hh := adjacent_symm Rg
      ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
    have hh' := (adjacent_act_iff Rg s.conjugator⁻¹ _ _).mpr hh
    simpa only [s.fixes_second] using hh'
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [s.center_color] at hh
    cases he : color Rg t <;> simp_all
  have hdist : (cosetGraph Rg).dist c s.centerVertex ≤ 2 := by
    have he : (cosetGraph Rg).dist (act Rg s.conjugator⁻¹ c) s.centerVertex =
        (cosetGraph Rg).dist c (alpha Rg) := dist_act Rg _ _ _
    rw [s.fixes_second,SimpleGraph.dist_comm (u := c) (v := alpha Rg),
      p.dist_start (by omega)] at he
    exact he.le
  have hPQ : s.span ≤ Q Rg s.centerVertex := localZSpan_le_Q Rg s.center_color hdist
    (by change 2 < sourceDistance h; omega)
  have hPG : s.span ≤ stabilizer Rg c :=
    (hPQ.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hab : ⁅s.span,s.span⁆ = ⊥ := by
    rw [s.span_map,←map_commutator,selected_span_abelian_of_four_lt h hb p,Subgroup.map_bot]
  have hPC : s.span ≤ centralizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp hab).trans
      (centralizer_le (Z_le_localZSpan Rg _ _))
  have hP := two_subgroup_seed_centralizer_le_core h e hz s.path.start_color s.span
    ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le _
      s.center_color).to_le hPQ) (le_inf hPG hPC)
  exact conjugateSpanBy_le hP (inf_le_left.trans (Q_normalized Rg c))


include e hz hk in
private theorem normal_section_residual_control {c d : Vertex Rg}
    (q : CriticalPath Rg (sourceGeometry h) c d)
    (D : Subgroup (FreeAmalgam Rg)) (hDG : D ≤ stabilizer Rg c)
    (hDN : stabilizer Rg c ≤ normalizer (D : Set (FreeAmalgam Rg)))
    (hcomm : ⁅D,Z Rg d⁆ ≤ Z Rg c) : ⁅D,Ltilde Rg c⁆ ≤ Z Rg c := by
  obtain ⟨i,hi,hir,hiQ,_⟩ := graph_cover h e hz hk c q.start_color
  let D₀ := D.comap i
  let Z₀ := (Z Rg c).comap i
  let A₀ := (Z Rg d).comap i
  have hDm : D₀.map i = D := map_comap_eq_self (hDG.trans_eq hir.symm)
  have hZm : Z₀.map i = Z Rg c :=
    map_comap_eq_self ((Z_le_stabilizer Rg c).trans_eq hir.symm)
  have hAm : A₀.map i = Z Rg d := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) c q.start_color
      (by rw [(sourceGeometry h).distance_constant _ q.start_color]; exact sourceDistance_pos h)
      q.critical).trans_eq hir.symm)
  have hg (m : (L ⊔ R : Subgroup G)) : i m ∈ stabilizer Rg c := by
    rw [←hir]
    exact ⟨m,rfl⟩
  let : D₀.Normal := ⟨by
    intro z hd m
    change i (m*z*m⁻¹) ∈ D
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hDN (hg m)) (i z)).mp hd⟩
  let : Z₀.Normal := ⟨by
    intro z hd m
    change i (m*z*m⁻¹) ∈ Z Rg c
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp ((Z_normalized Rg _) (hg m)) (i z)).mp hd⟩
  have hcomm₀ : ⁅D₀,A₀⁆ ≤ Z₀ := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [map_commutator,hDm,hAm,hZm]
  have hne : ¬ A₀ ≤ pCore 2 (L ⊔ R : Subgroup G) := by
    intro he
    have hh := map_mono (f := i) he
    rw [hAm,hiQ] at hh
    exact (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      c q.start_color (by
        rw [(sourceGeometry h).distance_constant _ q.start_color]
        exact sourceDistance_pos h) d q.end_color q.critical).2 hh
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) d q.end_color
  have hAtwo : IsPGroup 2 A₀ :=
    (IsElementaryAbelian.isPGroup 2 (Z Rg d)).comap_of_injective i hi
  have hm := map_mono (f := i)
    (CubicAction.normal_commutator_le_of_escaping_two h e hz D₀ Z₀ A₀ hAtwo hne hcomm₀)
  let j : (L ⊔ R : Subgroup G) →* stabilizer Rg c := i.codRestrict _ hg
  have hjs : Function.Surjective j := by
    intro x
    have hx : (x : FreeAmalgam Rg) ∈ i.range := hir.symm ▸ x.property
    obtain ⟨m,hm⟩ := hx
    exact ⟨m,Subtype.ext hm⟩
  have hj : (stabilizer Rg c).subtype.comp j = i := rfl
  have hLm : (L.subgroupOf (L ⊔ R)).map i = Ltilde Rg c := by
    rw [←h.relative_residual,←hj,←map_map,map_pResidual_of_surjective 2 j hjs]
    rfl
  rwa [map_commutator,hDm,hZm,hLm] at hm

include e hz hk in
/-- In the fixed-kernel branch the orbit actually equals the original
shifted span. Its residual is fixed modulo the second seed, while the
literal intervening edge core already normalizes the original span. -/
theorem spanOrbit_eq_span_of_kernel_fixed
    (hb : 4 < sourceDistance h)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (hfix : ⁅s.spanOrbit,s.orbitKernel⁆ = ⊥) : s.spanOrbit = s.span := by
  let c := p.walk.getVert 2
  let t := act Rg s.conjugator⁻¹ (p.walk.getVert 1)
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hat : Adjacent Rg s.centerVertex t := by
    apply (adjacent_act_iff Rg s.conjugator⁻¹ _ _).mpr
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := by
    have hh := adjacent_symm Rg
      ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
    have hh' := (adjacent_act_iff Rg s.conjugator⁻¹ _ _).mpr hh
    simpa only [s.fixes_second] using hh'
  have hZG : Z Rg s.endpoint ≤ stabilizer Rg c :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) c s.path.start_color
      (by rw [(sourceGeometry h).distance_constant _ s.path.start_color]; exact sourceDistance_pos h)
      s.path.critical
  have ho := s.centralizer_orbits_le_old_endpoint_core e hz hk hb hsmall hslice heligible
  have hs : (Q Rg s.endpoint).relIndex (Z Rg c) < 4 := by
    rw [(s.shifted_indices e hz hk hb hsmall hslice heligible).1]
    decide
  have hcomm := (small_critical_kernel_commutator h e hz hk s.path hs
    s.spanOrbit (ho.2.trans (s.old_core_le_endpoint_stabilizer (by omega)))
    (commutator_eq_bot_iff_le_centralizer.mp hfix)).trans
      (le_normalizer_iff_commutator_le_left.mp (hZG.trans (Z_normalized Rg c)))
  have hnorm := s.spanOrbit_normalized_of_kernel_fixed e hz hk hb hsmall hslice heligible hfix
  have hres := normal_section_residual_control e hz hk s.path s.spanOrbit
    ((s.spanOrbit_le_second_core e hz hb).trans (fun _ hx => hx.1)) hnorm hcomm
  have hP : s.span ≤ s.spanOrbit := le_conjugateSpanBy _ _
  have hN : stabilizer Rg c ≤ normalizer (s.span : Set (FreeAmalgam Rg)) := by
    rw [←CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
      (by rw [h.relative_residual]; exact (codisjoint_subgroupOf_sup L R).eq_top)
      s.path.start_color hct]
    apply sup_le
    · exact le_normalizer_iff_commutator_le_left.mpr
        (((commutator_mono hP le_rfl).trans hres).trans (Z_le_localZSpan Rg _ _))
    · exact (show Q Rg t ≤ stabilizer Rg s.centerVertex from
        fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (localZSpan_normalized Rg _ _)
  exact le_antisymm (conjugateSpanBy_le le_rfl (inf_le_left.trans hN)) hP

include e hz hk in
/-- The full source span either stabilizes in the second local group or
has exactly R₃ as its reverse-kernel commutator. In the latter case the
order-two line is inside the span orbit itself. -/
theorem spanOrbit_stabilization_or_displacement
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) ≤
      pointCore.map (MulAut.conj u).toMonoidHom)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    (s.spanOrbit = s.span ∧ stabilizer Rg (p.walk.getVert 2) ≤
      normalizer (s.spanOrbit : Set (FreeAmalgam Rg))) ∨
      (⁅s.spanOrbit,s.orbitKernel⁆ = s.orbitDisplacement ∧
        s.orbitDisplacement ≤ s.spanOrbit) := by
  by_cases he : ⁅s.spanOrbit,s.orbitKernel⁆ = ⊥
  · exact Or.inl ⟨s.spanOrbit_eq_span_of_kernel_fixed e hz hk hb hsmall hslice heligible he,
      s.spanOrbit_normalized_of_kernel_fixed e hz hk hb hsmall hslice heligible he⟩
  · have hf := s.full_orbit_kernel_commutator e hz hk hb u hR hsmall hslice heligible
    have hle : ⁅s.spanOrbit,s.orbitKernel⁆ ≤ s.orbitDisplacement :=
      (commutator_mono le_sup_right le_rfl).trans_eq hf.1
    have hc := (s.orbitDisplacement_full_core e hz hk hb u hR hsmall hslice heligible).2.1
    let : Finite s.orbitDisplacement := Nat.finite_of_card_ne_zero (by omega)
    let : Finite (⁅s.spanOrbit,s.orbitKernel⁆ : Subgroup (FreeAmalgam Rg)) :=
      Finite.of_injective (inclusion hle) (inclusion_injective _)
    have hpos := (one_lt_card_iff_ne_bot _).mpr he
    have heq := eq_of_le_of_card_ge hle (by omega)
    exact Or.inr ⟨heq,heq ▸ le_normalizer_iff_commutator_le_left.mp
      (hf.2.trans inf_le_right)⟩

end SmallSliceShift
omit hk in
include e hz in
/-- The literal whole-core consumer supplies the shift and the full reverse
kernel. The span orbit stabilizes when its kernel commutator vanishes;
otherwise its entire commutator is the same order-two R₃. -/
theorem coreExhaustion_or_cubic_orbit_kernel_control :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          4 < sourceDistance h →
          (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ≤ 2 →
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) →
          ∃ s : SmallSliceShift h p,
            s.seedOrbit ⊔ s.spanOrbit ≤ Q Rg a' ⊓ Q Rg (p.walk.getVert 2) ∧
            Nat.card s.orbitDisplacement = 2 ∧
            s.orbitDisplacement ≤ s.seedOrbit ⊓ s.orbitKernel ∧
            Q Rg a' ≤ normalizer (s.orbitKernel : Set (FreeAmalgam Rg)) ∧
            s.orbitDisplacement ≤ centralizer
              ((Q Rg a' ⊔ Z Rg s.endpoint : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
            s.orbitDisplacement ≤ centralizer (V Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) ∧
            ⁅s.seedOrbit ⊔ s.spanOrbit,s.orbitKernel⁆ = s.orbitDisplacement ∧
            ((s.spanOrbit = s.span ∧ stabilizer Rg (p.walk.getVert 2) ≤
                normalizer (s.spanOrbit : Set (FreeAmalgam Rg))) ∨
              (⁅s.spanOrbit,s.orbitKernel⁆ = s.orbitDisplacement ∧
                s.orbitDisplacement ≤ s.spanOrbit)) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,?_⟩
    intro u hfull a' p hb4 hsmall hslice hel
    obtain ⟨s⟩ := exists_small_slice_shift h e hz hk hb u hfull p hsmall hslice hel
    have ho := s.centralizer_orbits_le_old_endpoint_core e hz hk hb4 hsmall hslice hel
    have hc := s.orbitKernel_control e hz hk hb4 u hfull.le hsmall hslice hel
    have hQ : s.seedOrbit ⊔ s.spanOrbit ≤ Q Rg (p.walk.getVert 2) := sup_le
      ((s.seedOrbit_radius_and_escape e hz hb).1.trans
        ((sourceGeometry h).V_le_Q hb _ s.path.start_color))
      (s.spanOrbit_le_second_core e hz hb4)
    exact ⟨s,le_inf (sup_le ho.1 ho.2) hQ,
      (s.orbitDisplacement_full_core e hz hk hb4 u hfull.le hsmall hslice hel).2.1,
      hc.1,hc.2.1,hc.2.2,(s.orbitDisplacement_second_radius e hz hb4).trans inf_le_right,
      (s.full_orbit_kernel_commutator e hz hk hb4 u hfull.le hsmall hslice hel).1,
      s.spanOrbit_stabilization_or_displacement e hz hk hb4 u hfull.le hsmall hslice hel⟩

omit hk in
include e hz in
/-- Literal C.1.32 application on the same original graph. Second-local
group centrality of R₃ and the remaining source exclusions are still required. -/
theorem rankTwo_or_cubic_orbit_kernel_control :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          4 < sourceDistance h →
          (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ≤ 2 →
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) →
          ∃ s : SmallSliceShift h p,
            s.seedOrbit ⊔ s.spanOrbit ≤ Q Rg a' ⊓ Q Rg (p.walk.getVert 2) ∧
            Nat.card s.orbitDisplacement = 2 ∧
            s.orbitDisplacement ≤ s.seedOrbit ⊓ s.orbitKernel ∧
            Q Rg a' ≤ normalizer (s.orbitKernel : Set (FreeAmalgam Rg)) ∧
            s.orbitDisplacement ≤ centralizer
              ((Q Rg a' ⊔ Z Rg s.endpoint : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
            s.orbitDisplacement ≤ centralizer (V Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) ∧
            ⁅s.seedOrbit ⊔ s.spanOrbit,s.orbitKernel⁆ = s.orbitDisplacement ∧
            ((s.spanOrbit = s.span ∧ stabilizer Rg (p.walk.getVert 2) ≤
                normalizer (s.spanOrbit : Set (FreeAmalgam Rg))) ∨
              (⁅s.spanOrbit,s.orbitKernel⁆ = s.orbitDisplacement ∧
                s.orbitDisplacement ≤ s.spanOrbit)) :=
  (coreExhaustion_or_cubic_orbit_kernel_control e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
