module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.ForwardShifts
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOrbitKernelControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.EqualKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.EndSlices
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.UncontrolledKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOrbitDisplacement

/-!
# Whole-orbit reverse-kernel control on the original Borel graph

Above distance four, the complete shifted seed orbit acts quadratically
and nontrivially on the full reverse critical kernel. Quadratic action on
the critical transposition's fixed hyperplane forces elementary permutation
image. The Borel cover calculation gives either endpoint control modulo
that kernel displacement or an order-two displacement, for both moving covers.

In the controlled alternative the whole orbit joined to the second seed
is normal in the second stabilizer. In the line alternative an actual
conjugate seed realizes R₃; the entire reverse kernel belongs to its proper
Thompson mover, which fixes the same line. The original cubic kernel E,
whole seeds, and all central attachments are retained.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), pp.866--867,
and (5.9), p.921. These are orbit-control steps, not strictness or exhaustion.
The source exclusion of the normal alternative, full stabilizer centrality
of R₃, orbit stabilization, and the terminal distance exclusions remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
local notation "borel" => Theory.SpecificGroups.SymmetricSix.borel
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)
open Representation.NormalElementaryQuotient

include h e hz hk in
/-- A quadratic actor in both cores either controls the full endpoint
modulo the reverse-kernel displacement, or that displacement has order at most two. -/
theorem borel_quadratic_reverse_kernel_control_or_card
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (T : Subgroup (FreeAmalgam Rg))
    (hT : T ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hTa : T ≤ Q Rg a)
    (hquad : ⁅⁅Z Rg z ⊓ Q Rg a,T⁆,T⁆ = ⊥) :
    (⁅T,Z Rg z⁆ ≤ Z Rg a ⊔ ⁅Z Rg z ⊓ Q Rg a,T⁆) ∨
    Nat.card (⁅Z Rg z ⊓ Q Rg a,T⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
  by_cases hescape : ⁅T,Z Rg z⁆ ≤ Z Rg a ⊔ ⁅Z Rg z ⊓ Q Rg a,T⁆
  · exact Or.inl hescape
  apply Or.inr
  have hb := distance_gt_two h e hz hk
  have hfixed : ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),T⁆ =
      ⁅Z Rg z ⊓ Q Rg a,T⁆ := by
    rw [←critical_moving_kernel_eq_fixed h e p]
    exact ((critical_kernel_predecessor_moving h e hz hb p).2.2 _ hT).symm
  have hcontrol : ¬ ⁅U Rg z,T⁆ ≤
      ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),T⁆ ⊔ ⁅U Rg z,Z Rg a⁆ := by
    intro hh
    apply hescape
    rw [commutator_comm,critical_predecessor_seed_movement h e hz hb p _ hT]
    rw [hfixed] at hh
    exact hh.trans (sup_le le_sup_right (by
      rw [commutator_comm]
      exact ((commutator_mono le_rfl (DistanceEight.U_le_Z Rg z)).trans
        (critical_seed_commutator_le h p)).trans le_sup_left))
  let := h.relative_normal
  obtain ⟨i,hi,hir,hiR,hiQ,hiU,hA,hP,hJ,hAr,hPr,hJr,hApi,hPpi,hJpi,hFi,hfix⟩ :=
    borel_predecessor_cover_chart h e hz hk u hR p T hT 1 (one_mem _)
  obtain ⟨⟨τ,hτ,hτswap,hτeq⟩,hcrit⟩ :=
    plane_small_critical_chart_actor h e hz hk p hp i hi hiQ hiU hA hAr
  let A := (Z Rg a).comap i
  let P := T.comap i
  let F := W₀ ⊓ centralizer (A : Set M)
  let σ : Representation (ZMod 2) S (Additive W₀) :=
    NormalElementaryQuotient.representation W₀ π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)
  have hF : F.map i = U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) := by
    rw [←map_inf_centralizer_of_injective i hi,hiU,hA]
  have hQ : ⁅⁅F,P⁆,P⁆ = ⊥ := by
    apply (map_injective (f := i) hi)
    rw [map_commutator,map_commutator,hF,hP,hfixed,Subgroup.map_bot]
    exact hquad
  have hFs : subgroupSpace W₀ F = fixedSpace σ (zpowers τ) := by
    rw [←hτeq]
    ext v
    change ((v.toMul : M) ∈ W₀ ∧ (v.toMul : M) ∈ centralizer (A : Set M)) ↔ _
    rw [NormalElementaryQuotient.mem_fixedSpace_image W₀ π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)]
    exact and_iff_right v.toMul.property
  have hq : subspaceCommutator σ
      (subspaceCommutator σ (fixedSpace σ (zpowers τ)) (P.map π)) (P.map π) = ⊥ := by
    rw [←hFs,←subgroupSpace_commutator W₀ π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) F P inf_le_left,
      ←subgroupSpace_commutator W₀ π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) ⁅F,P⁆ P
        ((commutator_mono inf_le_left le_rfl).trans (commutator_le_left _ _)),hQ]
    ext v
    change (v.toMul : M) = 1 ↔ v = 0
    exact ⟨fun hv => Additive.toMul.injective (Subtype.ext hv),fun hv => hv ▸ rfl⟩
  obtain ⟨h2,hab⟩ := quadratic_cover_elementary σ (moved_subgroup_cover_model h e hz hk) τ hτswap (P.map π) hq
  have hcomm : ∀ g ∈ P.map π, Commute τ g := by
    obtain ⟨j,hj,hje⟩ := hτ
    rintro _ ⟨g,hg,rfl⟩
    rw [←hje]
    change _ * _ = _ * _
    rw [←map_mul,←map_mul]
    congr 1
    apply hi
    simp only [map_mul]
    exact (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)
      hj (i g) (hTa hg)).symm
  have hbound := borel_cover_uncontrolled_fixed_card h e hz hk u τ (hApi hτ)
    hτswap A P hτeq hPpi h2 hab hcomm (by
      intro hh
      apply hcontrol
      have hm := map_mono (f := i) hh
      rwa [Subgroup.map_sup,map_commutator W₀ P i,hiU,hP,
        map_commutator _ P i,hF,hP,map_commutator W₀ A i,hiU,hA] at hm)
  rw [←card_map_of_injective hi,map_commutator,hF,hP,hfixed] at hbound
  exact hbound

end AlternatingSixReconstruction.Exceptional.OriginalSylow
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open AlternatingSixReconstruction.Exceptional.OriginalSylow
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

private theorem borel_orbit_predecessor (hb : 2 < sourceDistance h) :
    s.path.walk.getVert (s.path.walk.length-2) = a' := by
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hq : s.path.walk.length = sourceDistance h := s.path.length_eq_b
  rw [show s.path.walk.length-2 = p.walk.length-2 by omega,
    s.overlap _ (Nat.le_refl _),show p.walk.length-2+2=p.walk.length by omega,
    p.walk.getVert_length]

include e hz hk in
/-- The whole Borel seed orbit moves the entire reverse kernel nontrivially.
The commutator lies in both the orbit and the kernel, and the orbit fixes it.
No cardinal bound on the full predecessor-core commutator is assumed. -/
theorem borel_orbit_displacement_nonzero_quadratic
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) =
      Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    s.orbitDisplacement ≠ ⊥ ∧
      s.orbitDisplacement ≤ s.seedOrbit ⊓ s.orbitKernel ∧
      ⁅s.orbitDisplacement,s.seedOrbit⁆ = ⊥ := by
  have hb2 : 2 < sourceDistance h := by omega
  have hel := (borel_critical_paths h e hz hk u hR p).2.2.2
  have hpre := s.borel_orbit_predecessor hb2
  have ho := s.borel_centralizer_orbits_le_old_endpoint_core e hz hk hb u hR hslice hel
  have hDpre : s.seedOrbit ≤ Q Rg (s.path.walk.getVert (s.path.walk.length-2)) := by
    rw [hpre]
    exact ho.1
  have hs : (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) < 4 := by
    rw [(s.borel_shifted_indices e hz hk hb u hR hslice hel).1]
    decide
  have hne : s.orbitDisplacement ≠ ⊥ := by
    intro he
    exact s.seedOrbit_endpoint_commutator_not_le e hz hb2
      (small_critical_predecessor_commutator h e hz hk hb2 s.path hs
        s.seedOrbit hDpre (commutator_eq_bot_iff_le_centralizer.mp he))
  have hc := s.path.start_color
  have hDV := (s.seedOrbit_radius_and_escape e hz hb2).1
  have hDC := s.orbitDisplacement_second_radius e hz hb
  have hQG : Q Rg a' ≤ stabilizer Rg s.endpoint := by
    apply Q_le_stabilizer_of_dist_le_two a' s.endpoint p.end_color s.path.end_color
    have hd := s.path.dist_end (s.path.walk.length-2)
    rw [hpre] at hd
    have hl : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    exact hd.le.trans (by omega)
  have hDZ : s.orbitDisplacement ≤ Z Rg s.endpoint :=
    (commutator_mono le_rfl (show s.orbitKernel ≤ Z Rg s.endpoint from inf_le_left)).trans
      (le_normalizer_iff_commutator_le_right.mp
        ((ho.1.trans hQG).trans (Z_normalized Rg _)))
  have hDD : s.orbitDisplacement ≤ s.seedOrbit :=
    le_normalizer_iff_commutator_le_left.mp
      (inf_le_right.trans ((s.second_core_le_lineCentralizer hb2).trans
        s.centralizer_orbits_normalized.1))
  have hDK : s.orbitDisplacement ≤ s.orbitKernel := le_inf hDZ
    (hDC.trans (inf_le_left.trans ((sourceGeometry h).V_le_Q hb2 _ hc)))
  exact ⟨hne,le_inf hDD hDK,commutator_eq_bot_iff_le_centralizer.mpr
    (hDC.trans (inf_le_right.trans (centralizer_le hDV)))⟩

include e hz hk in
/-- The complete R₃ orbit calculation has two alternatives: endpoint
displacement is controlled by R₃ and the starting seed, or R₃ has order two.
The quadratic hypothesis is discharged on the actual original Borel orbit. -/
theorem borel_orbit_control_or_line
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) =
      Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    (⁅s.seedOrbit,Z Rg s.endpoint⁆ ≤ Z Rg (p.walk.getVert 2) ⊔ s.orbitDisplacement) ∨
      Nat.card s.orbitDisplacement = 2 := by
  have hb2 : 2 < sourceDistance h := by omega
  have hel := (borel_critical_paths h e hz hk u hR p).2.2.2
  have ho := s.borel_centralizer_orbits_le_old_endpoint_core e hz hk hb u hR hslice hel
  have hDpre : s.seedOrbit ≤ Q Rg (s.path.walk.getVert (s.path.walk.length-2)) := by
    rw [s.borel_orbit_predecessor hb2]
    exact ho.1
  have hDQ : s.seedOrbit ≤ Q Rg (p.walk.getVert 2) :=
    (s.seedOrbit_radius_and_escape e hz hb2).1.trans
      ((sourceGeometry h).V_le_Q hb2 _ s.path.start_color)
  have hs : (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) < 4 := by
    rw [(s.borel_shifted_indices e hz hk hb u hR hslice hel).1]
    decide
  have hf := s.borel_orbit_displacement_nonzero_quadratic e hz hk hb u hR hslice
  have hquad : ⁅⁅Z Rg s.endpoint ⊓ Q Rg (p.walk.getVert 2),s.seedOrbit⁆,s.seedOrbit⁆ = ⊥ := by
    rw [commutator_comm (Z Rg s.endpoint ⊓ Q Rg (p.walk.getVert 2))]
    exact hf.2.2
  have hd := borel_quadratic_reverse_kernel_control_or_card h e hz hk u hR s.path hs
    s.seedOrbit hDpre hDQ hquad
  rw [commutator_comm (Z Rg s.endpoint ⊓ Q Rg (p.walk.getVert 2))] at hd
  rcases hd with hcontrol | hcard
  · exact Or.inl hcontrol
  · right
    change Nat.card s.orbitDisplacement ≤ 2 at hcard
    let := finite_Z Rg s.endpoint
    let : Finite s.orbitDisplacement := Finite.of_injective
      (inclusion (hf.2.1.trans (inf_le_right.trans inf_le_left))) (inclusion_injective _)
    have hp := (one_lt_card_iff_ne_bot s.orbitDisplacement).mpr hf.1
    omega

include e hz hk in
/-- In the controlled alternative the seed orbit joined to the whole seed
is normalized by the full second stabilizer. Otherwise an actual conjugate
seed realizes the nonzero order-two R₃. -/
theorem borel_orbit_normalized_or_line
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) =
      Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    (stabilizer Rg (p.walk.getVert 2) ≤ normalizer
      ((s.seedOrbit ⊔ Z Rg (p.walk.getVert 2) : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) ∨
      (Nat.card s.orbitDisplacement = 2 ∧ ∃ t ∈ s.lineCentralizer,
        ⁅(Z Rg s.centerVertex).map (MulAut.conj t).toMonoidHom,s.orbitKernel⁆ =
          s.orbitDisplacement) := by
  rcases s.borel_orbit_control_or_line e hz hk hb u hR hslice with hc | hl
  · left
    let c := p.walk.getVert 2
    let D := s.seedOrbit ⊔ Z Rg c
    have hDZ : s.orbitDisplacement ≤ D :=
      ((s.borel_orbit_displacement_nonzero_quadratic e hz hk hb u hR hslice).2.1.trans
        inf_le_left).trans le_sup_left
    have hDnorm : stabilizer Rg c ≤ normalizer (D : Set (FreeAmalgam Rg)) := by
      rw [←s.centralizer_orbits_normalized.2.2]
      apply sup_le
      · exact (le_inf s.centralizer_orbits_normalized.1
          (inf_le_left.trans (Z_normalized Rg c))).trans
            (normalizer_inf_normalizer_le_normalizer_sup _ _)
      · have hEN := (critical_Z_le_stabilizer Rg (sourceGeometry h) c s.path.start_color
          (by rw [(sourceGeometry h).distance_constant c s.path.start_color]; exact sourceDistance_pos h)
          s.path.critical).trans (Z_normalized Rg c)
        have hE : ⁅s.seedOrbit,Z Rg s.endpoint⁆ ≤ D :=
          hc.trans (sup_le le_sup_right hDZ)
        apply le_normalizer_iff.mpr
        intro x hx v hv
        have hm : D.map (MulAut.conj x).toMonoidHom ≤ D := by
          rw [Subgroup.map_sup]
          refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hEN hx)).le.trans le_sup_right)
          rintro _ ⟨y,hy,rfl⟩
          rw [commutator_comm] at hE
          have hm := D.mul_mem (hE (commutator_mem_commutator hx hy)) (mem_sup_left hy)
          simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hm
        exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hv)
    exact hDnorm
  · exact Or.inr ⟨hl,s.exists_seed_conjugate_orbitDisplacement hl⟩

include e hz hk in
/-- An actual conjugate seed realizing R₃ places the entire reverse kernel
in its proper Borel Thompson mover. That mover centralizes the same R₃. -/
theorem borel_orbit_line_mover
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) =
      Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hcard : Nat.card s.orbitDisplacement = 2) :
    ∃ x ∈ s.lineCentralizer, ∃ t : Vertex Rg,
      Adjacent Rg (act Rg x⁻¹ s.centerVertex) t ∧
      Adjacent Rg (p.walk.getVert 2) t ∧
      ⁅Z Rg (act Rg x⁻¹ s.centerVertex),s.orbitKernel⁆ = s.orbitDisplacement ∧
      s.orbitKernel ≤ edgeOffenderJoin (act Rg x⁻¹ s.centerVertex) t ∧
      s.orbitDisplacement ≤ centralizer
        (edgeOffenderJoin (act Rg x⁻¹ s.centerVertex) t : Set (FreeAmalgam Rg)) := by
  obtain ⟨x,hx,hline⟩ := s.exists_seed_conjugate_orbitDisplacement hcard
  let t₀ := act Rg s.conjugator⁻¹ (p.walk.getVert 1)
  let t := act Rg x⁻¹ t₀
  let c := p.walk.getVert 2
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hct₀ : Adjacent Rg c t₀ := by
    have ha := adjacent_symm Rg
      ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
    simpa only [s.fixes_second] using (adjacent_act_iff Rg s.conjugator⁻¹ _ _).mpr ha
  have hat₀ : Adjacent Rg s.centerVertex t₀ := by
    apply (adjacent_act_iff Rg s.conjugator⁻¹ _ _).mpr
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hxc : act Rg x⁻¹ c = c := (stabilizer Rg c).inv_mem hx.1
  have hct : Adjacent Rg c t := by
    simpa only [hxc] using (adjacent_act_iff Rg x⁻¹ _ _).mpr hct₀
  have hat : Adjacent Rg (act Rg x⁻¹ s.centerVertex) t :=
    (adjacent_act_iff Rg x⁻¹ _ _).mpr hat₀
  have ha : color Rg (act Rg x⁻¹ s.centerVertex) = false := by
    rw [action_preserves_color,s.center_color]
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [ha] at hh
    cases he : color Rg t <;> simp_all
  have hKT : s.orbitKernel ≤ Q Rg t :=
    inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hline' : ⁅Z Rg (act Rg x⁻¹ s.centerVertex),s.orbitKernel⁆ = s.orbitDisplacement := by
    simpa only [Z_act,inv_inv] using hline
  have hbound : Nat.card (⁅U Rg (act Rg x⁻¹ s.centerVertex),s.orbitKernel⁆ :
      Subgroup (FreeAmalgam Rg)) ≤ 2 := by
    let : Finite s.orbitDisplacement := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
    have he := (commutator_mono (DistanceEight.U_le_Z Rg _) le_rfl).trans_eq hline'
    exact (card_le_of_le he).trans hcard.le
  have hKJ := borel_small_commutator_actor_le_mover h e hz hk u hR ha hat
    s.orbitKernel hKT hbound
  have hquad : ⁅s.orbitDisplacement,edgeOffenderJoin (act Rg x⁻¹ s.centerVertex) t⁆ = ⊥ := by
    rw [←hline']
    exact le_bot_iff.mp ((commutator_mono (commutator_mono le_rfl hKJ) le_rfl).trans_eq
      (remaining_edge_full_seed_quadratic h e hz hk u (Or.inr hR) ha hat))
  exact ⟨x,hx,t,hat,hct,hline',hKJ,commutator_eq_bot_iff_le_centralizer.mp hquad⟩

end SmallSliceShift
end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
