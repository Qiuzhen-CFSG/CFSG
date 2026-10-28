module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOrbitDisplacement

/-!
# Restricted shifts and the full orbit commutator

A large shifted critical image admits a subgroup of the entire moving
cover which preserves its critical commutator, escapes the starting
two-core, and controls displacement by every subgroup of that two-core
in the endpoint stabilizer. Choose the shifted line using this restricted
actor. The full line-centralizer orbit would then be normal modulo the
second seed and lie in its Baumann slice, contradicting its proved escape.
Thus both shifted critical indices equal two for either cover order.

The orbit commutator consequently has order two. It exhausts the
commutator of the entire reverse critical kernel with the old endpoint's
two-core and centralizes that endpoint's radius. This description proves
independence from the residual conjugator at a fixed shifted endpoint.
The whole-core and literal C.1.32 consumers discharge the former shifted
smallness premise, retaining both covers and the odd covering kernel.

Centrality of R₃ in the second local group, orbit stabilization and strict
slices, the remaining radical and distance branches, R4/R6 and MS93
(5.11)--(5.12), natural exhaustion and both final reconstruction outcomes
remain required. No centrality in the second local group is asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), pp.866--867,
and (5.9), pp.920--922, particularly the restricted choice (**), the
shifted index and the independence of R₃ from the residual conjugator.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local notation "Rg" => edge L R
include h e hz hk in
/-- The simultaneous generating-centralizer and noncentral-line choice on
the actual graph, with the conjugator in the original local two-residual. -/
theorem exists_cover_line_generator_of_actor
    {a : Vertex Rg} (ha : color Rg a = false)
    (A₁ : Subgroup (FreeAmalgam Rg))
    (hAG : A₁ ≤ stabilizer Rg a) (htwo : IsPGroup 2 A₁)
    (hescape : ¬ A₁ ≤ Q Rg a)
    (H : Subgroup (FreeAmalgam Rg)) (hHU : H ≤ U Rg a)
    (hcard : Nat.card H = 2)
    (hcentral : ¬ H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) :
    ∃ g ∈ Ltilde Rg a,
      (stabilizer Rg a ⊓ centralizer
        (H.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam Rg))) ⊔
          A₁ = stabilizer Rg a ∧
      ¬ H.map (MulAut.conj g).toMonoidHom ≤ centralizer
        (A₁ : Set (FreeAmalgam Rg)) := by
  classical
  obtain ⟨z,hzn,hunique⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hcard
  have hznot : (z : FreeAmalgam Rg) ∉ centralizer
      (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    intro hz
    apply hcentral
    intro x hx
    by_cases hx1 : x = 1
    · exact hx1 ▸ one_mem _
    · have he : (⟨x,hx⟩ : H) = z := hunique _ (fun he => hx1 (congrArg Subtype.val he))
      have hxz : x = (z : FreeAmalgam Rg) := congrArg Subtype.val he
      rw [hxz]
      exact hz
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,_⟩ := graph_cover h e hz hk a ha
  obtain ⟨v,hv,hvz⟩ := (show (z : FreeAmalgam Rg) ∈ (W).map i from
    hiU.symm ▸ hHU z.property)
  have hvnot : v ∉ center M := by
    intro hv
    apply hznot
    intro m hm
    obtain ⟨m,rfl⟩ := hir.symm ▸ hm
    rw [←hvz,←map_mul,←map_mul]
    exact congrArg i (mem_center_iff.mp hv m)
  have hA : A₁ ≤ i.range := hAG.trans_eq hir.symm
  let A := A₁.comap i
  have hmA : A.map i = A₁ := map_comap_eq_self hA
  have hnA : ¬ A ≤ extensionKernel h := by
    intro he
    have ht : IsPGroup 2 A := htwo.comap_of_injective i hi
    have hh := map_mono (f := i)
      (two_subgroup_le_core_of_le_extensionKernel h hz A ht he)
    rw [hmA,hiQ] at hh
    exact hescape hh
  obtain ⟨g,hg,hgen,hmove⟩ := exists_cover_conjugate_generator h e hz hk ⟨v,hv⟩ hvnot A hnA
  let j : M →* stabilizer Rg a :=
    i.codRestrict _ (fun x => hir ▸ (show i x ∈ i.range from ⟨x,rfl⟩))
  have hgL : i g ∈ Ltilde Rg a := by
    have hg' : g ∈ pResidual 2 M := (h.relative_residual).symm ▸ hg
    exact mem_map_of_mem (stabilizer Rg a).subtype
      ((map_pResidual_le 2 j) (mem_map_of_mem j hg'))
  let C := centralizer ({g * v * g⁻¹} : Set M)
  let HC := H.map (MulAut.conj (i g)).toMonoidHom
  have hC : C.map i ≤ stabilizer Rg a ⊓
      centralizer (HC : Set (FreeAmalgam Rg)) := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨hir ▸ (show i x ∈ i.range from ⟨x,rfl⟩),?_⟩
    rintro y ⟨w,hw,rfl⟩
    by_cases hw1 : w = 1
    · simp only [hw1,map_one,one_mul,mul_one]
    · have he : (⟨w,hw⟩ : H) = z := hunique _ (fun he => hw1 (congrArg Subtype.val he))
      have hwz : w = (z : FreeAmalgam Rg) := congrArg Subtype.val he
      rw [hwz,←hvz]
      change (i g * i v * (i g)⁻¹) * i x = i x * (i g * i v * (i g)⁻¹)
      simpa only [map_mul,map_inv] using congrArg i
        (mem_centralizer_singleton_iff.mp hx).symm
  refine ⟨i g,hgL,?_,?_⟩
  · apply le_antisymm (sup_le inf_le_left (hA.trans_eq hir))
    have hm := congrArg (Subgroup.map i) hgen
    rw [Subgroup.map_sup,hmA,←MonoidHom.range_eq_map,hir] at hm
    calc
      stabilizer Rg a = C.map i ⊔ A₁ := hm.symm
      _ ≤ _ := sup_le_sup_right hC _
  · intro hfix
    apply hmove
    intro x hx
    have hzH : i (g * v * g⁻¹) ∈ HC := by
      have hh := mem_map_of_mem (MulAut.conj (i g)).toMonoidHom z.property
      change (i g * (z : FreeAmalgam Rg) * (i g)⁻¹) ∈ HC at hh
      simpa only [←hvz,map_mul,map_inv] using hh
    apply hi
    simpa only [map_mul] using hfix hzH (i x) hx

include h e hz hk in
/-- At a large critical image a subgroup of the full moving cover still
escapes the starting two-core and controls every subgroup of that core
lying in the endpoint stabilizer. The preserved commutator proves escape;
the cubic kernel is not replaced by the two-core. -/
theorem large_critical_restricted_actor
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg a)) :
    ∃ A : Subgroup (FreeAmalgam Rg), A ≤ U Rg a' ∧
      (¬ A ≤ Q Rg a) ∧
      ∀ Y : Subgroup (FreeAmalgam Rg), Y ≤ Q Rg a →
        Y ≤ stabilizer Rg a' → ⁅Y,A⁆ ≤ Z Rg a := by
  let q : CriticalPath Rg (sourceGeometry h) a' a := CriticalPath.ofPair p.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by
        rw [(sourceGeometry h).distance_constant a p.start_color]
        exact sourceDistance_pos h) a' p.end_color p.critical)
  have hAe : Z Rg a' ≤ stabilizer Rg a :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
      p.critical
  have hR : ⁅U Rg a',Z Rg a⁆ ≤ Z Rg a := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (DistanceEight.U_le_Z Rg a')).trans
      (le_normalizer_iff_commutator_le_left.mp (hAe.trans (Z_normalized Rg a)))
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  have hAq : ⁅U Rg a',Z Rg a⁆ ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    hR.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  obtain ⟨i,hi,hir,hiQ,_,hiU,_⟩ := graph_cover h e hz hk a' p.end_color
  have hAr : Z Rg a ≤ i.range := by
    rw [hir]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  obtain ⟨A,hA,_,hpres,hcontrol⟩ := embedded_cover_restriction_preserving h e hz hk i hi
    (Z Rg a) hAr (hiQ.symm ▸ hlarge) (hiU.symm ▸ hAq)
  have hAU : A ≤ U Rg a' := hiU ▸ hA
  refine ⟨A,hAU,?_,?_⟩
  · intro hn
    have hzA : ⁅A,Z Rg a⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (hn.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a p.start_color))))
    have hp : ⁅A,Z Rg a⁆ = ⁅U Rg a',Z Rg a⁆ := hiU ▸ hpres
    exact critical_moving_commutator_not_central h e hz hk q
      ((hp.symm.trans hzA).le.trans bot_le)
  · intro Y hYQ hYe
    have hYc : Y ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      hYQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a p.start_color)))
    have hh := hcontrol Y (hYe.trans_eq hir.symm)
      (hiU.symm ▸ hR.trans (le_centralizer_iff.mp hYc))
    rw [hiU,commutator_comm] at hh
    exact hh.trans hR

namespace SmallSliceShift
variable {h} {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

include e hz hk in
/-- Both shifted critical images have order two, for either entire cover.
If a shifted image were large, choose the shift using its controlled
restricted actor. Its centralizer orbit would then be a normal radius
subgroup modulo the seed and lie in the forbidden Baumann slice. -/
theorem shifted_indices
    (hb : 4 < sourceDistance h)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) = 2 ∧
      (Q Rg (p.walk.getVert 2)).relIndex (Z Rg s.endpoint) = 2 := by
  have hb2 : 2 < sourceDistance h := by omega
  apply small_critical_indices h e hz hk s.path
  by_contra hn
  have hlarge : 4 ≤ (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) := by omega
  obtain ⟨A,hAU,hAn,hcontrol⟩ := large_critical_restricted_actor h e hz hk s.path hlarge
  let c := p.walk.getVert 2
  let v := s.path.walk.getVert (s.path.walk.length-2)
  let t := p.walk.getVert 1
  have hc : color Rg c = false := s.path.start_color
  have hAZ : A ≤ Z Rg s.endpoint := hAU.trans (DistanceEight.U_le_Z Rg s.endpoint)
  have hEC : Z Rg s.endpoint ≤ stabilizer Rg c :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) c hc
      (by rw [(sourceGeometry h).distance_constant c hc]; exact sourceDistance_pos h)
      s.path.critical
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) s.endpoint s.path.end_color
  have htwo : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 (Z Rg s.endpoint)).to_le hAZ
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
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
  have hline := small_forward_slice_central_line h e hz hk hb2 p hsmall hslice heligible
  obtain ⟨g,hg,hgen,hmove⟩ := exists_cover_line_generator_of_actor h e hz hk hc A
    (hAZ.trans hEC) htwo hAn (forwardSliceLine h (alpha Rg) c) hHU
    hline.1 hline.2.2.2
  let r : SmallSliceShift h p :=
    ⟨s.endpoint,s.path,s.overlap,g,hg,
      le_antisymm (sup_le inf_le_left hEC) (hgen.symm.le.trans (sup_le_sup_left hAZ _)),
      fun hh => hmove (hh.trans (centralizer_le hAZ))⟩
  have hrgen : r.lineCentralizer ⊔ A = stabilizer Rg c := hgen
  have hpre : v = a' := by
    dsimp only [v]
    have hq : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    rw [show s.path.walk.length-2 = p.walk.length-2 by omega,
      s.overlap _ (Nat.le_refl _),show p.walk.length-2+2=p.walk.length by omega,
      p.walk.getVert_length]
  have hDpre : r.seedOrbit ≤ Q Rg v := by
    rw [hpre]
    exact (r.centralizer_orbits_le_old_endpoint_core e hz hk hb hsmall hslice heligible).1
  have hDe : r.seedOrbit ≤ stabilizer Rg s.endpoint := by
    let t' := s.path.walk.getVert (s.path.walk.length-1)
    have hq : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    have het : Adjacent Rg s.endpoint t' := by
      have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-1) (by omega)
      rw [show s.path.walk.length-1+1=s.path.walk.length by omega,
        s.path.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have hvt : Adjacent Rg v t' := by
      have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-2) (by omega)
      rw [show s.path.walk.length-2+1=s.path.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have ht' : color Rg t' = true := by
      have hh := adjacent_color_ne Rg het
      rw [s.path.end_color] at hh
      cases he : color Rg t' <;> simp_all
    exact (hDpre.trans (Q_le_adjacent_h Rg ht' hvt)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg het))
  have hDV : r.seedOrbit ≤ V Rg c := (r.seedOrbit_radius_and_escape e hz hb2).1
  have hDA : ⁅r.seedOrbit,A⁆ ≤ Z Rg c :=
    hcontrol r.seedOrbit (hDV.trans ((sourceGeometry h).V_le_Q hb2 c hc)) hDe
  let D := r.seedOrbit ⊔ Z Rg c
  have hVG : V Rg c ≤ stabilizer Rg c := (sourceGeometry h).V_local c hc (by
    rw [(sourceGeometry h).distance_constant c hc]; exact hb2)
  have hDVA : D ≤ V Rg c := sup_le hDV (Z_le_VBall Rg c 2)
  have hZA : ⁅Z Rg c,A⁆ ≤ Z Rg c :=
    le_normalizer_iff_commutator_le_left.mp ((hAZ.trans hEC).trans (Z_normalized Rg c))
  have hcomm : ⁅D,A⁆ ≤ Z Rg c :=
    commutator_sup_le_of_relative_normal (stabilizer Rg c) r.seedOrbit (Z Rg c)
      A (Z Rg c) (Z_normalized Rg c) (hDV.trans hVG)
      (Z_le_stabilizer Rg c) hDA hZA
  have hDN : stabilizer Rg c ≤ normalizer (D : Set (FreeAmalgam Rg)) := by
    rw [←hrgen]
    apply sup_le
    · exact (le_inf r.centralizer_orbits_normalized.1
        (inf_le_left.trans (Z_normalized Rg c))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr (hcomm.trans le_sup_right)
  have hDB := normalized_radius_le_slice_of_controlled_actor h e hz hb2 hc D A
    hDVA hDN (hAZ.trans hEC) htwo hAn hcomm
  exact (r.seedOrbit_radius_and_escape e hz hb2).2 (le_sup_left.trans hDB)

end SmallSliceShift
namespace SmallSliceShift
variable {h} {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

include e hz hk in
/-- R₃ is the commutator of the entire reverse critical kernel with the
old endpoint's two-core, independently of its realization by the seed
orbit. It has order two and centralizes the full old endpoint radius. -/
theorem orbitDisplacement_full_core
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    s.orbitDisplacement = ⁅s.orbitKernel,Q Rg a'⁆ ∧
      Nat.card s.orbitDisplacement = 2 ∧
      s.orbitDisplacement ≤ Z Rg s.endpoint ⊓
        centralizer (V Rg a' : Set (FreeAmalgam Rg)) := by
  have hb2 : 2 < sourceDistance h := by omega
  have hs : (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) < 4 := by
    rw [(s.shifted_indices e hz hk hb hsmall hslice heligible).1]
    decide
  have hcard := s.orbitDisplacement_card_two e hz hk hb u hR hsmall hslice heligible hs
  have hp : s.path.walk.getVert (s.path.walk.length-2) = a' := by
    have hl : p.walk.length = sourceDistance h := p.length_eq_b
    have hq : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    rw [show s.path.walk.length-2 = p.walk.length-2 by omega,
      s.overlap _ (Nat.le_refl _),show p.walk.length-2+2=p.walk.length by omega,
      p.walk.getVert_length]
  have hbound := small_critical_kernel_predecessor_card h e hz hk hb2 u hR s.path hs
  rw [hp] at hbound
  have hQG : Q Rg a' ≤ stabilizer Rg s.endpoint := by
    conv_lhs => rw [←hp]
    let t := s.path.walk.getVert (s.path.walk.length-1)
    have hl : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    have het : Adjacent Rg s.endpoint t := by
      have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-1) (by omega)
      rw [show s.path.walk.length-1+1=s.path.walk.length by omega,
        s.path.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have hpt : Adjacent Rg (s.path.walk.getVert (s.path.walk.length-2)) t := by
      have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-2) (by omega)
      rw [show s.path.walk.length-2+1=s.path.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have ht : color Rg t = true := by
      have hh := adjacent_color_ne Rg het
      rw [s.path.end_color] at hh
      cases he : color Rg t <;> simp_all
    exact (Q_le_adjacent_h Rg ht hpt).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg het))
  have hNZ : ⁅s.orbitKernel,Q Rg a'⁆ ≤ Z Rg s.endpoint :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hQG.trans (Z_normalized Rg s.endpoint)))
  let := finite_Z Rg s.endpoint
  let : Finite (⁅s.orbitKernel,Q Rg a'⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hNZ) (inclusion_injective _)
  have hle : s.orbitDisplacement ≤ ⁅s.orbitKernel,Q Rg a'⁆ := by
    rw [orbitDisplacement,commutator_comm]
    exact commutator_mono le_rfl
      (s.centralizer_orbits_le_old_endpoint_core e hz hk hb hsmall hslice heligible).1
  have heq := eq_of_le_of_card_ge hle (hcard.symm ▸ hbound)
  refine ⟨heq,hcard,le_inf (hle.trans hNZ) ?_⟩
  have hdist : (cosetGraph Rg).dist a' s.endpoint = 2 := by
    have hh := s.path.dist_end (s.path.walk.length-2)
    rw [hp] at hh
    have hl : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    exact hh.trans (by omega)
  have hZV : Z Rg s.endpoint ≤ V Rg a' :=
    le_iSup_of_le s.endpoint (le_iSup_of_le (by rw [SimpleGraph.dist_comm]; exact hdist.le) le_rfl)
  exact (hle.trans (commutator_mono (inf_le_left.trans hZV) le_rfl)).trans
    (radius_bounds_at h e hz hk a' p.end_color a' a').1

end SmallSliceShift

namespace SmallSliceShift
variable {h} {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

include e hz hk in
/-- For a fixed shifted endpoint R₃ is independent of the residual
conjugator, the chosen seed witness and the overlapping critical walk. -/
theorem orbitDisplacement_eq_of_endpoint
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (r : SmallSliceShift h p) (he : r.endpoint = s.endpoint) :
    r.orbitDisplacement = s.orbitDisplacement := by
  rw [(r.orbitDisplacement_full_core e hz hk hb u hR hsmall hslice heligible).1,
    (s.orbitDisplacement_full_core e hz hk hb u hR hsmall hslice heligible).1]
  simp only [orbitKernel,he]

end SmallSliceShift

omit hk in
include h e hz in
/-- Whole-core application: the restricted-actor shift excludes the large
shifted image for both covers. The resulting order-two orbit commutator
is the full old-endpoint core commutator and has a conjugated-seed witness. -/
theorem coreExhaustion_or_cubic_restricted_orbits :
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
            s.seedOrbit ⊔ s.spanOrbit ≤ Q Rg a' ∧
            (¬ ⁅s.seedOrbit,Z Rg s.endpoint⁆ ≤ Z Rg (p.walk.getVert 2)) ∧
            (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) = 2 ∧
            (Q Rg (p.walk.getVert 2)).relIndex (Z Rg s.endpoint) = 2 ∧
            Nat.card s.orbitDisplacement = 2 ∧
            s.orbitDisplacement = ⁅s.orbitKernel,Q Rg a'⁆ ∧
            s.orbitDisplacement ≤ Z Rg s.endpoint ⊓
              centralizer (V Rg a' : Set (FreeAmalgam Rg)) ∧
            (∀ r : SmallSliceShift h p, r.endpoint = s.endpoint →
              r.orbitDisplacement = s.orbitDisplacement) ∧
            ∃ t ∈ s.lineCentralizer,
              ⁅(Z Rg s.centerVertex).map (MulAut.conj t).toMonoidHom,s.orbitKernel⁆ =
                s.orbitDisplacement := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,?_⟩
    intro u hfull a' p hb4 hsmall hslice hel
    obtain ⟨s⟩ := exists_small_slice_shift h e hz hk hb u hfull p hsmall hslice hel
    have ho := s.centralizer_orbits_le_old_endpoint_core e hz hk hb4 hsmall hslice hel
    have hi := s.shifted_indices e hz hk hb4 hsmall hslice hel
    have hc := s.orbitDisplacement_full_core e hz hk hb4 u hfull.le hsmall hslice hel
    exact ⟨s,sup_le ho.1 ho.2,s.seedOrbit_endpoint_commutator_not_le e hz hb,
      hi.1,hi.2,hc.2.1,hc.1,hc.2.2,
      fun r he => s.orbitDisplacement_eq_of_endpoint e hz hk hb4 u hfull.le hsmall hslice hel r he,
      s.exists_seed_conjugate_orbitDisplacement hc.2.1⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application without a small shifted-image premise.
Centrality in the second local group, strict slices and the terminal source
exclusions remain necessary for unconditional reconstruction. -/
theorem rankTwo_or_cubic_restricted_orbits :
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
            s.seedOrbit ⊔ s.spanOrbit ≤ Q Rg a' ∧
            (¬ ⁅s.seedOrbit,Z Rg s.endpoint⁆ ≤ Z Rg (p.walk.getVert 2)) ∧
            (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) = 2 ∧
            (Q Rg (p.walk.getVert 2)).relIndex (Z Rg s.endpoint) = 2 ∧
            Nat.card s.orbitDisplacement = 2 ∧
            s.orbitDisplacement = ⁅s.orbitKernel,Q Rg a'⁆ ∧
            s.orbitDisplacement ≤ Z Rg s.endpoint ⊓
              centralizer (V Rg a' : Set (FreeAmalgam Rg)) ∧
            (∀ r : SmallSliceShift h p, r.endpoint = s.endpoint →
              r.orbitDisplacement = s.orbitDisplacement) ∧
            ∃ t ∈ s.lineCentralizer,
              ⁅(Z Rg s.centerVertex).map (MulAut.conj t).toMonoidHom,s.orbitKernel⁆ =
                s.orbitDisplacement :=
  (coreExhaustion_or_cubic_restricted_orbits h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
