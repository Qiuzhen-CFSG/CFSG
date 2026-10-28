module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicCentralizerOrbit

/-!
# Displacement of the centralizer orbit in the cubic branch

The seed orbit constructed in CubicCentralizerOrbit escapes the second
Baumann slice. Its displacement under the new endpoint seed therefore
cannot lie in the second seed: adjoining that seed would give a normal
radius subgroup, and the escaping endpoint actor would force it into the
slice. This argument uses the full endpoint seed and the original cubic
kernel.

In the small shifted-image branch, the whole reverse critical kernel has
commutator of order at most two with the predecessor core. The orbit's
commutator with that kernel is nonzero by the preceding displacement
obstruction. It consequently has order two, and one actual conjugated
seed realizes the entire commutator R₃. For the order-sixteen cover,
the natural-cover estimate also excludes a large shifted critical image.
The last edge seed centralizes the predecessor core, so that estimate
extends from the moving cover to the entire endpoint seed.

The whole-core and literal C.1.32 applications retain both covers and
the full kernel. The order-thirty-two large-image case, centrality of R₃,
orbit stabilization and strict slices, the other radical and distance
branches, R4/R6, MS93 (5.11)--(5.12), independent natural exhaustion and
both final reconstruction outcomes remain necessary.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), pp.866--867,
and (5.9), p.921, the orbit commutator R₃ and its conjugate-seed witness.
In the small-image case used here, the restricted source seed is the
entire endpoint seed; its central attachment is retained.
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

include e hz in
/-- The full seed orbit has nontrivial endpoint displacement modulo the
second seed. Otherwise adjoining that seed makes it locally normal and
an escaping endpoint actor forces it into its forbidden Baumann slice. -/
theorem seedOrbit_endpoint_commutator_not_le (hb : 2 < sourceDistance h) :
    ¬ ⁅s.seedOrbit,Z Rg s.endpoint⁆ ≤ Z Rg (p.walk.getVert 2) := by
  let c := p.walk.getVert 2
  let D := s.seedOrbit ⊔ Z Rg c
  have hc : color Rg c = false := s.path.start_color
  have hDV : D ≤ V Rg c := sup_le (s.seedOrbit_radius_and_escape e hz hb).1
    (Z_le_VBall Rg c 2)
  have hVG := (sourceGeometry h).V_local c hc (by
    rw [(sourceGeometry h).distance_constant c hc]; exact hb)
  have hEC : Z Rg s.endpoint ≤ stabilizer Rg c :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) c hc
      (by rw [(sourceGeometry h).distance_constant c hc]; exact sourceDistance_pos h)
      s.path.critical
  have hZcomm : ⁅Z Rg c,Z Rg s.endpoint⁆ ≤ Z Rg c :=
    le_normalizer_iff_commutator_le_left.mp (hEC.trans (Z_normalized Rg c))
  intro hbad
  have hDC : ⁅D,Z Rg s.endpoint⁆ ≤ Z Rg c :=
    commutator_sup_le_of_relative_normal (stabilizer Rg c) s.seedOrbit (Z Rg c)
      (Z Rg s.endpoint) (Z Rg c) (Z_normalized Rg c)
      ((s.seedOrbit_radius_and_escape e hz hb).1.trans hVG)
      (Z_le_stabilizer Rg c) hbad hZcomm
  have hDN : stabilizer Rg c ≤ normalizer (D : Set (FreeAmalgam Rg)) := by
    rw [←s.centralizer_orbits_normalized.2.2]
    apply sup_le
    · exact (le_inf s.centralizer_orbits_normalized.1
        (inf_le_left.trans (Z_normalized Rg c))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr (hDC.trans le_sup_right)
  have hreverse := critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
    c hc (by rw [(sourceGeometry h).distance_constant c hc]; exact sourceDistance_pos h)
    s.endpoint s.path.end_color s.path.critical
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) s.endpoint s.path.end_color
  have hDB := normalized_radius_le_slice_of_controlled_actor h e hz hb hc D
    (Z Rg s.endpoint) hDV hDN hEC (IsElementaryAbelian.isPGroup 2 _)
      hreverse.2 hDC
  exact (s.seedOrbit_radius_and_escape e hz hb).2 (le_sup_left.trans hDB)

private theorem shifted_predecessor (hb : 2 < sourceDistance h) :
    s.path.walk.getVert (s.path.walk.length-2) = a' := by
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hq : s.path.walk.length = sourceDistance h := s.path.length_eq_b
  rw [show s.path.walk.length-2 = p.walk.length-2 by omega,
    s.overlap _ (Nat.le_refl _),show p.walk.length-2+2=p.walk.length by omega,
    p.walk.getVert_length]

/-- The literal reverse critical kernel A₀ in the source (5.9) orbit argument. -/
@[expose] def orbitKernel : Subgroup (FreeAmalgam Rg) :=
  Z Rg s.endpoint ⊓ Q Rg (p.walk.getVert 2)

/-- The source subgroup R₃, with the whole reverse kernel retained. -/
@[expose] def orbitDisplacement : Subgroup (FreeAmalgam Rg) :=
  ⁅s.seedOrbit,s.orbitKernel⁆

include e hz hk in
/-- In the small shifted-image branch the entire orbit has exactly an
order-two commutator with A₀. Its vanishing would control the full endpoint
action and contradict the orbit's Baumann-slice escape. -/
theorem orbitDisplacement_card_two
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) ≤
      pointCore.map (MulAut.conj u).toMonoidHom)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (hshift : (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) < 4) :
    Nat.card s.orbitDisplacement = 2 := by
  have hb2 : 2 < sourceDistance h := by omega
  have hDpre : s.seedOrbit ≤ Q Rg (s.path.walk.getVert (s.path.walk.length-2)) := by
    rw [s.shifted_predecessor hb2]
    exact (s.centralizer_orbits_le_old_endpoint_core e hz hk hb hsmall hslice heligible).1
  have hcard := small_critical_kernel_predecessor_card h e hz hk hb2 u hR s.path hshift
  let K := Z Rg s.endpoint ⊓ Q Rg (p.walk.getVert 2)
  have hN : ⁅K,Q Rg (s.path.walk.getVert (s.path.walk.length-2))⁆ ≤ Z Rg s.endpoint := by
    have hZ := Z_normalized Rg s.endpoint
    have hl : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    let t := s.path.walk.getVert (s.path.walk.length-1)
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
    have hQG : Q Rg (s.path.walk.getVert (s.path.walk.length-2)) ≤
        stabilizer Rg s.endpoint :=
      (Q_le_adjacent_h Rg ht hpt).trans (fun _ hx => hx.2 _ (adjacent_symm Rg het))
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hQG.trans hZ))
  let := finite_Z Rg s.endpoint
  let : Finite (⁅K,Q Rg (s.path.walk.getVert (s.path.walk.length-2))⁆ :
      Subgroup (FreeAmalgam Rg)) := Finite.of_injective (inclusion hN) (inclusion_injective _)
  have hle : s.orbitDisplacement ≤ ⁅K,Q Rg (s.path.walk.getVert (s.path.walk.length-2))⁆ := by
    rw [orbitDisplacement,commutator_comm]
    exact commutator_mono le_rfl hDpre
  let : Finite s.orbitDisplacement := Finite.of_injective (inclusion hle) (inclusion_injective _)
  have hlecard : Nat.card s.orbitDisplacement ≤ 2 := (card_le_of_le hle).trans hcard
  have hne : s.orbitDisplacement ≠ ⊥ := by
    intro he
    have hfix : s.seedOrbit ≤ centralizer (Z Rg s.endpoint ⊓ Q Rg (p.walk.getVert 2) :
        Set (FreeAmalgam Rg)) := commutator_eq_bot_iff_le_centralizer.mp he
    exact s.seedOrbit_endpoint_commutator_not_le e hz hb2
      (small_critical_predecessor_commutator h e hz hk hb2 s.path hshift s.seedOrbit hDpre hfix)
  have hh := (one_lt_card_iff_ne_bot s.orbitDisplacement).mpr hne
  omega

include e hz hk in
/-- For the order-sixteen cover the large shifted-image alternative is
impossible. The full endpoint seed is the moving cover joined to the last
edge seed, which centralizes the predecessor core. Thus the natural-cover
estimate controls its entire action, contradicting orbit escape. -/
theorem natural_shifted_indices
    (hnat : Nat.card (initialMoved L R) = 16)
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
  let c := p.walk.getVert 2
  let v := s.path.walk.getVert (s.path.walk.length-2)
  let t := s.path.walk.getVert (s.path.walk.length-1)
  have hl : s.path.walk.length = sourceDistance h := s.path.length_eq_b
  have het : Adjacent Rg s.endpoint t := by
    have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-1) (by omega)
    rw [show s.path.walk.length-1+1=s.path.walk.length by omega,
      s.path.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hvt : Adjacent Rg v t := by
    have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-2) (by omega)
    rw [show s.path.walk.length-2+1=s.path.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg het
    rw [s.path.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hDpre : s.seedOrbit ≤ Q Rg v := by
    dsimp only [v]
    rw [s.shifted_predecessor hb2]
    exact (s.centralizer_orbits_le_old_endpoint_core e hz hk hb hsmall hslice heligible).1
  have hDZ : ⁅s.seedOrbit,Z Rg t⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply (hDpre.trans (Q_le_adjacent_h Rg ht hvt)).trans
    apply le_centralizer_iff.mpr
    intro z hz
    rw [Z,if_neg (by rw [ht]; decide)] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2
  have hDU : ⁅s.seedOrbit,U Rg s.endpoint⁆ ≤ Z Rg c :=
    (commutator_mono (le_inf (s.seedOrbit_radius_and_escape e hz hb2).1 hDpre) le_rfl).trans
      (critical_radius_moving_commutator_le_Z_of_natural h e hz hk hnat hb2 s.path hlarge)
  have hseed : Z Rg s.endpoint = U Rg s.endpoint ⊔ Z Rg t := by
    obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common Rg s.endpoint t).mp het
    · rcases hg with ⟨he,ht⟩
      have heq := CubicAction.graph_Z_eq_moved_sup_edge h e hz (base_adjacent Rg)
      rw [graph_U_map h e hz] at heq
      have hm := congrArg (fun A : Subgroup (FreeAmalgam Rg) =>
        A.map (MulAut.conj g⁻¹).toMonoidHom) heq
      rw [Subgroup.map_sup,←Z_act,←U_act,←Z_act] at hm
      simpa only [he,ht,alpha,beta,act_mVertex,act_hVertex,one_mul] using hm
    · have hh := s.path.end_color
      rw [hg.1] at hh
      cases hh
  have hEC : Z Rg s.endpoint ≤ stabilizer Rg c :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) c s.path.start_color
      (by rw [(sourceGeometry h).distance_constant c s.path.start_color]; exact sourceDistance_pos h)
      s.path.critical
  apply s.seedOrbit_endpoint_commutator_not_le e hz hb2
  rw [commutator_comm,hseed]
  apply commutator_sup_le_of_relative_normal (Z Rg s.endpoint) _ _ s.seedOrbit
    (Z Rg c) (hEC.trans (Z_normalized Rg c))
    (DistanceEight.U_le_Z Rg _) (adjacent_Z_le Rg s.path.end_color het)
  · rwa [commutator_comm]
  · rw [commutator_comm,hDZ]
    exact bot_le

/-- Every commutator of the orbit is generated on one of its literal seed
conjugates. If R₃ has order two, one such conjugate realizes all of R₃. -/
theorem exists_seed_conjugate_orbitDisplacement
    (hcard : Nat.card s.orbitDisplacement = 2) :
    ∃ t ∈ s.lineCentralizer,
      ⁅(Z Rg s.centerVertex).map (MulAut.conj t).toMonoidHom,s.orbitKernel⁆ =
        s.orbitDisplacement := by
  let : Finite s.orbitDisplacement := Nat.finite_of_card_ne_zero (by omega)
  have hne : s.orbitDisplacement ≠ ⊥ := (one_lt_card_iff_ne_bot _).mp (by omega)
  have hex : ∃ t : s.lineCentralizer,
      ⁅(Z Rg s.centerVertex).map (MulAut.conj (t : FreeAmalgam Rg)).toMonoidHom,
        s.orbitKernel⁆ ≠ ⊥ := by
    by_contra hn
    push Not at hn
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [seedOrbit,conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun t => commutator_eq_bot_iff_le_centralizer.mp (hn t))
  obtain ⟨t,ht⟩ := hex
  have hle : ⁅(Z Rg s.centerVertex).map (MulAut.conj (t : FreeAmalgam Rg)).toMonoidHom,
        s.orbitKernel⁆ ≤ s.orbitDisplacement := by
    apply commutator_mono _ le_rfl
    rw [seedOrbit,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun x : s.lineCentralizer =>
      (Z Rg s.centerVertex).map (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom) t
  let : Finite (⁅(Z Rg s.centerVertex).map (MulAut.conj (t : FreeAmalgam Rg)).toMonoidHom,
      s.orbitKernel⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hle) (inclusion_injective _)
  have hc := (one_lt_card_iff_ne_bot _).mpr ht
  exact ⟨t,t.property,eq_of_le_of_card_ge hle (by omega)⟩

end SmallSliceShift

omit hk in
include e hz in
/-- Whole-core application of the source orbit-displacement calculation.
The natural cover discharges smallness of the shifted critical image;
both covers retain the literal full-kernel calculation in that branch. -/
theorem coreExhaustion_or_cubic_orbit_displacement :
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
            (Nat.card (initialMoved L R) = 16 →
              (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) = 2 ∧
              (Q Rg (p.walk.getVert 2)).relIndex (Z Rg s.endpoint) = 2) ∧
            ((Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) < 4 →
              Nat.card s.orbitDisplacement = 2 ∧
              ∃ t ∈ s.lineCentralizer,
                ⁅(Z Rg s.centerVertex).map (MulAut.conj t).toMonoidHom,s.orbitKernel⁆ =
                  s.orbitDisplacement) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,?_⟩
    intro u hfull a' p hb4 hsmall hslice hel
    obtain ⟨s⟩ := exists_small_slice_shift h e hz hk hb u hfull p hsmall hslice hel
    have ho := s.centralizer_orbits_le_old_endpoint_core e hz hk hb4 hsmall hslice hel
    refine ⟨s,sup_le ho.1 ho.2,s.seedOrbit_endpoint_commutator_not_le e hz hb,
      fun hn => s.natural_shifted_indices e hz hk hn hb4 hsmall hslice hel,?_⟩
    intro hshift
    have hc := s.orbitDisplacement_card_two e hz hk hb4 u hfull.le hsmall hslice hel hshift
    exact ⟨hc,s.exists_seed_conjugate_orbitDisplacement hc⟩

omit hk in
include e hz in
/-- Literal C.1.32 application of the complete orbit-displacement family.
Centrality of R₃, the augmentation large-image branch and the terminal
source exclusions remain necessary for unconditional reconstruction. -/
theorem rankTwo_or_cubic_orbit_displacement :
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
            (Nat.card (initialMoved L R) = 16 →
              (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) = 2 ∧
              (Q Rg (p.walk.getVert 2)).relIndex (Z Rg s.endpoint) = 2) ∧
            ((Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) < 4 →
              Nat.card s.orbitDisplacement = 2 ∧
              ∃ t ∈ s.lineCentralizer,
                ⁅(Z Rg s.centerVertex).map (MulAut.conj t).toMonoidHom,s.orbitKernel⁆ =
                  s.orbitDisplacement) :=
  (coreExhaustion_or_cubic_orbit_displacement e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
