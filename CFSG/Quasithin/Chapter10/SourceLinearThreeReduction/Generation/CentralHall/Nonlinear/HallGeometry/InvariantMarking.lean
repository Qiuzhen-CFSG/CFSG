module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.TorusCoordinates
public import Theory.SpecificGroups.SL2.HallMarking
public import Theory.GroupTheory.Hall.TwoResidual

/-!
# A common matrix marking of the original invariant Hall subgroup

Choose the odd Hall subgroup C of the literal source Borel that is preserved
by the original Hall actor. In the original two-core quotient of L₀, its
image lies in the Sylow normalizer. The Hall condition makes its two unit
coordinates jointly surjective. Simultaneously mark that Sylow by the
two upper root groups and C by diagonal matrices. The two conjugators are
chosen once for all of C; the first also changes the marking of L, preserving
its literal inclusion into the first factor. Thus C is isomorphic to the
full product of the two unit groups. The original Hall actor still
normalizes C, and the original orbit intersection is still contained in C.
The final theorem transports this normalization to the literal quotient action
on the full pair of split tori.

Source: Aschbacher--Smith, 10.2.3, printed p.745. This constructs the common
Cartan marking preceding the field-factor and module fixed-vector arguments;
it does not assert that the whole original Hall actor lies in C.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Matrix.SpecialLinearGroup
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
include D

/-- Simultaneous coordinates on the actual invariant Hall subgroup, retaining
both the component inclusion and the original orbit Sylow. -/
theorem exists_hall_invariant_source_borel_marking {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    ∃ (C : Subgroup G) (hC : C ≤ sourceOrbitBorel T L),
      IsHallSubgroup Subgroup.OddHall.oddPrimes (C.subgroupOf (sourceOrbitBorel T L)) ∧
      B.map H.subtype ≤ normalizer (C : Set G) ∧
      B.map H.subtype ⊓ localOrbit T L ≤ C ∧
      ∃ (e' : (L ⧸ pCore 2 L) ≃* SL(2,F))
        (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)))
        (d : C →* Fˣ × Fˣ), Function.Bijective d ∧
        (∀ l : L, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
          ⟨l,le_componentOrbit L T l.property⟩) =
            (e' (QuotientGroup.mk' (pCore 2 L) l),1)) ∧
        ((T : Subgroup G).subgroupOf (localOrbit T L)).map
          (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))) =
            (upperUnipotent F).prod (upperUnipotent F) ∧
        ∀ x : C, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
          ⟨x,((hC.trans (map_subtype_le (pResidual 2
            (sourceOrbitSylowNormalizer T L)))).trans inf_le_left) x.property⟩) =
          (diag2 ((d x).1 : F) (Units.ne_zero _),
            diag2 ((d x).2 : F) (Units.ne_zero _)) := by
  obtain ⟨C,hC,hHall,hBC,hplus⟩ := exists_hall_invariant_source_borel D c e
  have ho : Odd (Nat.card C) := by
    have h := Subgroup.OddHall.odd_hall_odd hHall
    rwa [Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv] at h
  let R := localOrbit T L
  have hCN : C ≤ sourceOrbitSylowNormalizer T L :=
    hC.trans (map_subtype_le (pResidual 2 (sourceOrbitSylowNormalizer T L)))
  have hCR : C ≤ R := hCN.trans inf_le_left
  let C0 := C.subgroupOf R
  have ho0 : Odd (Nat.card C0) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hCR).toEquiv]
  obtain ⟨S,hS⟩ := source_orbit_sylow_intersection D
  obtain ⟨q0,hq0⟩ := marked_sl2_pair_quotient D e c.nonnormal
  let f := q0.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hf : Function.Surjective f := q0.surjective.comp (QuotientGroup.mk'_surjective _)
  let Sq := S.mapSurjective hf
  let Cq := C0.map f
  have hC0 : C0 ≤ normalizer (S : Set R) := by
    rw [←source_orbit_sylow_normalizer_eq S hS]
    exact fun x hx => hCN hx
  have hHallN : IsHallSubgroup OddHall.oddPrimes
      (C.subgroupOf (sourceOrbitSylowNormalizer T L)) :=
    OddHall.hall_of_twoResidual (sourceOrbitSylowNormalizer T L) C hC hHall
  have hCardN : Nat.card (normalizer (S : Set R)) =
      Nat.card (sourceOrbitSylowNormalizer T L) := by
    rw [←source_orbit_sylow_normalizer_eq S hS]
    exact Nat.card_congr (subgroupOfEquivOfLe
      (show sourceOrbitSylowNormalizer T L ≤ R from inf_le_left)).toEquiv
  have hCardC : Nat.card (C0.subgroupOf (normalizer (S : Set R))) =
      Nat.card (C.subgroupOf (sourceOrbitSylowNormalizer T L)) :=
    (Nat.card_congr (subgroupOfEquivOfLe hC0).toEquiv).trans
      ((Nat.card_congr (subgroupOfEquivOfLe hCR).toEquiv).trans
        (Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv).symm)
  have hIndex : (C0.subgroupOf (normalizer (S : Set R))).index =
      (C.subgroupOf (sourceOrbitSylowNormalizer T L)).index := by
    have hh := (C0.subgroupOf (normalizer (S : Set R))).card_mul_index
    rw [hCardC,hCardN] at hh
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos
      (hh.trans (C.subgroupOf (sourceOrbitSylowNormalizer T L)).card_mul_index.symm)
  have hHall0 : IsHallSubgroup OddHall.oddPrimes
      (C0.subgroupOf (normalizer (S : Set R))) :=
    ⟨fun p hp => hHallN.p_in_pi_of_p_dvd_card p (hCardC ▸ hp),
      fun p hp => hHallN.p_in_pi_of_p_dvd_index p (hIndex ▸ hp)⟩
  have hCq : Cq ≤ normalizer (Sq : Set (SL(2,F) × SL(2,F))) :=
    (map_mono hC0).trans (le_normalizer_map f)
  obtain ⟨a,b,dq,hSq,hdq⟩ := pair_sylow_odd_subgroup_diagonal_coordinates Sq Cq hCq
    (ho0.of_dvd_nat (C0.card_map_dvd f))
  let v := (MulAut.conj a).prodCongr (MulAut.conj b)
  let q := q0.trans v
  let e' := e.trans (MulAut.conj a)
  let i := (subgroupOfEquivOfLe hCR).symm.toMonoidHom
  let k : C →* Cq := (f.subgroupMap C0).comp i
  let d := dq.comp k
  have hdiag (x : C) : q (QuotientGroup.mk' (pCore 2 R) (i x)) =
      (diag2 ((d x).1 : F) (Units.ne_zero _),
        diag2 ((d x).2 : F) (Units.ne_zero _)) := hdq (k x)
  have hsurj : Function.Surjective d := by
    let fq := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
    have hkq : fq.ker ≤ (S : Subgroup R) := by
      intro x hx
      exact pCore_isPGroup.le_sylow_of_normal S
        ((QuotientGroup.eq_one_iff x).mp (q.map_eq_one_iff.mp hx))
    have hSq' : (S : Subgroup R).map fq =
        (upperUnipotent F).prod (upperUnipotent F) := by
      change (S : Subgroup R).map (v.toMonoidHom.comp f) = _
      rw [←Subgroup.map_map]
      exact hSq
    let j := (subgroupOfEquivOfLe hCR).toMonoidHom
    have hdj : ∀ x : C0, fq x =
        (diag2 (((d.comp j) x).1 : F) (Units.ne_zero _),
          diag2 (((d.comp j) x).2 : F) (Units.ne_zero _)) := fun x => hdiag (j x)
    have hs := pair_hall_marking_surjective fq
      (q.surjective.comp (QuotientGroup.mk'_surjective _)) S hkq hSq'
      C0 hHall0 (d.comp j) hdj
    intro z
    obtain ⟨x,hx⟩ := hs z
    exact ⟨j x,hx⟩
  refine ⟨C,hC,hHall,hBC,hplus,e',q,d,⟨?_,hsurj⟩,?_,?_,hdiag⟩
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hz := hdiag x
    have he : q (QuotientGroup.mk' (pCore 2 R) (i x)) = 1 := by
      rw [show d x = 1 from hx] at hz
      convert hz using 1
      apply Prod.ext <;> apply Subtype.ext <;>
        ext j l <;> fin_cases j <;> fin_cases l <;> simp [diag2_coe']
    have hk : (i x : R) ∈ pCore 2 R := (QuotientGroup.eq_one_iff _).mp
      (q.map_eq_one_iff.mp he)
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := R)).exists_card_eq
    have hdis : Disjoint (pCore 2 R) C0 := disjoint_of_coprime_natCard (by
      rw [hn]
      exact (Nat.coprime_two_left.mpr ho0).pow_left n)
    apply Subtype.ext
    exact congrArg (fun z : R => (z : G)) (disjoint_def.mp hdis hk (i x).property)
  · intro l
    change v (q0 _) = _
    rw [hq0]
    exact Prod.ext rfl (map_one (MulAut.conj b))
  · change ((T : Subgroup G).subgroupOf R).map (v.toMonoidHom.comp f) = _
    rw [←Subgroup.map_map,←hS]
    exact hSq

/-- The same quotient marking carries the original Hall action to an action
preserving the full pair of split diagonal tori. The component inclusion and
Sylow marking remain explicit; no field-factor conclusion is assumed. -/
theorem exists_hall_stable_pair_torus {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    ∃ (e' : (L ⧸ pCore 2 L) ≃* SL(2,F))
      (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F))),
      (∀ l : L, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
        ⟨l,le_componentOrbit L T l.property⟩) =
          (e' (QuotientGroup.mk' (pCore 2 L) l),1)) ∧
      ((T : Subgroup G).subgroupOf (localOrbit T L)).map
        (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))) =
          (upperUnipotent F).prod (upperUnipotent F) ∧
      ∀ (b : B) (z : Fˣ × Fˣ), ∃ w : Fˣ × Fˣ,
        q (action D B c.hall_le b (q.symm
          (diag2 (z.1 : F) (Units.ne_zero _),diag2 (z.2 : F) (Units.ne_zero _)))) =
            (diag2 (w.1 : F) (Units.ne_zero _),diag2 (w.2 : F) (Units.ne_zero _)) := by
  obtain ⟨C,hC,_,hBC,_,e',q,d,hd,hcomp,hS,hdiag⟩ :=
    exists_hall_invariant_source_borel_marking D c e
  refine ⟨e',q,hcomp,hS,fun b z => ?_⟩
  obtain ⟨x,hx⟩ := hd.2 z
  let bC : normalizer (C : Set G) := ⟨(b : G),hBC (mem_map_of_mem H.subtype b.property)⟩
  let x' : C := C.normalizerMonoidHom bC x
  refine ⟨d x',?_⟩
  rw [←hx,←hdiag x,q.symm_apply_apply]
  change q (quotientAut (pCore 2 (localOrbit T L)) _ _) = _
  rw [quotientAut_apply_mk]
  exact hdiag x'

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
