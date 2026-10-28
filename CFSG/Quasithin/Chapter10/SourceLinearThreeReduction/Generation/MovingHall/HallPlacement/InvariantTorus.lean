module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.InvariantMarking
public import Theory.SpecificGroups.SL2.SylowTorusKernel

/-!
# The original moving Hall subgroup and its invariant split torus

The literal H-star overlap normalizes the orbit Sylow and its two-residual
Borel. An invariant odd Hall subgroup of that solvable Borel contains the
original Hall's orbit intersection. Its two unit coordinates are jointly
bijective, using the actual quotient of the original component orbit.

This adapts the common Borel geometry to the moving context, without the
centralizing-Z hypothesis of the central-Hall context. The field-factor
consumer below uses this same torus and quotient action. Its reverse
normalization premise remains the geometric obligation of this owner.
Source: Aschbacher–Smith 10.2.3(4), printed pp.745–746.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Chapter3.Section02 Matrix.SpecialLinearGroup
open CentralHall.Nonlinear.HallGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
include D

/-- The original Hall normalizes the literal orbit Sylow. -/
theorem hall_normalizes_orbit_sylow {H : Subgroup G} {B : Subgroup H}
    (c : MovingHall.Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    B.map H.subtype ≤ normalizer ((T : Subgroup G) ⊓ localOrbit T L : Set G) :=
  (le_inf (map_subtype_le B) (map_le_iff_le_comap.mpr c.hall_le)).trans
    (source_sl2_hstar_overlap_normalizes_sylow D e c.nonnormal c.hstar)

/-- Only orbit containment is needed to place the original Hall in B₀. -/
theorem hall_le_borel_of_le_orbit {H : Subgroup G} {B : Subgroup H}
    (c : MovingHall.Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hBR : B.map H.subtype ≤ localOrbit T L) :
    B.map H.subtype ≤ sourceOrbitBorel T L :=
  source_sl2_hstar_odd_subgroup_le_borel_of_le_orbit D e c.nonnormal c.hstar
    _ (map_subtype_le B) hBR (c.odd_card_of_le_hall_image _ le_rfl)

/-- The orbit intersection is placed before removing any field factor. -/
theorem hall_orbit_intersection_le_borel {H : Subgroup G} {B : Subgroup H}
    (c : MovingHall.Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    B.map H.subtype ⊓ localOrbit T L ≤ sourceOrbitBorel T L :=
  source_sl2_hstar_odd_subgroup_le_borel_of_le_orbit D e c.nonnormal c.hstar
    _ (inf_le_left.trans (map_subtype_le B)) inf_le_right
    (c.odd_card_of_le_hall_image _ inf_le_left)

/-- The original Hall normalizes the two-residual, not merely its quotient. -/
theorem hall_normalizes_source_borel {H : Subgroup G} {B : Subgroup H}
    (c : MovingHall.Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    B.map H.subtype ≤ normalizer (sourceOrbitBorel T L : Set G) := by
  have hBN : B.map H.subtype ≤ normalizer (sourceOrbitSylowNormalizer T L : Set G) := by
    exact (le_inf (map_le_iff_le_comap.mpr c.hall_le)
      ((hall_normalizes_orbit_sylow D c e).trans
        (normalizer ((T : Subgroup G) ⊓ localOrbit T L : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact hBN.trans (normalizer_le_normalizer_characteristic_image
    (sourceOrbitSylowNormalizer T L) (pResidual 2 (sourceOrbitSylowNormalizer T L)))

/-- An actual invariant odd Hall subgroup of the original Borel. -/
theorem exists_hall_invariant_source_borel {H : Subgroup G} {B : Subgroup H}
    (c : MovingHall.Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    ∃ C : Subgroup G, C ≤ sourceOrbitBorel T L ∧
      IsHallSubgroup Subgroup.OddHall.oddPrimes (C.subgroupOf (sourceOrbitBorel T L)) ∧
      B.map H.subtype ≤ normalizer (C : Set G) ∧
      B.map H.subtype ⊓ localOrbit T L ≤ C := by
  let A := B.map H.subtype
  let : Group.IsSolvable B := Group.isSolvable_of_comm (isMulCommutative_iff.mp c.abelian)
  let : Group.IsSolvable A := Group.isSolvable_of_surjective
    (H.subtype.subgroupMap_surjective B)
  let : Group.IsSolvable (sourceOrbitBorel T L) := source_sl2_borel_solvable D e c.nonnormal
  obtain ⟨C,hC,hHall,hAC,hcontain⟩ := Subgroup.OddHall.exists_actor_invariant_hall
    (sourceOrbitBorel T L) A (hall_normalizes_source_borel D c e)
      (c.odd_card_of_le_hall_image _ le_rfl)
  exact ⟨C,hC,hHall,hAC,
    (le_inf inf_le_left (hall_orbit_intersection_le_borel D c e)).trans hcontain⟩

/-- Simultaneous coordinates on the actual invariant Hall subgroup, retaining
both the component inclusion and the original orbit Sylow. -/
theorem exists_hall_invariant_source_borel_marking {H : Subgroup G} {B : Subgroup H}
    (c : MovingHall.Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
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


end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement

namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Subgroup Theory.GroupTheory Chapter3.Section02 Matrix.SpecialLinearGroup
open BenderSuzuki.ZD.Linear
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
/-- In the actual quotient marking, reverse normalization kills both field
coordinates. The independent source geometry must still prove that the
selected invariant torus normalizes the original Hall. -/
theorem original_torus_field_factors_eq_one
    {H : Subgroup G} {B : Subgroup H} (c : MovingHall.Context D H B)
    (C : Subgroup G) (hCR : C ≤ localOrbit T L)
    (hBC : B.map H.subtype ≤ normalizer (C : Set G))
    (hCB : C ≤ normalizer (B.map H.subtype : Set G))
    (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)))
    (d : C →* Fˣ × Fˣ) (hd : Function.Surjective d)
    (hdiag : ∀ x : C, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
      ⟨x,hCR x.property⟩) = (splitDiagonalHom (d x).1,splitDiagonalHom (d x).2))
    (b : B) (σ τ : F ≃+* F)
    (hfield : ∀ z : Fˣ × Fˣ,
      q (CentralHall.action D B c.hall_le b
        (q.symm (splitDiagonalHom z.1,splitDiagonalHom z.2))) =
      (splitDiagonalHom (Units.map σ.toMonoidHom z.1),
        splitDiagonalHom (Units.map τ.toMonoidHom z.2))) : σ = 1 ∧ τ = 1 := by
  let := c.abelian
  let A := B.map H.subtype
  let bA : A := ⟨(b : G),mem_map_of_mem H.subtype b.property⟩
  have he (x : C) :
      d (C.normalizerMonoidHom (inclusion hBC bA) x) =
        (Units.map σ.toMonoidHom (d x).1,Units.map τ.toMonoidHom (d x).2) := by
    have hh := hfield (d x)
    rw [←hdiag x,q.symm_apply_apply] at hh
    change q (quotientAut (pCore 2 (localOrbit T L)) _ _) = _ at hh
    rw [quotientAut_apply_mk] at hh
    have hx := hdiag (C.normalizerMonoidHom (inclusion hBC bA) x)
    have hpair := hx.symm.trans hh
    exact Prod.ext (splitDiagonalHom_injective (congrArg Prod.fst hpair))
      (splitDiagonalHom_injective (congrArg Prod.snd hpair))
  have hf : Function.Surjective ((MonoidHom.fst Fˣ Fˣ).comp d) := by
    intro u
    obtain ⟨x,hx⟩ := hd (u,1)
    exact ⟨x,congrArg Prod.fst hx⟩
  have hs : Function.Surjective ((MonoidHom.snd Fˣ Fˣ).comp d) := by
    intro u
    obtain ⟨x,hx⟩ := hd (1,u)
    exact ⟨x,congrArg Prod.snd hx⟩
  exact ⟨field_factor_eq_one C A hBC hCB _ hf bA σ (fun x => congrArg Prod.fst (he x)),
    field_factor_eq_one C A hBC hCB _ hs bA τ (fun x => congrArg Prod.snd (he x))⟩

end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement

namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Subgroup Theory.GroupTheory Chapter3.Section02 Matrix.SpecialLinearGroup
open BenderSuzuki.ZD.Linear
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Construct the actual invariant torus and apply field rigidity in its same
quotient coordinates. Only reverse normalization and the coefficient-action
identity are premises of the final implication; all torus choices, Hall
conditions and surjectivity are supplied by the original context. -/
theorem exists_hall_invariant_rigid_torus
    {H : Subgroup G} {B : Subgroup H} (c : MovingHall.Context D H B)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
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
        (∀ x : C, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
          ⟨x,((hC.trans (map_subtype_le (pResidual 2
            (sourceOrbitSylowNormalizer T L)))).trans inf_le_left) x.property⟩) =
            (splitDiagonalHom (d x).1,splitDiagonalHom (d x).2)) ∧
        (C ≤ normalizer (B.map H.subtype : Set G) →
          ∀ (b : B) (σ τ : F ≃+* F),
          (∀ z : Fˣ × Fˣ, q (CentralHall.action D B c.hall_le b
            (q.symm (splitDiagonalHom z.1,splitDiagonalHom z.2))) =
              (splitDiagonalHom (Units.map σ.toMonoidHom z.1),
                splitDiagonalHom (Units.map τ.toMonoidHom z.2))) → σ = 1 ∧ τ = 1) := by
  obtain ⟨C,hC,hHall,hBC,hplus,e',q,d,hd,hcomp,hS,hdiag⟩ :=
    exists_hall_invariant_source_borel_marking D c e
  refine ⟨C,hC,hHall,hBC,hplus,e',q,d,hd,hcomp,hS,?_,?_⟩
  · simpa only [splitDiagonalHom_apply] using hdiag
  · intro hCB b σ τ hfield
    exact original_torus_field_factors_eq_one D c C
      ((hC.trans (map_subtype_le _)).trans inf_le_left) hBC hCB q d hd.2
      (by simpa only [splitDiagonalHom_apply] using hdiag) b σ τ hfield

end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
