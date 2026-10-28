module

public import Stellmacher.SectionFiveToSeven.Defs
public import Stellmacher.SectionTwo.QuotientAction
public import Stellmacher.OmegaOneCenterMap

/-!
# The canonical barred action in Stellmacher (6.4)

For Hypothesis 2, choose the Sylow 2-subgroup of `P₁` whose ambient image is
`S`.  Its Section 2 subgroup `V₁` is the intrinsic normal closure of the
central involutions, and its centralizer `C₁` is normal.  This module forms the
canonical quotient `barP₁ = P₁/C₁`, its mapped Sylow subgroup `barS`, and the
faithful conjugation action on `V₁`.  The action-defined subgroup
`J(V₁,barS)` and its full ambient preimage are therefore available without an
arbitrary quotient presentation in later theorem statements.

The principal setup theorem identifies the selected Sylow image with `S` and
the intrinsic `V₁` with the Section 6 ambient conjugate closure.  It then uses
the quotient-action computation theorem to identify fixed points of
`J(V₁,barS)` with ambient centralization of its full preimage.  This is the
transport required by the source-corrected statement of (6.4).

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), notation preceding Section 6 and Lemma (6.4), pp. 30--32.  The journal
scan retains the bars on `barP₁`, `barS`, and `J(V,barS)` that were lost in the
repository LaTeX transcription.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

private theorem conjugateClosure_le_container
    {H : Type u} [Group H] (X P : Subgroup H) (hXP : X ≤ P) :
    conjugateClosure X P ≤ P := by
  rw [conjugateClosure]
  apply (Subgroup.closure_le _).2
  rintro _ ⟨p, x, rfl⟩
  exact P.mul_mem (P.mul_mem p.property (hXP x.property)) (P.inv_mem p.property)

private theorem conjugateClosure_normal_subgroupOf
    {H : Type u} [Group H] (X P : Subgroup H) (hXP : X ≤ P) :
    ((conjugateClosure X P).subgroupOf P).Normal := by
  let A := conjugateClosure X P
  have hAP : A ≤ P := conjugateClosure_le_container X P hXP
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).2
  rw [Subgroup.le_normalizer_iff]
  intro p hp a ha
  change p * a * p⁻¹ ∈ conjugateClosure X P
  change a ∈ conjugateClosure X P at ha
  rw [conjugateClosure] at ha ⊢
  refine Subgroup.closure_induction
    (p := fun a _ => p * a * p⁻¹ ∈ Subgroup.closure
      {x : H | ∃ q : P, ∃ y : X, x = (q : H) * (y : H) * (q : H)⁻¹})
    (x := a) ?_ ?_ ?_ ?_ ha
  · rintro a ⟨q, x, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨(⟨p, hp⟩ : P) * q, x, ?_⟩
    change p * ((q : H) * (x : H) * (q : H)⁻¹) * p⁻¹ =
      (p * (q : H)) * (x : H) * (p * (q : H))⁻¹
    group
  · simp
  · intro a b _ _ ha hb
    have hab := Subgroup.mul_mem _ ha hb
    convert hab using 1
    group
  · intro a _ ha
    have hai := Subgroup.inv_mem _ ha
    convert hai using 1
    group

private theorem localNormalClosure_map_eq_conjugateClosure
    {H : Type u} [Group H] (X P : Subgroup H) (hXP : X ≤ P) :
    (Subgroup.normalClosure (X.subgroupOf P : Set P)).map P.subtype =
      conjugateClosure X P := by
  let A := conjugateClosure X P
  have hAP : A ≤ P := conjugateClosure_le_container X P hXP
  have hAnorm : (A.subgroupOf P).Normal :=
    conjugateClosure_normal_subgroupOf X P hXP
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    have hcomap : A.comap P.subtype = A.subgroupOf P := rfl
    rw [hcomap]
    let _ : (A.subgroupOf P).Normal := hAnorm
    apply Subgroup.normalClosure_le_normal
    intro x hx
    change (x : H) ∈ conjugateClosure X P
    rw [conjugateClosure]
    apply Subgroup.subset_closure
    exact ⟨1, ⟨(x : H), hx⟩, by simp⟩
  · rw [conjugateClosure]
    apply (Subgroup.closure_le _).2
    rintro _ ⟨p, x, rfl⟩
    let xP : P := ⟨(x : H), hXP x.property⟩
    have hxN : xP ∈ Subgroup.normalClosure (X.subgroupOf P : Set P) :=
      Subgroup.subset_normalClosure x.property
    have hc := Subgroup.normalClosure_normal.conj_mem xP hxN p
    exact Subgroup.mem_map_of_mem P.subtype hc

/-- A canonical intrinsic Sylow 2-subgroup of `P₁` mapping to `S`. -/
@[expose] public noncomputable def sectionSixSylow
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) : Sylow 2 P1 :=
  Classical.choose h.fiveOne.P1_mem.1.2.1.2

private theorem sectionSixSylow_image
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) :
    (sectionSixSylow h : Subgroup P1).map P1.subtype = S :=
  Classical.choose_spec h.fiveOne.P1_mem.1.2.1.2

/-- The intrinsic Section 2 normal closure inside `P₁`. -/
public noncomputable abbrev sectionSixLocalV
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) : Subgroup P1 :=
  Stellmacher.SectionTwo.vSubgroup (sectionSixSylow h)

/-- The intrinsic centralizer `C_{P₁}(V₁)`. -/
public noncomputable abbrev sectionSixLocalC
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) : Subgroup P1 :=
  Stellmacher.SectionTwo.cSubgroup (sectionSixSylow h)

public instance sectionSixLocalC_normal
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) :
    (sectionSixLocalC h).Normal := by
  let _ : (Stellmacher.SectionTwo.vSubgroup (sectionSixSylow h)).Normal := by
    rw [Stellmacher.SectionTwo.vSubgroup]
    exact Subgroup.normalClosure_normal
  dsimp [sectionSixLocalC, Stellmacher.SectionTwo.cSubgroup]
  exact Subgroup.normal_centralizer

/-- The canonical faithful quotient `barP₁ = P₁/C_{P₁}(V₁)`. -/
public noncomputable abbrev SectionSixBarP1
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) :=
  P1 ⧸ sectionSixLocalC h

/-- The canonical quotient map from `P₁` to `barP₁`. -/
public noncomputable abbrev sectionSixQuotientMap
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) :
    P1 →* SectionSixBarP1 h :=
  QuotientGroup.mk' (sectionSixLocalC h)

/-- The mapped Sylow subgroup `barS` of the canonical quotient. -/
public noncomputable abbrev sectionSixBarSylow
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) : Sylow 2 (SectionSixBarP1 h) :=
  (sectionSixSylow h).mapSurjective
    (QuotientGroup.mk'_surjective (sectionSixLocalC h))

/-- The canonical faithful action of `barP₁` on the intrinsic `V₁`. -/
public noncomputable abbrev sectionSixQuotientAction
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) :
    MulDistribMulAction (SectionSixBarP1 h) (sectionSixLocalV h) := by
  let q := sectionSixQuotientMap h
  have hq : Function.Surjective q :=
    QuotientGroup.mk'_surjective (sectionSixLocalC h)
  have hker : q.ker = Stellmacher.SectionTwo.cSubgroup (sectionSixSylow h) :=
    QuotientGroup.ker_mk' (sectionSixLocalC h)
  exact Stellmacher.SectionTwo.quotientConjugationAction
    (sectionSixSylow h) q hq hker

/-- The source's action-defined subgroup `J(V₁,barS)`. -/
@[expose] public noncomputable def sectionSixBarredCritical
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) :
    Subgroup (SectionSixBarP1 h) := by
  let _ := sectionSixQuotientAction h
  exact Stellmacher.SectionOne.oneJ
    (V := sectionSixLocalV h)
    (sectionSixBarSylow h : Subgroup (SectionSixBarP1 h))

/-- The full preimage of `J(V₁,barS)`, mapped from `P₁` into `H`. -/
@[expose] public noncomputable def sectionSixBarredCriticalPreimage
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) : Subgroup H :=
  ((sectionSixBarredCritical h).comap (sectionSixQuotientMap h)).map P1.subtype

/-- The `J(V₁,barS)`-fixed subgroup of the intrinsic module. -/
@[expose] public noncomputable def sectionSixBarredFixedPoints
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) : Subgroup (sectionSixLocalV h) := by
  let _ := sectionSixQuotientAction h
  exact FixedPoints.subgroup (sectionSixBarredCritical h) (sectionSixLocalV h)

/-- The kernel of the canonical quotient action. -/
@[expose] public noncomputable def sectionSixBarredActionKernel
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) : Subgroup (SectionSixBarP1 h) := by
  let _ := sectionSixQuotientAction h
  exact fixingSubgroup (SectionSixBarP1 h) (Set.univ : Set (sectionSixLocalV h))

/-- The four transport facts supplied by the canonical barred-action setup. -/
public structure SectionSixBarredActionSetup
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) : Prop where
  sylow_image : (sectionSixSylow h : Subgroup P1).map P1.subtype = S
  localV_image : (sectionSixLocalV h).map P1.subtype = sectionSixV S P1
  action_faithful : sectionSixBarredActionKernel h = ⊥
  mem_fixedPoints_iff (w : sectionSixLocalV h) :
    w ∈ sectionSixBarredFixedPoints h ↔
      ((w : P1) : H) ∈
        Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H)

/-- Construct the canonical faithful quotient used in Stellmacher (6.4), and
identify its intrinsic module and fixed points with the ambient Section 6
notation. -/
public theorem sectionSix_barred_action_setup
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) :
    SectionSixBarredActionSetup h := by
  classical
  have hZmap :
      (Stellmacher.SectionTwo.zSubgroup (sectionSixSylow h)).map P1.subtype =
        omegaOneCenter S := by
    change (omegaOneCenterAmbient (sectionSixSylow h : Subgroup P1)).map P1.subtype =
      omegaOneCenterAmbient S
    rw [← omegaOneCenterAmbient_map_injective P1.subtype P1.subtype_injective,
      sectionSixSylow_image h]
  have hVmap : (sectionSixLocalV h).map P1.subtype = sectionSixV S P1 := by
    rw [sectionSixLocalV, Stellmacher.SectionTwo.vSubgroup,
      sectionSixV, ← hZmap]
    simpa [subgroupOf_map_subtype_eq] using
      localNormalClosure_map_eq_conjugateClosure
        ((Stellmacher.SectionTwo.zSubgroup (sectionSixSylow h)).map P1.subtype)
        P1 (Subgroup.map_subtype_le _)
  refine ⟨sectionSixSylow_image h, hVmap, ?_, ?_⟩
  · let q := sectionSixQuotientMap h
    have hq : Function.Surjective q :=
      QuotientGroup.mk'_surjective (sectionSixLocalC h)
    have hker : q.ker = Stellmacher.SectionTwo.cSubgroup (sectionSixSylow h) :=
      QuotientGroup.ker_mk' (sectionSixLocalC h)
    simpa [sectionSixBarredActionKernel, sectionSixQuotientAction] using
      Stellmacher.SectionTwo.quotientConjugationAction_faithful
        (sectionSixSylow h) q hq hker
  · intro w
    let q := sectionSixQuotientMap h
    have hq : Function.Surjective q :=
      QuotientGroup.mk'_surjective (sectionSixLocalC h)
    have hker : q.ker = Stellmacher.SectionTwo.cSubgroup (sectionSixSylow h) :=
      QuotientGroup.ker_mk' (sectionSixLocalC h)
    let _ := sectionSixQuotientAction h
    constructor
    · intro hw
      change w ∈ FixedPoints.subgroup
        (sectionSixBarredCritical h) (sectionSixLocalV h) at hw
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨x1, hx1, rfl⟩ := hx
      have hqx : q x1 ∈ sectionSixBarredCritical h := hx1
      have hwfix := (FixedPoints.mem_subgroup
        (M := sectionSixBarredCritical h) (a := w)).mp hw ⟨q x1, hqx⟩
      have hwfix' : q x1 • w = w := by
        simpa only [Subgroup.smul_def] using hwfix
      have hcoe := congrArg Subtype.val hwfix'
      have hact : ((q x1 • w : sectionSixLocalV h) : P1) =
          x1 * (w : P1) * x1⁻¹ := by
        simpa [sectionSixQuotientAction] using
          Stellmacher.SectionTwo.quotientConjugationAction_smul_coe
            (sectionSixSylow h) q hq hker x1 w
      rw [hact] at hcoe
      exact congrArg P1.subtype (mul_inv_eq_iff_eq_mul.mp hcoe)
    · intro hw
      rw [Subgroup.mem_centralizer_iff] at hw
      change w ∈ FixedPoints.subgroup
        (sectionSixBarredCritical h) (sectionSixLocalV h)
      rw [FixedPoints.mem_subgroup]
      intro x
      obtain ⟨x1, hx1⟩ := hq x
      have hxpre : x1 ∈ (sectionSixBarredCritical h).comap q := by
        change q x1 ∈ sectionSixBarredCritical h
        rw [hx1]
        exact x.property
      have hxcent := hw (P1.subtype x1)
        (Subgroup.mem_map_of_mem P1.subtype hxpre)
      have hxcentP : x1 * (w : P1) = (w : P1) * x1 := by
        exact P1.subtype_injective hxcent
      apply Subtype.ext
      have hact :=
        Stellmacher.SectionTwo.quotientConjugationAction_smul_coe
          (sectionSixSylow h) q hq hker x1 w
      have hval : ((q x1 • w : sectionSixLocalV h) : P1) = (w : P1) := by
        rw [show ((q x1 • w : sectionSixLocalV h) : P1) =
            x1 * (w : P1) * x1⁻¹ by
          simpa [sectionSixQuotientAction] using hact]
        rw [hxcentP, mul_inv_cancel_right]
      simpa only [Subgroup.smul_def, ← hx1] using hval

end Stellmacher.SectionsFiveToSeven
