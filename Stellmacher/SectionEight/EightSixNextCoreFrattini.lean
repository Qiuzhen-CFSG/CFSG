module
public import Stellmacher.SectionEight.EightSixNextResidualCoreAction
public import Stellmacher.SectionEight.EightSixNextQuotientModule
public import Theory.GroupTheory.CommutatorPreimageFrattini

/-!
# The Frattini subgroup of the next core

For the actual length-two configuration of (8.6), suppose the initial
center has order four, the next center is central in its stabilizer, and
the prescribed opposite-core intersection D is elementary abelian. Then
the next two-core R has Frattini subgroup equal to the next central line Z.
The local equation-one packet and the actual definitions of D and L are
retained; the assertion does not require an actor-cost branch hypothesis.

The next-core generation theorem gives R=VD. The literal quotient V/Z is
elementary, and [V,R]=Z makes its image commute with the elementary image
of D in R/Z. Every element of R/Z consequently has order at most two, so
this quotient is elementary and Φ(R)≤Z. The reverse inclusion follows
directly from Z=[V,R]≤[R,R]≤Φ(R). All quotients use the same normality
instance supplied in their construction.

This proves the Frattini clause of Stellmacher (8.6)(b2), Journal of
Algebra 190 (1997), printed p.44. The quotient calculation is also the
general reduction before the high-cost step in assertion (18), p.45.
Existing high-cost declarations are unchanged.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement Pointwise IsMulCommutative
universe u
public theorem eight_six_next_core_frattini
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (helementary : IsElementaryAbelianSubgroup 2 D) :
    FrattiniAmbient (QAt ctx.Γ ctx.criticalPath.firstStep) =
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  have hRP : R ≤ P := by
    change Γ.twoCoreAt _ ≤ _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hVR : V ≤ R := SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp
    (by exact hlength ▸ by decide) _
  have hDR : D ≤ R := hD ▸ inf_le_right
  have hZV : Z ≤ V := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hPZ : P ≤ Subgroup.normalizer (Z : Set G) := stabilizer_le_normalizer_z Γ _
  have hN : (Z.subgroupOf R).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hRP.trans hPZ)
  let _ := hN
  let W := R ⧸ Z.subgroupOf R
  let projection := QuotientGroup.mk' (Z.subgroupOf R)
  have hgen : R = V ⊔ D := eight_six_next_core_eq_v_sup_intersection ctx hlength
    previous D L Q hprev hD hL data
  obtain ⟨hNV,hWV,_⟩ := eight_six_next_quotient_module_data_local ctx hcenter hlength
    hcard data.first_commutator
  have hsquareV (v : G) (hv : v ∈ V) : v ^ 2 ∈ Z := by
    let _ := hNV
    let _ := hWV
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (V ⧸ Z.subgroupOf V))
      (QuotientGroup.mk' (Z.subgroupOf V) ⟨v,hv⟩)
    rw [← map_pow] at hh
    exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf V) ((⟨v,hv⟩ : V) ^ 2)).mp hh
  let _ : IsElementaryAbelian 2 D := helementary
  have hDNV : D ≤ Subgroup.normalizer (V : Set G) :=
    (hDR.trans hRP).trans (stabilizer_le_normalizer_v Γ _)
  have hsquare (w : W) : w ^ 2 = 1 := by
    obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf R) w
    have hr : (r:G) ∈ (V : Set G) * (D : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left V D hDNV,←hgen]
      exact r.property
    obtain ⟨v,hv,d,hd,hvd⟩ := hr
    let vR : R := ⟨v,hVR hv⟩
    let dR : R := ⟨d,hDR hd⟩
    have heq : r = vR * dR := Subtype.ext hvd.symm
    have hcomm : Commute (projection vR) (projection dR) := by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [←map_commutatorElement]
      apply (QuotientGroup.eq_one_iff _).mpr
      change ⁅v,d⁆ ∈ Z
      exact data.first_commutator.le (Subgroup.commutator_mem_commutator hv (hDR hd))
    rw [heq,map_mul,hcomm.mul_pow,←map_pow,←map_pow]
    have hv2 : projection (vR^2) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hsquareV v hv)
    have hd2 : dR^2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian d hd)
    rw [hv2,hd2,map_one,mul_one]
  have hW : IsElementaryAbelian 2 W := {
    toIsMulCommutative := ⟨⟨fun a b => by
      have hinv (w : W) : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsquare w)
      calc a*b = (a*b)⁻¹ := (hinv _).symm
           _ = b*a := by rw [mul_inv_rev,hinv,hinv]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }
  let _ := hW
  have hRtwo : IsPGroup 2 R := by
    change IsPGroup 2 (Γ.twoCoreAt _)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  let _ : Fact (IsPGroup 2 R) := ⟨hRtwo⟩
  apply le_antisymm
  · have hPhi := Subgroup.frattini_le_of_elementary_quotient hRtwo (Z.subgroupOf R) hW
    have hh := Subgroup.map_mono (f := R.subtype) hPhi
    rw [Subgroup.map_subgroupOf_eq_of_le (hZV.trans hVR)] at hh
    exact hh
  · have hcomm : ⁅R,R⁆ ≤ FrattiniAmbient R := by
      have hh := Subgroup.map_mono (f := R.subtype)
        (commutator_le_frattini_of_isPGroup (p := 2) (R := R))
      rw [Subgroup.map_subtype_commutator] at hh
      exact hh
    exact data.first_commutator.symm.le.trans
      ((Subgroup.commutator_mono hVR le_rfl).trans hcomm)
end Stellmacher.SectionEight
