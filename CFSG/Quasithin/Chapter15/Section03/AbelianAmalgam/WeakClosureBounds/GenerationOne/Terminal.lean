module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.Setup
public import Theory.GroupTheory.CentralPChiefCore
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.CComponent.SolvableQuotient

/-!
# The terminal centralization argument in 15.3.65

Fixation of the image of `Z_S` gives `[Z_S,H] ≤ Z`. Since `H` centralizes
`Z`, coprime commutator idempotence lifts this to centralization of `Z_S`
by `O²(H)`. Normality of the residual then gives centralization of the
whole conjugate span `U = ⟨Z_S^H⟩`. Faithfulness of the actual quotient
representation forces the image of every subgroup of `O²(H)` to vanish.

Thus the remaining representation calculation must prove seed fixation;
it cannot take that assertion as a source-theorem hypothesis. The lemmas
here isolate and prove the group-theoretic implication after that calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.65, final paragraph of the proof on printed p.1152.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- Relative normality of the embedded residual, without ambient normality of H. -/
theorem normalizes_residual (H : Subgroup G) :
    H ≤ normalizer (residual H : Set G) := by
  apply (normal_subgroupOf_iff_le_normalizer (residual_le H)).mp
  apply normal_embedded_pResidual_subgroupOf 2 (le_refl H)
  rw [subgroupOf_self]
  infer_instance

/-- Coprime action lifts centralization modulo Z for a two-perfect actor.
It is not necessary for that actor itself to have odd order. -/
theorem centralizes_seed_of_twoPerfect [Finite G]
    {R ZS Z H : Subgroup G}
    (hR : IsPPerfect 2 R) (hRH : R ≤ H) (hZS : IsPGroup 2 ZS)
    (hZZS : Z ≤ ZS) (hHZ : H ≤ centralizer (Z : Set G))
    (hcomm : ⁅ZS, H⁆ ≤ Z) : R ≤ centralizer (ZS : Set G) := by
  have hc : ⁅ZS, R⁆ ≤ Z := (commutator_mono le_rfl hRH).trans hcomm
  have hn : R ≤ normalizer (ZS : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hc.trans hZZS)
  have hid := commutator_coprime_order_generators_idempotent 2 ZS R hZS hn
  have hgen := closure_coprime_order_eq_top_of_pResidual_eq_top 2
    ((pResidual_eq_top_iff 2 R).mpr hR)
  have hmap : (⊤ : Subgroup R).map R.subtype = R := by
    ext x
    exact ⟨fun ⟨y, _, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, mem_top _, rfl⟩⟩
  rw [hgen, hmap] at hid
  change ⁅⁅ZS, R⁆, R⁆ = ⁅ZS, R⁆ at hid
  have hz : ⁅Z, R⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp (hRH.trans hHZ))
  have hh : ⁅⁅ZS, R⁆, R⁆ = ⊥ :=
    bot_unique ((commutator_mono hc le_rfl).trans_eq hz)
  rw [hh] at hid
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hid.symm)

/-- A normal subgroup centralizing the seed centralizes all its conjugates.
Normality is needed only relative to the group taking the conjugate span. -/
theorem centralizes_span_of_normalizes
    {R ZS H : Subgroup G} (hHR : H ≤ normalizer (R : Set G))
    (hRZ : R ≤ centralizer (ZS : Set G)) :
    R ≤ centralizer (conjugateSpanBy ZS H : Set G) := by
  apply le_centralizer_iff.mp
  apply (closure_le _).mpr
  rintro x ⟨h, hh, z, hz, rfl⟩
  apply mem_centralizer_iff.mpr
  intro r hr
  have hr' : h⁻¹ * r * h ∈ R := by
    simpa only [inv_inv, SetLike.mem_coe] using (hHR (H.inv_mem hh) r).mp hr
  have hc := mem_centralizer_iff.mp (hRZ hr') z hz
  have he := congrArg (fun x : G => h * x * h⁻¹) hc
  simpa only [mul_assoc, mul_inv_cancel, mul_inv_cancel_left, mul_one] using he.symm

/-- The source coprime-action step with the actual two-residual. -/
theorem residual_centralizes_span [Finite G]
    {H ZS Z : Subgroup G} (hZS : IsPGroup 2 ZS) (hZZS : Z ≤ ZS)
    (hHZ : H ≤ centralizer (Z : Set G)) (hcomm : ⁅ZS, H⁆ ≤ Z) :
    residual H ≤ centralizer (conjugateSpanBy ZS H : Set G) :=
  centralizes_span_of_normalizes (normalizes_residual H)
    (centralizes_seed_of_twoPerfect (isPPerfect_embedded_pResidual 2 H)
      (residual_le H) hZS hZZS hHZ hcomm)

/-- Faithfulness refers to the literal image in H/O₂(H), not to a family label. -/
theorem actorImage_eq_bot_of_centralizes
    {H U Z K : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (hKU : K ≤ centralizer (U : Set G)) :
    actorImage H K = ⊥ := by
  apply bot_unique
  rintro q ⟨k, hk, rfl⟩
  change QuotientGroup.mk' (pCore 2 H) k = 1
  apply a.faithful
  apply LinearMap.ext
  intro v
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) v.toMul
  have hv : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) = v :=
    congrArg Additive.ofMul hu
  rw [← hv, a.conjugation, map_one]
  have hc := mem_centralizer_iff.mp (hKU hk) u u.property
  change (u : G) * (k : G) = (k : G) * (u : G) at hc
  have he : (k : G) * u * (k : G)⁻¹ = u := by rw [← hc, mul_inv_cancel_right]
  change Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) _) =
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u)
  congr 2
  exact Subtype.ext he

/-- A genuine C-component of H has nontrivial image modulo its solvable two-core.
The C-component assumption is internal to H. -/
theorem actorImage_ne_bot_of_component [Finite G]
    {H K : Subgroup G} (hK : (K.subgroupOf H).IsCComponent) :
    actorImage H K ≠ ⊥ := by
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  exact hK.map_quotient_ne_bot (pCore 2 H)

/-- Seed fixation contradicts a nontrivial component image after coprime
lifting. The model calculation proving fixation remains outside this lemma. -/
theorem not_seedSpace_le_fixedSpace [Finite G]
    {H U Z ZS K : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (hU : U = conjugateSpanBy ZS H)
    (hZZS : Z ≤ ZS) (hHZ : H ≤ centralizer (Z : Set G))
    (hKR : K ≤ residual H) (hK : actorImage H K ≠ ⊥) :
    ¬ seedSpace a ZS ≤ fixedSpace a.representation ⊤ := by
  intro hfix
  have hZU : ZS ≤ U := hU ▸ le_conjugateSpanBy ZS H
  have hZS : IsPGroup 2 ZS :=
    (IsElementaryAbelian.isPGroup (p := 2) (G := U)).to_le hZU
  have hcomm := (seedSpace_le_fixedSpace_iff a hZU).mp hfix
  have hRU := residual_centralizes_span hZS hZZS hHZ hcomm
  rw [← hU] at hRU
  exact hK (actorImage_eq_bot_of_centralizes a (hKR.trans hRU))

/-- The terminal contradiction from the actual E.2.2 component and residual
orbit identity. Neither the nontrivial image nor its containment is assumed. -/
theorem not_seedSpace_le_fixedSpace_of_component [Finite G]
    {H U Z ZS K T : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (hU : U = conjugateSpanBy ZS H)
    (hZZS : Z ≤ ZS) (hHZ : H ≤ centralizer (Z : Set G))
    (hK : (K.subgroupOf H).IsCComponent)
    (hres : residual H = conjugateSpanBy K T) :
    ¬ seedSpace a ZS ≤ fixedSpace a.representation ⊤ := by
  apply not_seedSpace_le_fixedSpace a hU hZZS hHZ
    (hK := actorImage_ne_bot_of_component hK)
  rw [hres]
  exact le_conjugateSpanBy K T

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne
