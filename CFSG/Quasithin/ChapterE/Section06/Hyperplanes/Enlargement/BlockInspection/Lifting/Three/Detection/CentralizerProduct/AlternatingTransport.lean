module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.CentralizerProduct.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.CentralizerProduct.FactorAction
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.FactorCentralizers
public import Theory.GroupAction.CentralQuotientFusionGap.SylowFixed

/-!
# Transport control for moved alternating envelope factors

The actual V-action on an alternating E.6.7 factor has order two. If l lies
in that factor and c centralizes it, transport of U into V by l*c makes
conjugation by l preserve each U-action. Each action is inner through an
element of the actual Sylow omega-center, so it fixes that Sylow subgroup
and the center pointwise. The Sylow displacement lemma removes the central
ambiguity and shows that l centralizes U. The fixed-hyperplane calculation
then places l in M.

The argument uses E.6.7's ambient action bound and retains central extensions.
It needs neither the full natural-module lift of C.1.13 nor an intrinsic
order-two assertion about the A₃ Sylow omega-center quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7 and
E.6.23, printed pp.246 and 254–255; C.1.7–13, printed pp.123–125.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection
open InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] [Finite G]

/-- A moved alternating factor satisfies the published transporter contract.
The existing E.6.7 decomposition supplies the actual rank-one V-action;
all Sylow and inner-action witnesses are derived from the ambient hypotheses.
This applies in particular to n = 3 or 5 and to the hyperplane/corank-two
configuration of the envelope centralizer product. -/
theorem alternating_factor_transporter
    {K : GroupClass} {T : Sylow 2 G} {M V A U : Subgroup G}
    (h : HypothesisE61 K T M V) (h21 : OddCoreFree V)
    (hA : A ∈ obstructionFamily M V)
    (d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V A
      (layerEnvelope (centralizer (A : Set G)) (sylowCentralizer (T : Subgroup G) V)))
    (i : Fin d.count) (n : ℕ) (ha : ChapterC.IsAlternatingBlock (d.block i) n)
    (hUV : U ≤ V) (hmoved : ¬ d.block i ≤ centralizer (U : Set G)) :
    FactorTransporter (d.block i) M U V := by
  let _ := h.elementary
  let L := d.block i
  obtain ⟨S, _hS, hinner⟩ := envelope_factor_sylow_action h h21 hA d i
  have hVL : V ≤ normalizer (L : Set G) := by
    have hm (v : G) (hv : v ∈ V) (x : G) (hx : x ∈ L) : v * x * v⁻¹ ∈ L := by
      obtain ⟨z, _, he⟩ := hinner v hv
      rw [← he ⟨x, hx⟩]
      exact L.mul_mem (L.mul_mem z.property hx) (L.inv_mem z.property)
    intro v hv
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · exact hm v hv x
    · intro hx
      have hh := hm v⁻¹ (V.inv_mem hv) (v * x * v⁻¹) hx
      simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel,
        mul_one, one_mul] using hh
  let f : V →* MulAut L := L.normalizerMonoidHom.comp (inclusion hVL)
  have hk : f.ker = (V ⊓ centralizer (L : Set G)).subgroupOf V := by
    ext x
    constructor
    · intro hx
      have hx' : inclusion hVL x ∈ L.normalizerMonoidHom.ker := hx
      rw [normalizerMonoidHom_ker] at hx'
      exact ⟨x.property, hx'⟩
    · intro hx
      have hx' : inclusion hVL x ∈ L.normalizerMonoidHom.ker := by
        rw [normalizerMonoidHom_ker]
        exact hx.2
      exact hx'
  have hcard : Nat.card f.range = 2 := by
    rw [← index_ker, hk]
    change (V ⊓ centralizer (L : Set G)).relIndex V = 2
    calc
      _ = 2 ^ subgroupCorank V (V ⊓ centralizer (L : Set G)) := by
        rw [subgroupCorank_eq_quotient_finrank]
        exact Subgroup.relIndex_eq_two_pow_quotient_finrank V _
      _ = 2 := by rw [(d.alternating i n ha).1]; rfl
  intro l hl c hc htrans
  let lL : L := ⟨l, hl⟩
  let lN : normalizer (L : Set G) := ⟨l, L.le_normalizer hl⟩
  let cN : normalizer (L : Set G) := ⟨c, Subgroup.centralizer_le_normalizer _ hc⟩
  let gN := lN * cN
  have hcact : L.normalizerMonoidHom cN = 1 := by
    rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
    exact hc
  have hgact : L.normalizerMonoidHom gN = MulAut.conj lL := by
    change L.normalizerMonoidHom (lN * cN) = _
    rw [map_mul, hcact, mul_one]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  apply (alternating_factor_centralizer_le h d hUV i n ha hmoved).2
  refine ⟨hl, mem_centralizer_iff.mpr ?_⟩
  intro u hu
  let uV : V := ⟨u, hUV hu⟩
  have hu' : (l * c) * u * (l * c)⁻¹ ∈ V :=
    htrans (mem_map_of_mem (MulAut.conj (l * c)).toMonoidHom hu)
  let uV' : V := ⟨(l * c) * u * (l * c)⁻¹, hu'⟩
  have he : f uV' = MulAut.conj lL * f uV * (MulAut.conj lL)⁻¹ := by
    change L.normalizerMonoidHom (gN * inclusion hVL uV * gN⁻¹) = _
    rw [map_mul, map_mul, map_inv, hgact]
    rfl
  have hfix : f uV' = f uV := by
    by_cases h1 : f uV = 1
    · rw [he, h1, mul_one, mul_inv_cancel]
    · have h2 : f uV' ≠ 1 := by
        rw [he, ne_eq, conj_eq_one_iff]
        exact h1
      obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : f.range)).mp hcard
      have hv : f.rangeRestrict uV = w := hw _ (fun hh => h1 (congrArg Subtype.val hh))
      have hv' : f.rangeRestrict uV' = w := hw _ (fun hh => h2 (congrArg Subtype.val hh))
      exact congrArg Subtype.val (hv'.trans hv.symm)
  have hcomm : Commute (MulAut.conj lL) (f uV) := by
    exact (mul_inv_eq_iff_eq_mul).mp (he.symm.trans hfix)
  obtain ⟨z, hz, hzact⟩ := hinner u (hUV hu)
  have hfa : f uV = MulAut.conj z := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact (hzact x).symm
  obtain ⟨_, hz2, hzS⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
  have hfa2 : (f uV) ^ 2 = 1 := by
    rw [hfa, ← map_pow, hz2, map_one]
  have hZfix : center L ≤ (f uV).fixedSubgroup := by
    intro x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [hfa, MulAut.conj_apply, (mem_center_iff.mp hx z), mul_inv_cancel_right]
  have hSfix : (S : Subgroup L) ≤ (f uV).fixedSubgroup := by
    intro x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [hfa, MulAut.conj_apply, ← hzS x hx, mul_inv_cancel_right]
  have hlfix := MulAut.CentralQuotientFusionGap.eq_of_commute_conj_of_fixed_sylow
    (f uV) S hfa2 hZfix hSfix lL hcomm
  have hh := congrArg Subtype.val hlfix
  change u * l * u⁻¹ = l at hh
  exact (mul_inv_eq_iff_eq_mul).mp hh

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection
