module

public import Theory.Representation.HexacodeAction.WeightFourVectorStabilizer
public import Theory.Representation.HexacodeAction.FullWeightVectorQuotient
public import Theory.GroupTheory.PCoreLocalSetup
import Theory.Representation.BinaryOffender.CommutingPerfectSupports
import Theory.GroupTheory.SylowKernelCore
import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
import all Theory.Representation.HexacodeAction.ThompsonOffenders

/-!
# The actual weight-four vector stabilizer's two-core

The four concrete line-group words fix the weight-four point with zero
coordinates 4 and 5, and their displacements fill that point. The kernel
on the quotient by the point is a normal two-group. Order four therefore
identifies the line group with the actual vector stabilizer's two-core.
The original even orbit transports this identification to every weight-four
vector, preserving the literal scalar point.

The internal import of ThompsonOffenders is intentional: this calculation
companion reduces its concrete four words in private kernel-checked proofs.
No additional definition bodies are exposed.

Source: Aschbacher--Smith, 12.7.15 and the ensuing G.3.1 application, p.843.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode
open BinaryOffender ThompsonOffenders

private def seed : hexacode := ⟨systematicEncoder ![a,a,a], systematic_mem _⟩
private def lastPair : BinaryPermutation.SixPairsQuadratic.Pair := ⟨{4,5}, by decide⟩

private theorem seed_weight : hammingNorm seed.val = 4 := by decide

private theorem seed_ne_zero : seed ≠ 0 := by
  intro he
  have hh := seed_weight
  simp [he] at hh

private theorem seed_point :
    (Submodule.span F {seed}).restrictScalars Bit = zeroPairPlane lastPair := by
  have hle : (Submodule.span F {seed}).restrictScalars Bit ≤ zeroPairPlane lastPair := by
    intro w hw
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [field_smul_formula]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (by intro i hi; revert i hi; decide)
    · apply Submodule.smul_mem
      intro i hi
      revert i hi
      decide
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [fieldPoint_binary_finrank _ (finrank_span_singleton seed_ne_zero),
    zeroPairPlane_finrank]

set_option maxRecDepth 4096 in
private theorem line_fixes_seed (g : SylowModel.lineGroup) : evenAction g.val seed = seed := by
  obtain ⟨p, hp⟩ := g.property
  rw [← hp]
  apply Subtype.ext
  change Monomial.act (SylowModel.lineWord p).val.val (systematicEncoder ![a,a,a]) = _
  clear hp g
  revert p
  decide +kernel

set_option maxRecDepth 4096 in
private theorem line_displacement (g : SylowModel.lineGroup) (w : hexacode) :
    evenAction g.val w - w ∈ (Submodule.span F {seed}).restrictScalars Bit := by
  rw [seed_point]
  obtain ⟨p, hp⟩ := g.property
  rw [← hp]
  intro i hi
  change (Monomial.act (SylowModel.lineWord p).val.val w.val) (hexPos i) -
    w.val (hexPos i) = 0
  rw [← systematic_reconstruct w]
  have hh : ∀ (p : SylowModel.PairBits) (q : Fin 3 → K) (i : Fin 6),
      i ∈ lastPair.val →
      (Monomial.act (SylowModel.lineWord p).val.val (systematicEncoder q)) (hexPos i) -
        systematicEncoder q (hexPos i) = 0 := by decide +kernel
  exact hh p (hexProjection firstThree w) i hi

set_option maxRecDepth 4096 in
private theorem seed_displacement :
    ∃ w : hexacode, evenAction (SylowModel.lineWord (1,0)) w - w = seed := by
  have hh : ∃ q : Fin 3 → K,
      Monomial.act (SylowModel.lineWord (1,0)).val.val (systematicEncoder q) -
        systematicEncoder q = seed.val := by decide +kernel
  obtain ⟨q, hq⟩ := hh
  exact ⟨⟨systematicEncoder q, systematic_mem q⟩, Subtype.ext hq⟩

private theorem line_commutator :
    subspaceCommutator evenAction ⊤ SylowModel.lineGroup =
      (Submodule.span F {seed}).restrictScalars Bit := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, w, _, rfl⟩
    exact line_displacement ⟨g, hg⟩ w
  · intro w hw
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    obtain ⟨x, hx⟩ := seed_displacement
    have he : evenAction (SylowModel.lineWord (1,0)) (r • x) - r • x = r • seed := by
      change evenFieldAction (SylowModel.lineWord (1,0)) (r • x) - r • x = _
      rw [map_smul, ← smul_sub]
      exact congrArg (fun q => r • q) hx
    exact he ▸ Submodule.subset_span
      ⟨SylowModel.lineWord (1,0), ⟨(1,0), rfl⟩, r • x, Submodule.mem_top, rfl⟩

private theorem quotient_kernel_two (v : hexacode) :
    IsPGroup 2 (fullWeightVectorQuotientAction v).ker := by
  have hadd (w : hexacode) : w + w = 0 := by
    apply Subtype.ext
    funext i
    exact Prod.ext (bit_self_add _) (bit_self_add _)
  have hneg (w : hexacode) : -w = w := neg_eq_iff_add_eq_zero.mpr (hadd w)
  intro g
  refine ⟨1, ?_⟩
  suffices hg : g ^ 2 = 1 by simpa using hg
  have he : evenFieldAction (g.val.val ^ 2) = 1 := by
    apply LinearEquiv.ext
    intro w
    have hq := LinearMap.congr_fun (show fullWeightVectorQuotientAction v g.val = 1 from
      g.property) ((Submodule.span F {v}).mkQ w)
    have hd : evenAction g.val.val w - w ∈ Submodule.span F {v} := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change (Submodule.span F {v}).mkQ (evenFieldAction g.val.val w - w) = 0
      rw [map_sub, ← fullWeightVectorQuotientAction_mk, hq, Module.End.one_apply, sub_self]
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hd
    have hfix : evenAction g.val.val (evenAction g.val.val w - w) =
        evenAction g.val.val w - w := by
      rw [← hr]
      change evenFieldAction g.val.val (r • v) = r • v
      rw [map_smul, show evenFieldAction g.val.val v = v from g.val.property]
    rw [map_sub] at hfix
    change evenAction (g.val.val ^ 2) w = w
    rw [pow_two, map_mul, Module.End.mul_apply]
    calc
      evenAction g.val.val (evenAction g.val.val w) =
          (evenAction g.val.val (evenAction g.val.val w) - evenAction g.val.val w) +
            evenAction g.val.val w := (sub_add_cancel _ _).symm
      _ = (evenAction g.val.val w - w) + evenAction g.val.val w := congrArg (· + _) hfix
      _ = w := by rw [sub_eq_add_neg, hneg, add_right_comm, hadd, zero_add]
  exact Subtype.ext (Subtype.ext (evenFieldAction_injective
    (he.trans evenFieldAction.map_one.symm)))

private theorem core_card (v : hexacode) (hv : hammingNorm v.val = 4) :
    Nat.card ((fullWeightVectorStabilizer v).pCoreIn 2) = 4 := by
  let e := weightFourVectorStabilizerEquiv v hv
  rw [pCoreIn, card_map_of_injective (fullWeightVectorStabilizer v).subtype_injective,
    ← card_map_of_injective (f := e.toMonoidHom) e.injective, pCore_map_iso 2 e,
    ← Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq,
    Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card]

private theorem seed_core :
    (fullWeightVectorStabilizer seed).pCoreIn 2 = SylowModel.lineGroup := by
  have hk : (fullWeightVectorQuotientAction seed).ker ≤
      pCore 2 (fullWeightVectorStabilizer seed) :=
    le_sSup ⟨inferInstance, quotient_kernel_two seed⟩
  have hle : SylowModel.lineGroup ≤ (fullWeightVectorStabilizer seed).pCoreIn 2 := by
    intro g hg
    let gS : fullWeightVectorStabilizer seed := ⟨g, line_fixes_seed ⟨g, hg⟩⟩
    refine ⟨gS, hk ?_, rfl⟩
    apply LinearMap.ext
    intro w
    obtain ⟨w, rfl⟩ := (Submodule.span F {seed}).mkQ_surjective w
    change (Submodule.span F {seed}).mkQ (evenFieldAction g w) =
      (Submodule.span F {seed}).mkQ w
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (line_displacement ⟨g, hg⟩ w)
  exact (Subgroup.eq_of_le_of_card_ge hle (by
    rw [core_card seed seed_weight, SylowModel.lineGroup_card])).symm

private theorem core_conjugate (v : hexacode) (k : HexEvenAutomorphisms) :
    ((fullWeightVectorStabilizer v).pCoreIn 2).map (MulAut.conj k).toMonoidHom =
      (fullWeightVectorStabilizer (evenAction k v)).pCoreIn 2 := by
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj k).injective]
  congr 1
  ext g
  rw [mem_map_equiv]
  change evenAction (k⁻¹*g*k) v = v ↔ evenAction g (evenAction k v) = evenAction k v
  constructor
  · intro he
    have hh := congrArg (evenAction k) he
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, mul_assoc] using hh
  · intro he
    have hh := congrArg (evenAction k⁻¹) he
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left, mul_assoc,
      inv_mul_cancel, map_one, Module.End.one_apply] using hh

private theorem seed_orbit (v : hexacode) (hv : hammingNorm v.val = 4) :
    ∃ k : HexEvenAutomorphisms, evenAction k seed = v := by
  have hh : v ∈ Set.range (fun k : HexEvenAutomorphisms => evenAction k seed) := by
    rw [evenAction_orbit_eq_weight seed seed_ne_zero]
    exact hv.trans seed_weight.symm
  exact hh

/-- The actual even vector-stabilizer two-core has precisely the scalar
point as its common fixed space. -/
theorem weightFourVectorCore_fixed (v : hexacode) (hv : hammingNorm v.val = 4) :
    fixedSpace evenAction ((fullWeightVectorStabilizer v).pCoreIn 2) =
      (Submodule.span F {v}).restrictScalars Bit := by
  have hv0 : v ≠ 0 := by intro he; simp [he] at hv
  have hle : (Submodule.span F {v}).restrictScalars Bit ≤
      fixedSpace evenAction ((fullWeightVectorStabilizer v).pCoreIn 2) := by
    intro w hw g
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    change evenFieldAction g.val (r • v) = r • v
    rw [map_smul, show evenFieldAction g.val v = v from
      pCoreIn_le 2 (fullWeightVectorStabilizer v) g.property]
  have hd : Module.finrank Bit (fixedSpace evenAction
      ((fullWeightVectorStabilizer v).pCoreIn 2)) = 2 := by
    obtain ⟨k, rfl⟩ := seed_orbit v hv
    rw [← core_conjugate, seed_core]
    exact (fixedSpaceConjEquiv evenAction SylowModel.lineGroup k).finrank_eq.symm.trans
      lineFixed_finrank
  exact (Submodule.eq_of_le_of_finrank_eq hle (by
    rw [fieldPoint_binary_finrank _ (finrank_span_singleton hv0), hd])).symm

/-- The original whole hexacode commutator of the actual vector-stabilizer
two-core is the same scalar point. -/
theorem weightFourVectorCore_commutator (v : hexacode) (hv : hammingNorm v.val = 4) :
    subspaceCommutator evenAction ⊤ ((fullWeightVectorStabilizer v).pCoreIn 2) =
      (Submodule.span F {v}).restrictScalars Bit := by
  obtain ⟨k, rfl⟩ := seed_orbit v hv
  have htop : (⊤ : Submodule Bit hexacode).map (evenAction k) = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top]
    exact (evenFieldAction k).surjective
  rw [← core_conjugate, seed_core, ← htop, ← subspaceCommutator_map_conj,
    line_commutator]
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    change evenFieldAction k (r • seed) ∈ Submodule.span F {evenAction k seed}
    rw [map_smul]
    exact Submodule.mem_span_singleton.mpr ⟨r, rfl⟩
  · intro w hw
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    refine ⟨r • seed, Submodule.mem_span_singleton.mpr ⟨r, rfl⟩, ?_⟩
    exact (evenFieldAction k).map_smul r seed

end Representation.Hexacode
