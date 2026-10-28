module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad
public import Theory.Mathieu.M24.LocalGeometry.OctadCharacteristicTwo

/-!
# Intrinsic octad two-cores and the native alternating image

Octad transitivity transports the checked seed equality between the
intrinsic two-core and the pointwise restriction kernel. This identifies
the two-core for every native octad, with no ambient-normality assumption.
The transported order is sixteen. The known stabilizer order then makes
the eight-point permutation image an index-two subgroup of the symmetric
group, and hence precisely the alternating group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.14.1(4) and the proof of H.15.2, printed pp.397–399. The seed equality
is proved in `Theory.Mathieu.M24.LocalGeometry.OctadCharacteristicTwo`.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
namespace MathieuCode.CocodeOctad
noncomputable section

lemma mem_coordinateAction_ker (O : Octad) (g : octadStabilizer O) :
    g ∈ (coordinateAction O).ker ↔ ∀ i ∈ O.val, g.val • i = i := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i hi
    exact congrArg Subtype.val (Equiv.congr_fun h ⟨i, hi⟩)
  · intro h
    exact Equiv.ext (fun i => Subtype.ext (h i.val i.property))

lemma coordinateAction_ker_eq (O : Octad) :
    (coordinateAction O).ker = (LinearFourCore.action O).ker := by
  ext g
  rw [mem_coordinateAction_ker, LinearFourCore.mem_action_ker]

/-- The intrinsic two-core equals the pointwise octad kernel for every native octad. -/
lemma core_eq_coordinateKernel (O : Octad) :
    pCore 2 (octadStabilizer O) = (coordinateAction O).ker := by
  obtain ⟨g, hg⟩ := exists_smul_octad_eq LinearFourCore.seedOctad O
  have hs : octadStabilizer O =
      (octadStabilizer LinearFourCore.seedOctad).map (MulAut.conj g).toMonoidHom := by
    change MulAction.stabilizer M24 O.val =
      (MulAction.stabilizer M24 LinearFourCore.seedOctad.val).map _
    rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  let e : octadStabilizer LinearFourCore.seedOctad ≃* octadStabilizer O :=
    ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr hs.symm)
  have he (x : octadStabilizer LinearFourCore.seedOctad) :
      (e x).val = g * x.val * g⁻¹ := rfl
  have hf (x : octadStabilizer LinearFourCore.seedOctad) :
      e x ∈ (coordinateAction O).ker ↔ x ∈ (coordinateAction LinearFourCore.seedOctad).ker := by
    rw [mem_coordinateAction_ker, mem_coordinateAction_ker]
    constructor
    · intro hx i hi
      have hai : g • i ∈ O.val := by
        rw [← hg]
        exact Finset.smul_mem_smul_finset hi
      have hh := hx (g • i) hai
      rw [he] at hh
      have hh' : g • (x.val • i) = g • i := by
        simpa only [mul_smul, inv_smul_smul] using hh
      exact (MulAction.injective g) hh'
    · intro hx i hi
      have hgi : g⁻¹ • i ∈ LinearFourCore.seedOctad.val := by
        rw [← hg] at hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_smul_finset.mp hi
        simpa using hj
      rw [he, mul_smul, mul_smul, hx _ hgi, smul_inv_smul]
  have hk : ((coordinateAction LinearFourCore.seedOctad).ker).map e.toMonoidHom =
      (coordinateAction O).ker := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [hf]
    constructor
    · rintro ⟨z, hz, heq⟩
      exact e.injective heq ▸ hz
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [← pCore_map_iso 2 e, ← hk,
    coordinateAction_ker_eq, LinearFourCore.seed_core_eq_kernel]

lemma card_coordinateKernel (O : Octad) : Nat.card (coordinateAction O).ker = 16 := by
  obtain ⟨g, hg⟩ := exists_smul_octad_eq LinearFourCore.seedOctad O
  let e : octadStabilizer LinearFourCore.seedOctad ≃* octadStabilizer O :=
    MulAction.stabilizerEquivStabilizer hg.symm
  have hc := Nat.card_congr (e.subgroupMap (pCore 2
    (octadStabilizer LinearFourCore.seedOctad))).toEquiv
  change Nat.card (pCore 2 (octadStabilizer LinearFourCore.seedOctad)) =
    Nat.card ((pCore 2 (octadStabilizer LinearFourCore.seedOctad)).map e.toMonoidHom) at hc
  rw [pCore_map_iso 2 e, LinearFourCore.seed_core_eq_kernel,
    LinearFourCore.kernel_card, core_eq_coordinateKernel] at hc
  exact hc.symm

lemma card_coordinateAction_range (O : Octad) : Nat.card (coordinateAction O).range = 20160 := by
  have hc := Subgroup.card_mul_index (coordinateAction O).ker
  rw [card_coordinateKernel, octadStabilizer_card, Subgroup.index_ker] at hc
  omega

/-- The native eight-point restriction has the full alternating image. -/
lemma coordinateAction_range (O : Octad) :
    (coordinateAction O).range = alternatingGroup O.val := by
  have hcard : Nat.card O.val = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact m24Blocks_card _ O.property
  have hperm : Nat.card (Equiv.Perm O.val) = 40320 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hcard]
    decide
  have hi : (coordinateAction O).range.index = 2 := by
    have hc := Subgroup.card_mul_index (coordinateAction O).range
    rw [card_coordinateAction_range, hperm] at hc
    omega
  have : (coordinateAction O).range.Normal := Subgroup.normal_of_index_eq_two hi
  have : IsCyclic (Equiv.Perm O.val ⧸ (coordinateAction O).range) := isCyclic_of_prime_card hi
  have hle : alternatingGroup O.val ≤ (coordinateAction O).range := by
    rw [← alternatingGroup.commutator_perm_eq (by rw [hcard]; decide)]
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  have : Nontrivial O.val := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  rw [card_coordinateAction_range, nat_card_alternatingGroup, hcard]
  decide

end
end MathieuCode.CocodeOctad
