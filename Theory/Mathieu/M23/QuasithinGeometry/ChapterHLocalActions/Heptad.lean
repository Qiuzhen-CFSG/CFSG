module

public import Theory.Mathieu.M23.QuasithinGeometry.CommonFour.Cores
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalCore
public import Theory.Representation.BinaryPrimeDegree
public import Theory.Representation.Quotient

/-!
# The intrinsic heptad quotient and its irreducible binary action

The actual heptad complement acts on its translation kernel through the
existing four binary coordinates. A three-cycle has no nonzero fixed vector.
Simplicity of A7 then makes every nonzero invariant subspace faithful, and
its order-five elements force that subspace to have dimension at least four.
Thus this concrete conjugation module is irreducible.

The alternating quotient has trivial two-core, so the translation kernel
is the intrinsic two-core. An element of native M23 transports the
computational heptad to the literal seven points of the source octad under
`MathieuCode.pointEmbedding`. The induced stabilizer, core and quotient
isomorphisms retain the full conjugation formula in this source marking.

Source: Aschbacher–Smith, H.14.2(3), printed p.397 of the combined
1 March 2004 manuscript. The split extension and binary coordinates are
reused from `HeptadStructure.SplitExtension` and `HeptadStructure.BinaryAction`.
The general binary prime-degree bound is `Representation.BinaryPrimeDegree`.
-/

@[expose] public section
open Sporadic.Mathieu Sporadic.Mathieu.M23Geometry
open Sporadic.Mathieu.M24LocalGeometry MathieuCode
open Representation
open scoped Pointwise

namespace Sporadic.Mathieu.M23Geometry.ChapterHLocalActions
noncomputable section

/-- The four-dimensional binary coordinate space. -/
abbrev Four := Fin 4 → ZMod 2

/-- The concrete A7 conjugation representation in the translation coordinates. -/
def heptadRepresentation : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four where
  toFun a := (heptadLinearAction a).toLinearMap
  map_one' := congrArg LinearEquiv.toLinearMap heptadLinearAction.map_one
  map_mul' a b := congrArg LinearEquiv.toLinearMap (heptadLinearAction.map_mul a b)

/-- The actual binary action is irreducible, by simplicity and the prime-five degree bound. -/
theorem heptadRepresentation_irreducible : IsIrreducible heptadRepresentation := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hz : heptadRepresentation.invariants = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    exact (heptadLinearAction_cycle_fixed_iff v).mp (hv AlternatingSection.c)
  refine ⟨fun N => ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  have hfaith : Function.Injective N.toRepresentation := by
    rcases N.toRepresentation.normal_ker.eq_bot_or_eq_top with hk | hk
    · exact N.toRepresentation.ker_eq_bot_iff.mp hk
    · have he : N.toRepresentation = 1 := MonoidHom.ker_eq_top_iff.mp hk
      have hle : N.toSubmodule ≤ heptadRepresentation.invariants := by
        intro v hv g
        have h := DFunLike.congr_fun (congrArg (fun σ => σ g) he) ⟨v, hv⟩
        exact congrArg Subtype.val h
      rw [hz] at hle
      exact (hN (Subrepresentation.toSubmodule_injective (le_bot_iff.mp hle))).elim
  have hlo := BinaryPrimeDegree.orderOf_le_finrank N.toRepresentation hfaith
    (by decide : Nat.Prime 5) (by decide : 5 ≠ 2) (show 5 ∣ Nat.card (alternatingGroup (Fin 7)) by
      rw [nat_card_alternatingGroup]; norm_num [Nat.factorial])
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hlo
  apply Subrepresentation.toSubmodule_injective
  by_contra hnt
  have hlt := Submodule.finrank_lt hnt
  have hdim : Module.finrank (ZMod 2) Four = 4 := by simp [Four]
  rw [hdim] at hlt
  omega

/-- The seven native points obtained by deleting the distinguished point from the marked octad. -/
def sourceHeptad : Finset (Fin 23) := {0, 1, 2, 3, 10, 16, 22}

/-- The source seven-set is a heptad of the native Witt design. -/
theorem sourceHeptad_mem : sourceHeptad ∈ m23Blocks := by decide +kernel

/-- Incidence with the actual marked octad through the native point embedding. -/
theorem sourceHeptad_incidence (i : Fin 23) :
    m23PointEmbedding i ∈ standardOctad.val ↔ i ∈ sourceHeptad := by
  revert i; decide +kernel

/-- The literal restricted octad stabilizer is the setwise stabilizer of the source heptad. -/
theorem sourceStabilizer_eq : CommonFour.markedHeptadStabilizer =
    MulAction.stabilizer M23 sourceHeptad := by
  ext g
  change pointEmbedding g ∈ octadStabilizer standardOctad ↔ _
  rw [show octadStabilizer standardOctad = MulAction.stabilizer M24 standardOctad.val from rfl]
  rw [MulAction.mem_stabilizer_finset, MulAction.mem_stabilizer_finset]
  constructor
  · intro hg i
    rw [← sourceHeptad_incidence, ← sourceHeptad_incidence]
    have h := hg (m23PointEmbedding i)
    change (pointEmbedding g).val (m23PointEmbedding i) ∈ standardOctad.val ↔
      m23PointEmbedding i ∈ standardOctad.val at h
    rw [pointEmbedding_apply] at h
    exact h
  · intro hg j
    by_cases hj : j = 0
    · subst j
      rw [show pointEmbedding g • (0 : Fin 24) = 0 from pointEmbedding_fixed g]
    · obtain ⟨i, hi⟩ := m23PointEquiv.surjective ⟨j, hj⟩
      have he : m23PointEmbedding i = j := congrArg Subtype.val hi
      rw [← he, show pointEmbedding g • m23PointEmbedding i = m23PointEmbedding (g • i) from
        pointEmbedding_apply g i, sourceHeptad_incidence, sourceHeptad_incidence]
      exact hg i


/-- The computational heptad translation kernel is exactly its intrinsic two-core. -/
theorem heptad_core_eq_kernel : pCore 2 heptadStabilizer = heptadKernel := by
  let f := heptadAlternatingAction
  have hf : Function.Surjective f :=
    fun a => ⟨AlternatingSection.s a, heptadAlternatingAction_section a⟩
  have hn : ((pCore 2 heptadStabilizer).map f).Normal :=
    Subgroup.Normal.map inferInstance f hf
  have hp : IsPGroup 2 ((pCore 2 heptadStabilizer).map f) := pCore_isPGroup.map f
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hb : (pCore 2 heptadStabilizer).map f = ⊥ := by
    rcases hn.eq_bot_or_eq_top with h | h
    · exact h
    · have htwo : IsPGroup 2 (alternatingGroup (Fin 7)) :=
        (h ▸ hp).of_surjective (⊤ : Subgroup (alternatingGroup (Fin 7))).subtype
          (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
      obtain ⟨n, hn⟩ := htwo.exists_card_dvd_pow
      have hc : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
        rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
      have hd : 3 ∣ 2 ^ n := (show 3 ∣ 2520 by decide).trans (hc ▸ hn)
      exact False.elim ((by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd))
  apply le_antisymm
  · rw [← heptadAlternatingAction_ker]
    intro x hx
    have hmem : f x ∈ (⊥ : Subgroup (alternatingGroup (Fin 7))) :=
      hb ▸ (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    exact Subgroup.mem_bot.mp hmem
  · exact le_sSup ⟨inferInstance, heptadKernel_isTwoGroup⟩

/-- Every stabilizer element acts on translations by its alternating quotient image. -/
theorem heptad_conjugation (g : heptadStabilizer) (v : Four) :
    g * (heptadBinaryEquiv (Multiplicative.ofAdd v)).val * g⁻¹ =
      (heptadBinaryEquiv (Multiplicative.ofAdd
        (heptadRepresentation (heptadAlternatingAction g) v))).val := by
  obtain ⟨z, rfl⟩ := heptadSplitEquiv.surjective g
  have ha : heptadAlternatingAction (heptadSplitEquiv z) = z.right :=
    Subtype.ext (heptadAction_split z)
  rw [ha]
  change (z.left.val * AlternatingSection.s z.right) * _ *
    (z.left.val * AlternatingSection.s z.right)⁻¹ = _
  change _ = (heptadBinaryEquiv
    (heptadBinaryAction z.right (Multiplicative.ofAdd v))).val
  rw [heptadBinaryAction_equivariant]
  have hcomm := congrArg Subtype.val
    (heptadKernel_mul_comm z.left (heptadConjugation z.right (heptadBinaryEquiv (Multiplicative.ofAdd v))))
  simp only [Subgroup.coe_mul] at hcomm
  calc
    _ = z.left.val * (heptadConjugation z.right
        (heptadBinaryEquiv (Multiplicative.ofAdd v))).val * z.left.val⁻¹ := by
      rw [heptadConjugation_coe]; group
    _ = _ := by rw [hcomm, mul_inv_cancel_right]

/-- A native M23 conjugator from the computational heptad to the source heptad. -/
def sourceMarking : M23 := Classical.choose (exists_smul_omega_eq sourceHeptad_mem)

/-- The chosen marking sends the actual seven-point sets to one another. -/
theorem sourceMarking_heptad : sourceMarking • omega = sourceHeptad :=
  Classical.choose_spec (exists_smul_omega_eq sourceHeptad_mem)

/-- The same ambient conjugation transports the entire stabilizer. -/
theorem sourceMarking_stabilizer :
    heptadStabilizer.map (MulAut.conj sourceMarking).toMonoidHom =
      CommonFour.markedHeptadStabilizer := by
  rw [sourceStabilizer_eq, ← sourceMarking_heptad]
  exact (MulAction.stabilizer_smul_eq_stabilizer_map_conj sourceMarking omega).symm

/-- The stabilizer equivalence induced by the native ambient conjugator. -/
def sourceStabilizerEquiv : heptadStabilizer ≃* CommonFour.markedHeptadStabilizer :=
  ((MulAut.conj sourceMarking).subgroupMap heptadStabilizer).trans
    (MulEquiv.subgroupCongr sourceMarking_stabilizer)

/-- The stabilizer equivalence retains its ambient conjugation formula. -/
theorem sourceStabilizerEquiv_coe (g : heptadStabilizer) :
    (sourceStabilizerEquiv g).val = sourceMarking * g.val * sourceMarking⁻¹ := rfl

/-- The pointwise computational kernel identifies with the intrinsic source two-core. -/
def sourceCoreEquiv : heptadKernel ≃* pCore 2 CommonFour.markedHeptadStabilizer :=
  (MulEquiv.subgroupCongr heptad_core_eq_kernel.symm).trans
    ((sourceStabilizerEquiv.subgroupMap (pCore 2 heptadStabilizer)).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 2 sourceStabilizerEquiv)))

/-- Four binary translation coordinates on the intrinsic source two-core. -/
def sourceBinaryEquiv : Multiplicative Four ≃* pCore 2 CommonFour.markedHeptadStabilizer :=
  heptadBinaryEquiv.trans sourceCoreEquiv

/-- The binary coordinates are transported by the same stabilizer equivalence. -/
theorem sourceBinaryEquiv_coe (v : Multiplicative Four) :
    (sourceBinaryEquiv v).val = sourceStabilizerEquiv (heptadBinaryEquiv v).val := rfl

/-- The literal source stabilizer modulo its intrinsic two-core is A7. -/
def sourceQuotientEquiv :
    (CommonFour.markedHeptadStabilizer ⧸ pCore 2 CommonFour.markedHeptadStabilizer) ≃*
      alternatingGroup (Fin 7) :=
  (QuotientGroup.congr _ _ sourceStabilizerEquiv.symm
    (pCore_map_iso 2 sourceStabilizerEquiv.symm)).trans
    ((QuotientGroup.quotientMulEquivOfEq heptad_core_eq_kernel).trans
      heptadQuotientAlternatingEquiv)

/-- The quotient equivalence is the transported seven-label action on representatives. -/
theorem sourceQuotientEquiv_mk (g : CommonFour.markedHeptadStabilizer) :
    sourceQuotientEquiv (QuotientGroup.mk g) =
      heptadAlternatingAction (sourceStabilizerEquiv.symm g) := rfl

/-- The source coordinates intertwine actual conjugation with the A7 representation. -/
theorem sourceBinaryEquiv_conjugation (g : CommonFour.markedHeptadStabilizer) (v : Four) :
    g * (sourceBinaryEquiv (Multiplicative.ofAdd v)).val * g⁻¹ =
      (sourceBinaryEquiv (Multiplicative.ofAdd
        (heptadRepresentation (sourceQuotientEquiv (QuotientGroup.mk g)) v))).val := by
  rw [sourceQuotientEquiv_mk, sourceBinaryEquiv_coe, sourceBinaryEquiv_coe]
  obtain ⟨h, rfl⟩ := sourceStabilizerEquiv.surjective g
  rw [sourceStabilizerEquiv.symm_apply_apply]
  simpa only [map_mul, map_inv] using congrArg sourceStabilizerEquiv (heptad_conjugation h v)

/-- The representation of the actual intrinsic quotient in these binary coordinates. -/
def sourceQuotientRepresentation : Representation (ZMod 2)
    (CommonFour.markedHeptadStabilizer ⧸ pCore 2 CommonFour.markedHeptadStabilizer) Four :=
  heptadRepresentation.comp sourceQuotientEquiv.toMonoidHom

/-- The representation of the literal intrinsic source quotient is irreducible. -/
theorem sourceQuotientRepresentation_irreducible : IsIrreducible sourceQuotientRepresentation :=
  (irreducible_comp_surjective_iff sourceQuotientEquiv.toMonoidHom
    sourceQuotientEquiv.surjective heptadRepresentation).mpr heptadRepresentation_irreducible

end
end Sporadic.Mathieu.M23Geometry.ChapterHLocalActions
