module

public import Theory.GroupAction.FixedPointCentralizerCount
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaCharacters.Fusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaCharacters.RootCentralizers

/-!
# The three marked actor centralizers in the actual normalizer

The action of N(E) on the fifteen nonidentity vectors has the marked
involution centralizer as point stabilizer, of order 384. The original actors
`a`, `c`, and `bd` fix respectively 3, 3, and 1 of these vectors. Internal
fusion of the seventeen local classes gives their stabilizer intersections
of sizes 36, 32, and 48, independently of the unresolved order-four pair.
The transporter double count therefore gives centralizer orders 32, 36, and 8.

All actions and embeddings are the original marked maps. In particular,
no placement of the S4 actors inside an arbitrary A6 complement is needed.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 5–6, pp.9–11.
-/

open Subgroup
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy CaseII CaseII.Distribution
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

private def markedActor (i : Fin 3) : TwistedModel := ![a, c, b * d] i

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)

omit [Finite G] in
private theorem markedActor_eq (i : Fin 3) :
    normalizerFixedRepresentative D k (Fin.natAdd 6 i) =
      normalizerCentralizer D k (markedActor i) := by fin_cases i <;> rfl

include L in
private theorem intersection_card (i : Fin 3) :
    Nat.card {t : TwistedModel // IsConj (normalizerCentralizer D k t)
      (normalizerFixedRepresentative D k (Fin.natAdd 6 i))} = (![36, 32, 48] i : ℕ) := by
  classical
  obtain ⟨swap, hf⟩ := exists_normalizerInertiaFusion D k L
  have hconj (t : TwistedModel) :
      IsConj (normalizerCentralizer D k t)
        (normalizerFixedRepresentative D k (Fin.natAdd 6 i)) ↔
          normalizerInertiaFusionIndex swap (localClass t) = Fin.natAdd 6 i := by
    have ht := ((normalizerCentralizer D k).map_isConj (localClass_conjugate t)).trans
      (hf (localClass t))
    constructor
    · intro hr
      exact normalizerFixedRepresentative_distinct D k L
        (ConjClasses.mk_eq_mk_iff_isConj.mpr (ht.symm.trans hr))
    · intro hr
      rwa [hr] at ht
  rw [Nat.card_congr (Equiv.subtypeEquivRight hconj), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  let f : Fin 17 → ℕ := fun j => if normalizerInertiaFusionIndex swap j = Fin.natAdd 6 i then 1 else 0
  change (∑ t : TwistedModel, f (localClass t)) = _
  have hs := Fintype.sum_fiberwise' localClass f
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, localClass_card] at hs
  rw [← hs]
  have hc : ∀ (swap : Bool) (i : Fin 3),
      (∑ j : Fin 17, (![1, 1, 8, 6, 12, 24, 32, 32, 32, 32, 12, 24, 48, 24, 24, 24, 48] j : ℕ) *
        (if normalizerInertiaFusionIndex swap j = Fin.natAdd 6 i then 1 else 0)) =
          (![36, 32, 48] i : ℕ) := by decide +kernel
  exact hc swap i

omit [Finite G] in
private theorem centralizer_smul (t : TwistedModel) (v : BinaryFour) :
    normalizerCentralizer D k t • normalizerVector D k v =
      normalizerVector D k (twistedAction t.right v) := by
  apply Subtype.ext
  change CaseII.into D k t * CaseII.into D k (SemidirectProduct.inl v) *
    (CaseII.into D k t)⁻¹ = CaseII.into D k (SemidirectProduct.inl (twistedAction t.right v))
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  ext <;> simp [mul_comm]

include L in
private theorem orbit_eq :
    MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k) = {1}ᶜ := by
  apply eNormalizerPoint_orbit_eq_of_card
  obtain ⟨K, hK, ⟨eK⟩⟩ := L.normalizer_E
  rw [Nat.card_congr (hK.symm.QuotientMulEquiv.trans eK).toEquiv,
    nat_card_alternatingGroup, Nat.card_fin]
  decide

include L in
private theorem fixed_card (i : Fin 3) :
    Nat.card {v : MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k) //
      normalizerFixedRepresentative D k (Fin.natAdd 6 i) • v.val = v.val} =
        (![3, 3, 1] i : ℕ) := by
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun v : E D k => v ∈ MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k))
    (fun v : E D k => normalizerFixedRepresentative D k (Fin.natAdd 6 i) • v = v))]
  have he : Nat.card {v : E D k // v ∈ MulAction.orbit (normalizer (E D k : Set G))
      (eNormalizerPoint D k) ∧ normalizerFixedRepresentative D k (Fin.natAdd 6 i) • v = v} =
      Nat.card {v : BinaryFour // v ≠ 1 ∧ twistedAction (markedActor i).right v = v} := by
    apply Nat.card_congr
    apply Equiv.symm
    apply (normalizerVectorEquiv D k).toEquiv.subtypeEquiv
    intro v
    rw [orbit_eq D k L, markedActor_eq D k]
    change (v ≠ 1 ∧ twistedAction (markedActor i).right v = v) ↔
      (normalizerVector D k v ≠ 1 ∧
        normalizerCentralizer D k (markedActor i) • normalizerVector D k v = normalizerVector D k v)
    rw [centralizer_smul, (normalizerVector_bijective D k).1.eq_iff]
    rw [← map_one (normalizerVector D k)]
    constructor
    · rintro ⟨hv, hf⟩
      exact ⟨fun h => hv ((normalizerVector_bijective D k).1 h), hf⟩
    · rintro ⟨hv, hf⟩
      exact ⟨fun h => hv (congrArg (normalizerVector D k) h), hf⟩
  rw [he]
  have hc : ∀ i : Fin 3, Fintype.card {v : BinaryFour //
      v ≠ 1 ∧ twistedAction (markedActor i).right v = v} = (![3, 3, 1] i : ℕ) := by
    decide +kernel
  rw [Nat.card_eq_fintype_card]
  exact hc i

include L in
private theorem stabilizer_intersection_card (i : Fin 3) :
    Nat.card {h : MulAction.stabilizer (normalizer (E D k : Set G)) (eNormalizerPoint D k) //
      IsConj (h : normalizer (E D k : Set G))
        (normalizerFixedRepresentative D k (Fin.natAdd 6 i))} = (![36, 32, 48] i : ℕ) := by
  let e : TwistedModel ≃* MulAction.stabilizer (normalizer (E D k : Set G))
      (eNormalizerPoint D k) :=
    (MonoidHom.ofInjective (normalizerCentralizer_injective D k)).trans
      (MulEquiv.subgroupCongr ((normalizerCentralizer_range D k).trans
        (eNormalizerPoint_stabilizer D k).symm))
  rw [← intersection_card D k L i]
  apply Nat.card_congr
  exact (e.toEquiv.subtypeEquiv (fun _ => Iff.rfl)).symm

include L in
/-- The actual centralizers of the marked a, c, and bd in N(E) have orders 32, 36, and 8. -/
public theorem normalizerFixedCentralizer_card_actors (i : Fin 3) :
    Nat.card (centralizer ({normalizerFixedRepresentative D k (Fin.natAdd 6 i)} :
      Set (normalizer (E D k : Set G)))) = (![32, 36, 8] i : ℕ) := by
  have h := MulAction.centralizer_card_mul_conj_stabilizer (eNormalizerPoint D k)
    (normalizerFixedRepresentative D k (Fin.natAdd 6 i))
  rw [stabilizer_intersection_card D k L, eNormalizerPoint_stabilizer_card,
    fixed_card D k L] at h
  fin_cases i <;> norm_num at h ⊢ <;> omega

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
