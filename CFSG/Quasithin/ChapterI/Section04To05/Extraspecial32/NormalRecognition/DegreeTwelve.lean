module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.Interfaces
public import Mathlib.Algebra.Group.Action.TransferInstance

/-!
# The final degree-twelve coset action

Given the actual subgroups at the end of Aschbacher's construction, the map
`mL ↦ mzM` embeds `M/L` in the complement of the base coset in `G/M`.
The two sets have eleven points, so the map is a bijection. Its equivariance
lifts four-transitivity to five-transitivity. The order 95040 then makes the
transporter of every ordered five-tuple unique; faithfulness follows too.

The source order alternatives and the subgroup configuration remain explicit
inputs. This module does not claim to have constructed either from the local
hypotheses. `nonempty_action_of_sourceGeometry` connects both pending source
branches to the exact `DegreeTwelveAction` required by normal recognition.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 4.3, 4.10 and 4.11. The cardinality argument here
establishes the same coset coverage as 4.11 without separately constructing
the set `M ∪ MzM` as a subgroup.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve

open Subgroup MulAction

variable {G : Type*} [Group G] {z : G}

private theorem local_stabilizer (b : ElevenSubgroupData z) :
    MulAction.stabilizer b.M (z : G ⧸ b.M) = b.L.subgroupOf b.M := by
  ext m
  change ((m : G) * z : G ⧸ b.M) = (z : G ⧸ b.M) ↔ (m : G) ∈ b.L
  rw [← b.intersection]
  simp only [mem_inf, m.property, true_and, mem_map_equiv]
  change ((m : G) * z : G ⧸ b.M) = (z : G ⧸ b.M) ↔ z⁻¹ * (m : G) * z ∈ b.M
  rw [eq_comm, QuotientGroup.eq]
  rw [mul_assoc]

private def cosetMap (b : ElevenSubgroupData z) :
    (b.M ⧸ b.L.subgroupOf b.M) → (G ⧸ b.M) := fun q =>
  Quotient.liftOn' q (fun m : b.M => m • (z : G ⧸ b.M)) (by
    intro m n hmn
    have hs : (m⁻¹ * n) • (z : G ⧸ b.M) = (z : G ⧸ b.M) := by
      change m⁻¹ * n ∈ MulAction.stabilizer b.M (z : G ⧸ b.M)
      rw [local_stabilizer]
      exact QuotientGroup.leftRel_apply.mp hmn
    calc
      m • (z : G ⧸ b.M) = m • ((m⁻¹ * n) • (z : G ⧸ b.M)) :=
        congrArg (m • ·) hs.symm
      _ = n • (z : G ⧸ b.M) := by rw [← mul_smul, mul_inv_cancel_left])

private theorem cosetMap_injective (b : ElevenSubgroupData z) : Function.Injective (cosetMap b) := by
  intro q r
  induction q using Quotient.inductionOn' with | h m =>
    induction r using Quotient.inductionOn' with | h n =>
      intro he
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply, ← local_stabilizer b]
      change (m⁻¹ * n) • (z : G ⧸ b.M) = (z : G ⧸ b.M)
      change m • (z : G ⧸ b.M) = n • (z : G ⧸ b.M) at he
      rw [mul_smul, ← he, inv_smul_smul]

private theorem cosetMap_ne_base (b : ElevenSubgroupData z) (q : b.M ⧸ b.L.subgroupOf b.M) :
    cosetMap b q ≠ ((1 : G) : G ⧸ b.M) := by
  induction q using Quotient.inductionOn' with | h m =>
    intro he
    change (((m : G) * z : G) : G ⧸ b.M) = ((1 : G) : G ⧸ b.M) at he
    have hm : (m : G) * z ∈ b.M := by
      simpa only [QuotientGroup.eq, inv_one, one_mul] using he.symm
    exact b.z_not_mem ((b.M.mul_mem_cancel_left m.property).mp hm)

private def stabilizerHom (b : ElevenSubgroupData z) :
    b.M →* MulAction.stabilizer G ((1 : G) : G ⧸ b.M) :=
  (MulEquiv.subgroupCongr (MulAction.stabilizer_quotient b.M).symm).toMonoidHom

private def puncturedCosetMap (b : ElevenSubgroupData z) :
    (b.M ⧸ b.L.subgroupOf b.M) →ₑ[stabilizerHom b]
      SubMulAction.ofStabilizer G ((1 : G) : G ⧸ b.M) where
  toFun q := ⟨cosetMap b q, cosetMap_ne_base b q⟩
  map_smul' m q := by
    apply Subtype.ext
    induction q using Quotient.inductionOn' with | h n =>
      change (m * n) • (z : G ⧸ b.M) = m • n • (z : G ⧸ b.M)
      exact mul_smul _ _ _

/-- The eleven-point subgroup has twelve left cosets in the ambient group. -/
public theorem ElevenSubgroupData.quotient_card (b : ElevenSubgroupData z) (hG : Nat.card G = 95040) :
    Nat.card (G ⧸ b.M) = 12 := by
  have he := b.M.index_mul_card
  rw [b.card_M, hG] at he
  change b.M.index = 12
  omega

private theorem local_quotient_card (b : ElevenSubgroupData z) :
    Nat.card (b.M ⧸ b.L.subgroupOf b.M) = 11 := by
  have he := (b.L.subgroupOf b.M).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe b.le).toEquiv, b.card_L, b.card_M] at he
  change (b.L.subgroupOf b.M).index = 11
  omega

variable [Finite G]

private theorem puncturedCosetMap_bijective (b : ElevenSubgroupData z) (hG : Nat.card G = 95040) :
    Function.Bijective (puncturedCosetMap b) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨fun x y he => cosetMap_injective b (congrArg Subtype.val he), ?_⟩
  rw [local_quotient_card b, SubMulAction.nat_card_ofStabilizer_eq, ElevenSubgroupData.quotient_card b hG]

/-- The action on the literal cosets of `M` is five-transitive: the map
`mL ↦ mzM` identifies its point stabilizer action with the four-transitive
action on `M/L`. -/
public theorem ElevenSubgroupData.quotient_five_transitive (b : ElevenSubgroupData z) (hG : Nat.card G = 95040) :
    MulAction.IsMultiplyPretransitive G (G ⧸ b.M) 5 := by
  let := SubMulAction.mulAction
    (SubMulAction.ofStabilizer G ((1 : G) : G ⧸ b.M))
  apply (SubMulAction.ofStabilizer.isMultiplyPretransitive
    (a := ((1 : G) : G ⧸ b.M))).mpr
  have ht : MulAction.IsMultiplyPretransitive b.M (b.M ⧸ b.L.subgroupOf b.M) 4 := b.transitive
  have hp : MulAction.IsMultiplyPretransitive
      (MulAction.stabilizer G ((1 : G) : G ⧸ b.M))
      (SubMulAction.ofStabilizer G ((1 : G) : G ⧸ b.M)) 4 :=
    MulAction.IsPretransitive.of_embedding (f := puncturedCosetMap b)
      (puncturedCosetMap_bijective b hG).surjective
  exact hp

private noncomputable abbrev finAction (b : ElevenSubgroupData z) (hG : Nat.card G = 95040) :
    MulAction G (Fin 12) :=
  (Finite.equivFinOfCardEq (ElevenSubgroupData.quotient_card b hG)).symm.mulAction G

private theorem fin_transitive (b : ElevenSubgroupData z) (hG : Nat.card G = 95040) :
    letI := finAction b hG
    MulAction.IsMultiplyPretransitive G (Fin 12) 5 := by
  let e := Finite.equivFinOfCardEq (ElevenSubgroupData.quotient_card b hG)
  let := finAction b hG
  let f : (G ⧸ b.M) →[G] Fin 12 :=
    { toFun := e
      map_smul' := by
        intro g x
        change e (g • x) = e (g • e.symm (e x))
        rw [e.symm_apply_apply] }
  let := ElevenSubgroupData.quotient_five_transitive b hG
  exact MulAction.IsPretransitive.of_embedding (f := f) e.surjective

/-- Relabel the actual coset action by `Fin 12`. The equality between the
group order and the number of ordered five-tuples makes every transporter
unique and also proves faithfulness. -/
public theorem ElevenSubgroupData.nonempty_action_of_card (b : ElevenSubgroupData z) (hG : Nat.card G = 95040) :
    Nonempty (DegreeTwelveAction G) := by
  let := finAction b hG
  let := fin_transitive b hG
  let base : Fin 5 ↪ Fin 12 := Fin.castLEEmb (by decide)
  have hbij : Function.Bijective (fun g : G => g • base) := by
    apply (Nat.bijective_iff_surjective_and_card _).mpr
    refine ⟨fun y => MulAction.exists_smul_eq G base y, ?_⟩
    rw [hG, Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
      Fintype.card_fin]
    norm_num [Nat.descFactorial]
  have hsharp := Theory.GroupTheory.MulAction.isSharplyMultiplyPretransitive_of_bijective_orbitMap
    base hbij
  have hfaith : FaithfulSMul G (Fin 12) := by
    constructor
    intro a c he
    apply hbij.injective
    apply Function.Embedding.ext
    intro i
    exact he (base i)
  exact ⟨⟨finAction b hG, hfaith, hsharp⟩⟩

omit [Finite G] in
/-- The subgroup of order 7920 excludes the order-12096 alternative. -/
public theorem ElevenSubgroupData.card_of_order_cases (b : ElevenSubgroupData z)
    (hc : Nat.card G = 12096 ∨ Nat.card G = 95040) : Nat.card G = 95040 := by
  rcases hc with hc | hc
  · have hd := b.M.card_subgroup_dvd_card
    rw [b.card_M, hc] at hd
    norm_num at hd
  · exact hc

/-- Final assembly of the action once the local geometry/order calculation
and the eleven-point subgroup have both been constructed. The original local
hypotheses alone are not asserted to supply these two inputs here. -/
public theorem nonempty_action_of_sourceGeometry (h : Hypotheses z)
    (a : SourceGeometry h) (b : ElevenSubgroupData z) :
    Nonempty (DegreeTwelveAction G) :=
  b.nonempty_action_of_card (b.card_of_order_cases a.order_cases)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve
