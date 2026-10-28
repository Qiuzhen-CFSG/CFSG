module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalCubic
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoResidualSeparation
public import Theory.Representation.SL2.CharacteristicTwoFrattini
public import Theory.Frattini.OmegaProducts

/-!
# Exceptional beta-field bounds and its literal Frattini quotient

In the exceptional linear branch the beta-core order and its exact
Frattini subgroup give |Q_beta/Phi(Q_beta)| = q_alpha² q_beta.
Characteristic two passes from the full stabilizer to the Sylow-generated
local group, whose core is the same actual Q_beta. Its faithful Frattini
action has size at least q_beta² for a nonbinary beta field. The small
fields satisfy the bound directly. Thus q_beta <= q_alpha²; the previously
constructed natural alpha layers then give q_beta = q_alpha or q_alpha².

This proves the beta-field estimate used in DGS (10.9) without first
assuming q_alpha = 2. It does not prove that alpha-field equality, the
exceptional parabolic recognition, or the path parameters. The companion
source module preserves the original endpoints and small-unitary rows.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(5.7), p.108, (10.7), pp.158--159, and proof of (10.9), p.163.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local instance boundAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

private theorem local_core_selfCentralizing (h : LocallyRankOneTriple P B) (m : Vertex F) :
    centralizer (pCore 2 (graphLocalGroup F m) : Set (graphLocalGroup F m)) ≤
      pCore 2 (graphLocalGroup F m) := by
  let := finite_endpoints h
  let A := graphLocalGroup F m
  let H := stabilizer F m
  have hc : A.pCoreIn 2 = Q F m := sylowGenerated_core _
  have hmem (x : A) : x ∈ pCore 2 A ↔ (x : G) ∈ Q F m := by
    rw [←hc]
    exact (mem_map_iff_mem (f := A.subtype) A.subtype_injective).symm
  intro x hx
  apply (hmem x).mpr
  let xH : H := ⟨x,sylowGenerated_le _ x.property⟩
  have hxH : xH ∈ centralizer (pCore 2 H : Set H) := by
    intro y hy
    have hyQ : (y : G) ∈ A.pCoreIn 2 := hc.symm ▸ mem_map_of_mem H.subtype hy
    obtain ⟨z,hz,he⟩ := hyQ
    apply Subtype.ext
    change (y : G) * (x : G) = (x : G) * (y : G)
    rw [←he]
    exact congrArg Subtype.val (hx z hz)
  exact mem_map_of_mem H.subtype ((source_vertex_core_selfCentralizing h m) hxH)

/-- The literal beta Frattini quotient has the order used in (10.9). -/
theorem BTwoCenterActionData.exceptional_beta_frattini_card
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ = Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    Nat.card (Q F m ⧸ frattini (Q F m)) = Nat.card k ^ 2 * Nat.card K := by
  let := finite_endpoints h
  let : Finite (Q F m) := Finite.of_injective
    (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  have hQ := (c.exceptional_linear_core_orders h hB hSyl hb hactor hcentral
    ht hne hcomm.le hnot eβ hD E).2
  have hPhi := (c.beta_core_frattini_eq h hB hSyl hb hactor hcentral ht hne hcomm).1
  have hPhic : Nat.card (frattini (Q F m)) = Nat.card k := by
    rw [←card_map_of_injective (f := (Q F m).subtype) (Q F m).subtype_injective,hPhi,
      c.central_middle_center_card h hB hSyl hb hactor hcentral E]
  have hquotient := card_eq_card_quotient_mul_card_subgroup (frattini (Q F m))
  rw [hQ,hPhic] at hquotient
  apply Nat.mul_right_cancel (Nat.card_pos : 0 < Nat.card k)
  calc
    Nat.card (Q F m ⧸ frattini (Q F m)) * Nat.card k =
      Nat.card k ^ 3 * Nat.card K := hquotient.symm
    _ = (Nat.card k ^ 2 * Nat.card K) * Nat.card k := by ring

/-- The faithful beta action bounds its field by the square of the alpha field. -/
theorem BTwoCenterActionData.exceptional_beta_field_bound
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ = Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    Nat.card K ≤ Nat.card k ^ 2 := by
  have hk : 1 < Nat.card k := by
    let := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  by_cases hK : Nat.card K ≤ 3
  · nlinarith
  let := finite_endpoints h
  let A := graphLocalGroup F m
  let : Finite A := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hc : A.pCoreIn 2 = Q F m := sylowGenerated_core _
  let a : pCore 2 A ≃* Q F m :=
    ((pCore 2 A).equivMapOfInjective A.subtype A.subtype_injective).trans
      (MulEquiv.subgroupCongr hc)
  let e := QuotientGroup.congr _ _ a (frattini_map_equiv a)
  have hl := Representation.SL2.characteristic_two_frattini_card_lower
    (local_core_selfCentralizing h m) eβ (by omega : 3 < Nat.card K)
  rw [Nat.card_congr e.toEquiv,
    c.exceptional_beta_frattini_card h hB hSyl hb hactor hcentral ht hne hcomm hnot eβ hD E] at hl
  rw [pow_two] at hl
  exact Nat.le_of_mul_le_mul_right hl Nat.card_pos

/-- The natural alpha copies leave just the first and second field powers. -/
theorem BTwoCenterActionData.exceptional_beta_field_alternatives
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ = Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    Nat.card K = Nat.card k ∨ Nat.card K = Nat.card k ^ 2 := by
  obtain ⟨n,hn,hpow⟩ := c.linear_core_field_power h hB hSyl hb hactor hcentral
    ht hne hcomm.le hnot eβ
  have hbound := c.exceptional_beta_field_bound h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD E
  have hk : 1 < Nat.card k := by
    let := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  rw [hpow] at hbound
  have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right hk).mp hbound
  interval_cases n <;> simp_all
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
