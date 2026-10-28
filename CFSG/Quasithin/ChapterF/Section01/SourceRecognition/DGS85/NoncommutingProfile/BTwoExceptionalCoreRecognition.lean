module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalBinary
public import Theory.GroupTheory.FixedFreeSixteen
public import Theory.GroupTheory.C4SquareSymmetricThreeSplit
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# The binary exceptional alpha core and its split local extension

For q_beta = 2, the previously proved field restriction and core orders
make Q_alpha a non-elementary sixteen with a fixed-point-free cubic.
Intrinsic recognition identifies this actual core with C₄ × C₄.
The original quotient kernel is self-centralizing and the local actor has
order 96. The normalizer of its constructed cubic complements that kernel;
the complement is identified with SL₂(k) by the original quotient map.

This supplies core recognition and splitting in the binary row of DGS
(10.9), printed p.163. Recognition of the whole marked amalgam and its
path parameters remain separate. The companion source module transports
the core and complement through the actual original endpoint inclusion.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local instance coreModelAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- The literal binary exceptional alpha core is the homocyclic four-square. -/
theorem BTwoCenterActionData.exceptional_binary_alpha_core_equiv
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (hK : Nat.card K = 2) :
    Nonempty (Q F v ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  let := finite_endpoints h
  let : Finite (Q F v) := Finite.of_injective
    (inclusion (Q_le_stabilizer F v)) (inclusion_injective _)
  have hk := c.exceptional_linear_alpha_field_binary h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD E
  have hcard := (c.exceptional_linear_core_orders h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD E).1
  rw [hk,hK] at hcard
  obtain ⟨a,_,_,_,hfree⟩ := c.exceptional_linear_cubic h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD
  exact Theory.GroupTheory.FixedFreeSixteen.c4_square (by norm_num at hcard ⊢; exact hcard)
    (c.coreConjugation a) hfree
    (c.exceptional_linear_core_not_elementary h hB hSyl hb hactor hcentral
      ht hne hcomm hnot eβ hD E)

/-- The constructed cubic normalizer splits the original alpha quotient map. -/
theorem BTwoCenterActionData.exceptional_binary_alpha_complement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (hK : Nat.card K = 2) :
    Nat.card c.actor = 96 ∧
      ∃ a : c.actor, orderOf a = 3 ∧
        c.quotient.ker.IsComplement' (normalizer (zpowers a : Set c.actor)) ∧
        ∃ e : normalizer (zpowers a : Set c.actor) ≃* SL(2,k),
          ∀ x, e x = c.quotient x := by
  let := finite_endpoints h
  let : Finite c.actor := Finite.of_injective (inclusion c.actor_le) (inclusion_injective _)
  obtain ⟨eQ⟩ := c.exceptional_binary_alpha_core_equiv h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD E hK
  let eker : c.quotient.ker ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :=
    ((MulEquiv.subgroupCongr c.kernel).trans (subgroupOfEquivOfLe c.core_le)).trans eQ
  have hkcard : Nat.card c.quotient.ker = 16 := by
    rw [Nat.card_congr eker.toEquiv,Nat.card_prod]
    norm_num
  have hk := c.exceptional_linear_alpha_field_binary h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD E
  have hcard : Nat.card c.actor = 96 := by
    have hh := c.quotient.ker.card_mul_index
    rw [index_ker,MonoidHom.range_eq_top.mpr c.onto,card_top,hkcard,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,hk] at hh
    norm_num at hh
    exact hh.symm
  have hself : centralizer (c.quotient.ker : Set c.actor) ≤ c.quotient.ker := by
    intro x hx
    rw [c.kernel]
    change (x : G) ∈ Q F v
    let xS : stabilizer F v := ⟨x,c.actor_le x.property⟩
    have hxC : xS ∈ centralizer (pCore 2 (stabilizer F v) : Set (stabilizer F v)) := by
      intro y hy
      have hyQ : (y : G) ∈ Q F v := mem_map_of_mem (stabilizer F v).subtype hy
      let yA : c.actor := ⟨y,c.core_le hyQ⟩
      have hyK : yA ∈ c.quotient.ker := c.kernel.symm ▸ hyQ
      apply Subtype.ext
      change (y : G) * (x : G) = (x : G) * (y : G)
      exact congrArg (fun z : c.actor => (z : G)) (hx yA hyK)
    exact mem_map_of_mem (stabilizer F v).subtype
      (source_vertex_core_selfCentralizing h v hxC)
  obtain ⟨a,ha,_,_,_⟩ := c.exceptional_linear_cubic h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD
  have hs := C4SquareExtension.cubic_normalizer_complement c.quotient.ker eker hcard hself a ha
  let e := hs.symm.QuotientMulEquiv.symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective c.quotient c.onto)
  exact ⟨hcard,a,ha,hs,e,fun _ => rfl⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
