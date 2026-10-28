module
public import Theory.GroupAction.CentralElementaryQuotientFaithfulness
public import Theory.Representation.Suzuki.MinimalDegree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiLocalKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearResidualLayer

/-!
# The faithful literal Suzuki center layer, including the binary field

Construct conjugation on the elementary quotient V_beta/Z_beta and
pull it back through the original quotient marking. The common Sylow
and neighboring-center inclusion force Z_beta to be fixed by the whole
starred endpoint. The proved full-kernel calculation bounds the kernel
on V_beta by its two-core. The central-section automorphism argument
therefore makes the descended action faithful.

The degree bound now applies to this actual representation and proves
|V_beta/Z_beta| >= q^4. For q = 2 the prime-five divisor of |Sz(2)| gives
the four-dimensional bound directly. No faithfulness, nontriviality,
representation witness, or geometric order bound is an input.

The common Sylow, center inclusion and commutator bound are retained
earlier (12.1) inputs. The Suzuki marking is the still separate (12.5)
selection conclusion. The q^4 upper bound, central-layer identification,
second-kernel quotient and remaining (12.6)--(12.9) conclusions are not
asserted by this theorem. Both quotient and actor maps are the original
ones from SourceLayers.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1), (12.5)--(12.6), printed pp.178,182--183, and (12.9)(c2), p.186.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original marked actor acts faithfully on its actual elementary center
quotient, whose order is at least q⁴, also for the binary Suzuki group. -/
theorem source_suzuki_faithful_center_layer (h : HypothesisF11 L S)
    (hb : 2 < b (reducedFamily L S)) (i : Bool) {m : ℕ}
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup m)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    let v := base F i
    let := V_elementary F (reduced_triple h).generate
      (fun w => (source_Z_Q_U (reduced_triple h) w).1) (reduced_kernel_sylow h) hb v
    let : ((Z F v).subgroupOf (V F v 1)).Normal := normal_of_isMulCommutative _
    ∃ ρ : Representation (ZMod 2)
      (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0)))
      (Additive (V F v 1 ⧸ (Z F v).subgroupOf (V F v 1))),
      Function.Injective ρ ∧
      (2 ^ (2 * m + 1)) ^ 4 ≤ Nat.card (V F v 1 ⧸ (Z F v).subgroupOf (V F v 1)) ∧
      ∀ x : L (if i then 1 else 0), ∀ y : V F v 1,
        (ρ (QuotientGroup.mk x) (Additive.ofMul (QuotientGroup.mk y))).toMul =
          QuotientGroup.mk ⟨(originalActor (L := L) (S := S) i x : G₀ L S) * y *
            (originalActor (L := L) (S := S) i x : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp (star_normalizes_span h i (originalActor (L := L) (S := S) i x).property)
              y).mp y.property⟩ := by
  let F := reducedFamily L S
  let v := base F i
  let A := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun w => (source_Z_Q_U (reduced_triple h) w).1
  let := V_elementary F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb v
  let : ((Z F v).subgroupOf (V F v 1)).Normal := normal_of_isMulCommutative _
  let : Finite (V F v 1) := Finite.of_injective
    (inclusion ((V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb v).trans
      (Q_le_stabilizer F v))) (inclusion_injective _)
  obtain ⟨σ,hσ⟩ := exists_center_layer_action F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb v A (star_le_stabilizer i) (star_core h i).le hcomm
  have hf : Function.Injective σ := central_quotient_conjugation_faithful A
    (V F v 1) (Z F v) (star_normalizes_span h i)
    (le_centralizer_iff.mp (source_center_centralizes_star_of_neighbor_inclusion h i hzy T hT))
    (source_suzuki_span_centralizer_le_core h i e) σ hσ
  let ρ := σ.comp (originalQuotient h i).toMonoidHom
  have hρ : Function.Injective ρ := hf.comp (originalQuotient h i).injective
  let τ := ρ.comp e.symm.toMonoidHom
  have hτ : Function.Injective τ := hρ.comp e.symm.injective
  have hd : 4 * (2 * m + 1) ≤ Module.finrank (ZMod 2)
      (Additive (V F v 1 ⧸ (Z F v).subgroupOf (V F v 1))) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hh := Representation.BinaryPrimeDegree.orderOf_le_finrank τ hτ
        (by decide : Nat.Prime 5) (by decide : 5 ≠ 2)
        (by rw [suzukiZero_card]; decide)
      simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_five,
        Nat.mul_zero, Nat.zero_add, Nat.mul_one] using hh
    · exact Representation.Suzuki.finrank_ge (by omega) τ hτ
  have hcard : (2 ^ (2 * m + 1)) ^ 4 ≤
      Nat.card (V F v 1 ⧸ (Z F v).subgroupOf (V F v 1)) := by
    change (2 ^ (2 * m + 1)) ^ 4 ≤
      Nat.card (Additive (V F v 1 ⧸ (Z F v).subgroupOf (V F v 1)))
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, ←pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    simpa only [Nat.mul_comm] using hd
  refine ⟨ρ,hρ,hcard,?_⟩
  intro x y
  exact hσ (originalActor (L := L) (S := S) i x) y

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
