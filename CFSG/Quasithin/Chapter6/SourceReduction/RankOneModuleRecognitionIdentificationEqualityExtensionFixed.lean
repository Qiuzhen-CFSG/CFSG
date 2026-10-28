module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionLayer
public import Theory.Representation.SL2FourNaturalBorelFixedLifting.Gaschutz

/-!
# Lifting the local-core fixed plane

The identity [Q,L]=V makes the L-action on Q/V trivial. Gaschütz lifts
a T∩L-fixed vector modulo V to an L-fixed vector. That vector vanishes
because C_T(L)=1, proving C_Q(T∩L)=Z_S on the original ambient subgroups.
This is the fixed-space input to the centralizer order bound.

Source: Aschbacher–Smith, proof of 6.2.13, printed p.687, using A.1.39.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

private def binaryAction {D Q : Type*} [Group D] [Group Q]
    [IsElementaryAbelian 2 Q] (β : D →* MulAut Q) :
    Representation (ZMod 2) D (Additive Q) where
  toFun a := (β a).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext v
    change β 1 v.toMul = v.toMul
    rw [map_one]
    rfl
  map_mul' a b := by
    ext v
    change β (a * b) v.toMul = β a (β b v.toMul)
    rw [map_mul]
    rfl

/-- Gaschütz lifts a Sylow-fixed element of the local core modulo V.
The lifted L-fixed element vanishes by C_T(L)=1. -/
theorem LocalAnalysis.equality_local_core_sylow_fixed
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G) =
      ZS (T : Subgroup G) L R := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let V := layer L R
  let : IsElementaryAbelian 2 Q :=
    A.equality_local_core_elementary h611 hnatural hz horder hTH hbranch
  have hQT : Q ≤ (T : Subgroup G) := by
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
    rw [← equality_sylow_centralizer_eq_core h611 hnatural]
    exact inf_le_left
  have hN : L ≤ normalizer (Q : Set G) :=
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  let β : L →* MulAut Q := Q.normalizerMonoidHom.comp (inclusion hN)
  let ρ := binaryAction β
  let N : Submodule (ZMod 2) (Additive Q) :=
    AddSubgroup.toZModSubmodule (n := 2) (V.subgroupOf Q).toAddSubgroup
  have hcomm := A.equality_local_core_commutator h611 hnatural hz horder hTH hbranch
  change ⁅Q, L⁆ = V at hcomm
  have hd (l : L) (q : Additive Q) : ρ l q - q ∈ N := by
    change ((β l) q.toMul / q.toMul : Q) ∈ V.subgroupOf Q
    rw [div_eq_mul_inv]
    change (l : G) * (q.toMul : G) * (l : G)⁻¹ * (q.toMul : G)⁻¹ ∈ V
    rw [← hcomm, commutator_comm Q L]
    exact commutator_mem_commutator l.property q.toMul.property
  obtain ⟨S, hS⟩ := NormalSylowQuotientAction.intersection_sylow T L h611.sylow_normalizes_L
  have hSmap : (S : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
    rw [hS, subgroupOf_map_subtype]
  apply le_antisymm
  · intro q hq
    let y : Additive Q := Additive.ofMul ⟨q, hq.1⟩
    have hy : y ∈ Representation.BinaryOffender.fixedSpace ρ (S : Subgroup L) := by
      intro s
      apply Additive.toMul.injective
      apply Subtype.ext
      change (s.val : G) * q * (s.val : G)⁻¹ = q
      rw [hq.2 s.val ((show (s.val : G) ∈ (T : Subgroup G) ⊓ L by
        rw [← hSmap]; exact mem_map_of_mem L.subtype s.property)), mul_inv_cancel_right]
    obtain ⟨w, hw, hn⟩ := Representation.SL2FourNaturalBorelFixedLifting.exists_fixed_lift
      ρ N hd S y hy
    have hwC : (w.toMul : G) ∈ centralizer (L : Set G) := by
      intro l hl
      have he := congrArg (fun x : Additive Q => (x.toMul : G)) (hw ⟨l, hl⟩)
      exact mul_inv_eq_iff_eq_mul.mp he
    have hw1 : (w.toMul : G) = 1 := by
      have hh : (w.toMul : G) ∈ (T : Subgroup G) ⊓ centralizer (L : Set G) :=
        ⟨hQT w.toMul.property, hwC⟩
      rwa [hnatural.2.2.1, mem_bot] at hh
    have hw0 : w = 0 := Additive.toMul.injective (Subtype.ext hw1)
    rw [hw0, sub_zero] at hn
    exact ⟨hn, hq.2⟩
  · exact inf_le_inf_right _ ((h611.layer_le_V).trans (reduced_le_core h611.V_mem))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
