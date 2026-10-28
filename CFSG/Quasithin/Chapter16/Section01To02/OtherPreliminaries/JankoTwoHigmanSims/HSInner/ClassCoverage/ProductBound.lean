module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Distinct
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Upper bound for the full second HS involution centralizer

The finite certificates construct 15,400 distinct conjugates of the exact
marked word `t = s0 * s1 * s2 * s1 * s0 * s2` in the ATLAS carrier.
Orbit–stabilizer and the proved carrier order 44,352,000 therefore bound
its full centralizer by 2880. Neither orbit exhaustion nor any centralizer
structure, fusion, simplicity or perfectness premise is used.

This is the upper-bound input to the separate product-centralizer assembly,
whose product is `Z₂ × Aut(A₆)`.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3, Table 5.3m.
The untrusted certificate generator and its provenance are in
`ProductBound/source/`.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage
open Theory.GroupTheory Sporadic.LeechRelated.HS ProductBoundCertificate

/-- The full centralizer of the marked second HS involution has order at most 2880. -/
theorem t_centralizer_card_le_2880 :
    Nat.card (Subgroup.centralizer ({t} : Set Carrier)) ≤ 2880 := by
  let orbit := MulAction.orbit (ConjAct Carrier) t
  let f : Fin 15400 → orbit := fun i => ⟨conjugate (wordCode i), by
    refine ⟨ConjAct.toConjAct (evalWord Certificate.ambientLetter
      (word 19 (wordCode i)))⁻¹, ?_⟩
    simp only [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, inv_inv, conjugate]⟩
  have hf : Function.Injective f := by
    intro i j h
    exact conjugate_injective (congrArg Subtype.val h)
  have hsize : 15400 ≤ Nat.card orbit := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf
  have hstab : Nat.card (Subgroup.centralizer ({t} : Set Carrier)) =
      Nat.card (MulAction.stabilizer (ConjAct Carrier) t) := by
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    rfl
  have hcount : Nat.card orbit * Nat.card (Subgroup.centralizer ({t} : Set Carrier)) =
      Nat.card Carrier := by
    have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct Carrier) t)
    rw [Nat.card_prod, ← hstab] at h
    exact h
  have hprod := Nat.mul_le_mul_right
    (Nat.card (Subgroup.centralizer ({t} : Set Carrier))) hsize
  rw [hcount, NormalizerIndex.card_carrier] at hprod
  omega

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage
