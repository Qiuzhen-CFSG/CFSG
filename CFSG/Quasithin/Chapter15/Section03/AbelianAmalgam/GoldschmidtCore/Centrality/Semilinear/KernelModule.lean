module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.KernelMarking
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.DoubledAction
public import Mathlib.LinearAlgebra.Pi

/-!
# Intrinsic doubled natural module for the character kernel

The ambient elementary subgroup U lies in C_H(U)=N, hence in K and
O₂(K). Its intrinsic copy in K is normal. The compatible quotient
K/O₂(K)≃H/O₂(H) transports the marked natural coordinates, and the
explicit pair coordinates become the literal doubled natural action on
Fin 2 → Fin 3 → F₂. The representative formula is retained.

The first local two-core is transported through both actual subgroup
inclusions, so its ambient image is the original centralizer of V.
These are the precise intrinsic data used by the pushing-up consumer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the terminal module argument following 15.3.68, printed pp.1154–1155.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
variable {G : Type*} [Group G] [Finite G]

/-- Convert the literal doubled action to the intrinsic character kernel,
retaining both quotient and ambient subgroup maps. -/
theorem intrinsic_kernel_double (H B U : Subgroup G) [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hbad : ∃ q : ambientTwoCore H, ExternalQuotient.coreCharacter H B hHB q ≠ 1)
    (hUQ : U ≤ ambientTwoCore H)
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G))
    (m : (H ⧸ pCore 2 H) ≃* Matrix.PSL3Two.SL)
    (Φ : Additive U ≃ₗ[ZMod 2] (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (hΦ : ∀ h : H, quotientAction H B hHB h = 1 → ∀ u : Additive U,
      Φ (spanAction H U hHU h u) =
        (BinaryLinearThree.W (m (QuotientGroup.mk' _ h)) (Φ u).1,
         BinaryLinearThree.W (m (QuotientGroup.mk' _ h)) (Φ u).2)) :
    let K := characterKernel H B hHB
    let Uk := U.subgroupOf K
    ∃ hnormal : Uk.Normal, letI := hnormal
      IsElementaryAbelian 2 Uk ∧ Uk ≤ pCore 2 K ∧ Uk.map K.subtype = U ∧
      H ⊓ centralizer (Uk.map K.subtype : Set G) = (pCore 2 K).map K.subtype ∧
      ∃ eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL,
        (∀ k : K, eK (QuotientGroup.mk' _ k) =
          m (QuotientGroup.mk' (pCore 2 H) (inclusion (map_subtype_le _) k))) ∧
        ∃ eU : Uk ≃* Multiplicative (Fin 2 → BinaryLinearThree.Vector),
          ∀ (k : K) (u : Uk), (eU (MulAut.conjNormal k u)).toAdd =
            fun j => Matrix.mulVec (eK (QuotientGroup.mk' _ k)).val ((eU u).toAdd j) := by
  let K := characterKernel H B hHB
  let Uk := U.subgroupOf K
  have hUH : U ≤ H := hUQ.trans (pCoreIn_le 2 H)
  have hUN : U ≤ ambientTwoCore H ⊓ K := (le_inf hUH U.le_centralizer).trans hN.ge
  have hUK : U ≤ K := hUN.trans inf_le_right
  have hnormal : Uk.Normal := (normal_subgroupOf_iff_le_normalizer hUK).mpr
    ((map_subtype_le _).trans hHU)
  let := hnormal
  have hUk : IsElementaryAbelian 2 Uk := IsElementaryAbelian.subgroupOf hUK
  have hcore : Uk ≤ pCore 2 K := by
    rw [← localTwoCore_eq_pCore K]
    change U.subgroupOf K ≤ (ambientTwoCore K).subgroupOf K
    rw [ExternalQuotient.kernel_core]
    exact fun _ hu => hUN hu
  have hmap : Uk.map K.subtype = U := map_subgroupOf_eq_of_le hUK
  have hcent : H ⊓ centralizer (Uk.map K.subtype : Set G) = (pCore 2 K).map K.subtype := by
    rw [hmap,← hN]
    exact (ExternalQuotient.kernel_core H B hHB).symm
  let eK := (kernelCoreQuotientEquiv H B hHB hc hbad).trans m
  have heK (k : K) : eK (QuotientGroup.mk' _ k) =
      m (QuotientGroup.mk' (pCore 2 H) (inclusion (map_subtype_le _) k)) := by
    exact congrArg m (kernelCoreQuotientEquiv_mk H B hHB hc hbad k)
  let eU : Uk ≃* Multiplicative (Fin 2 → BinaryLinearThree.Vector) :=
    (subgroupOfEquivOfLe hUK).trans
      ((Φ.trans (LinearEquiv.finTwoArrow (ZMod 2) BinaryLinearThree.Vector).symm).toAddEquiv.toMultiplicative)
  refine ⟨hnormal,hUk,hcore,hmap,hcent,eK,heK,eU,?_⟩
  intro k u
  let h : H := inclusion (map_subtype_le _) k
  have hχ : quotientAction H B hHB h = 1 := by
    obtain ⟨h',hh,he⟩ := k.property
    exact (show h' = h from Subtype.ext he) ▸ hh
  let v : Additive U := Additive.ofMul (subgroupOfEquivOfLe hUK u)
  change (LinearEquiv.finTwoArrow (ZMod 2) BinaryLinearThree.Vector).symm
    (Φ (spanAction H U hHU h v)) =
      fun j => Matrix.mulVec (eK (QuotientGroup.mk' _ k)).val
        ((LinearEquiv.finTwoArrow (ZMod 2) BinaryLinearThree.Vector).symm (Φ v) j)
  rw [hΦ h hχ,heK]
  funext j
  fin_cases j <;> rfl

omit [Finite G] in
/-- Transport the core of the actual G₁∩K through its two ambient inclusions. -/
theorem nested_first_core (H B G₁ R : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) (hG₁ : G₁ ≤ H)
    (hR : ambientTwoCore G₁ ⊓ characterKernel H B hHB = R) :
    let K := characterKernel H B hHB
    let P := (G₁ ⊓ K).subgroupOf K
    ((pCore 2 P).map P.subtype).map K.subtype = R := by
  let K := characterKernel H B hHB
  let A := G₁ ⊓ K
  let P := A.subgroupOf K
  let e : P ≃* A := subgroupOfEquivOfLe inf_le_right
  have he : ((pCore 2 P).map P.subtype).map K.subtype = ambientTwoCore A := by
    change _ = (pCore 2 A).map A.subtype
    rw [← pCore_map_iso 2 e,map_map,map_map]
    rfl
  exact he.trans (ExternalQuotient.first_kernel_core H B G₁ R hHB hG₁ hR)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
