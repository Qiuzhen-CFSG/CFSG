module
public import CFSG.Quasithin.ChapterB.Section02.Baumann.Basic
public import Stellmacher.CentralizerQuotientRepresentation

/-!
# Fixed codimensions for a marked centralizer quotient

The actual descended representation has precisely the ambient relative
centralizer as its fixed-vector group. Cardinalities identify the source
logarithmic codimension with binary linear codimension. The same exact
kernel identifies subgroup-image orders, transferring the absence of
strong offenders along any marked faithful action quotient.
Source: Aschbacher–Smith B.2.18(c), B.6.10 and E.2.3.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.BaumannArgument
variable {G D : Type*} [Group G] [Finite G] [Group D]

theorem fixedCodim_eq_centralizer_quotient
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (A : Subgroup G) :
    fixedCodim U A = BinaryOffender.fixedCodim
      (NormalElementaryQuotient.representation U q hq hker) (A.map q) := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hcV : Nat.card U = 2 ^ Module.finrank (ZMod 2) (Additive U) := by
    rw [← Nat.card_congr (Additive.toMul : Additive U ≃ U)]
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U))
  have hcC : Nat.card (U ⊓ centralizer (A : Set G) : Subgroup G) =
      2 ^ Module.finrank (ZMod 2) (BinaryOffender.fixedSpace ρ (A.map q)) := by
    rw [← Nat.card_congr (NormalElementaryQuotient.fixedSpaceEquiv U q hq hker A)]
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := BinaryOffender.fixedSpace ρ (A.map q)))
  unfold fixedCodim
  rw [hcV,hcC,Nat.log_pow (by decide : 1<2),Nat.log_pow (by decide : 1<2)]
  have hd := BinaryOffender.fixedCodim_add_finrank ρ (A.map q)
  dsimp only [ρ] at hcC hd ⊢
  omega

theorem noStrong_of_centralizer_quotient
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hno : ¬ BinaryOffender.IsStrongFFModule
      (NormalElementaryQuotient.representation U q hq hker))
    (R : Subgroup G) : NoStrongOffenders U R := by
  intro A hAR hAe hne
  let k : (G ⧸ centralizer (U : Set G)) →* D :=
    QuotientGroup.lift _ q hker.symm.le
  have hmap : (A.map (actionMap U)).map k = A.map q := by
    rw [map_map]
    rfl
  have hAq : IsElementaryAbelian 2 (A.map q) := hmap ▸ hAe.map k
  have hneq : A.map q ≠ ⊥ := by
    intro hh
    apply hne
    apply (map_eq_bot_iff A).mpr
    rw [actionMap_ker, ←hker]
    exact (map_eq_bot_iff A).mp hh
  have hc : Nat.card (A.map (actionMap U)) = Nat.card (A.map q) := by
    rw [←relIndex_ker,←relIndex_ker,actionMap_ker,hker]
  rw [hc,fixedCodim_eq_centralizer_quotient U q hq hker]
  by_contra hh
  exact hno ⟨A.map q,⟨hneq, hAq⟩, Nat.lt_of_not_ge hh⟩
end CFSG.Quasithin.ChapterB.BaumannArgument
