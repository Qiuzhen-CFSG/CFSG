module

public import Theory.Representation.AlternatingCentralCoverSmallSixteen
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.DihedralInspection.Scalars

/-!
# Alternating-cover degree exclusions for the dihedral multiplicity action

Apply the degree-two and degree-three exclusions over F₁₆ to the literal
scalar refinement of conjugation on O₂(I)/U. A central-cover identification
of a quotient through which this action factors supplies the group input.
Nontriviality is measured on the original multiplicative quotient action.

The field marking, quotient identification, and nontriviality remain explicit
source inputs. These conditional applications do not identify the overgroup
or replace the simultaneous action on U.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Proposition 8.2.8(1), printed p.719 (PDF p.736), final dihedral case.
-/

public section
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups
open Subgroup
open scoped IsMulCommutative

variable {F G : Type*} [Field F] [Finite F] [Group G] [Finite G]
    (K I U : Subgroup G) [Group.IsPerfect K]
    [(U.subgroupOf (I.pCoreIn 2)).Normal]
    [IsMulCommutative (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))]
    [Module F (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)))]
    (e : (I ⧸ pCore 2 I) ≃* DihedralGroup 5)
    (hQI : K.pCoreIn 2 ≤ normalizer (I : Set G))
    (hKI : ⁅K, I⁆ ≤ K.pCoreIn 2) (hKU : K ≤ normalizer (U : Set G))
    (hUP : U ≤ I.pCoreIn 2)
    (hfull : I.pCoreIn 2 = ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ⊔ U)
    (hIC : I ≤ centralizer (U : Set G))
    (hPP : ⁅I.pCoreIn 2, I.pCoreIn 2⁆ ≤ U)
    (ζ : F) (hgen : Subring.closure ({ζ} : Set F) = ⊤)
    (x : (pResidual 2 I).map I.subtype)
    (hscalar : ∀ v, Additive.ofMul (pairResidualQuotientAction I U hIC x v) =
      ζ • Additive.ofMul v)

/-- The actual multiplicity action cannot factor nontrivially through any of
these alternating central covers in the indicated dimensions. The factor
kernel N can be O₂(K), or the exact multiplicity-action kernel. -/
theorem componentMultiplicityAction_alternatingCover_exclusion
    (hF : Nat.card F = 16) (N : Subgroup K) [N.Normal]
    (hN : N ≤ (componentMultiplicityAction K I U e hQI hKI hKU hUP hfull
      hIC hPP ζ hgen x hscalar).ker)
    (m : ℕ) (c : PerfectCentralCovering.Cover (K ⧸ N) (alternatingGroup (Fin m)))
    (hd : ((m = 6 ∨ m = 7 ∨ m = 8) ∧
      Module.finrank F (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))) = 2) ∨
      ((m = 7 ∨ m = 8) ∧
      Module.finrank F (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))) = 3))
    (hnontriv : ∃ (k : K) (v : I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)),
      componentCoreQuotientAction K I U hQI hKI hKU hUP hfull k v ≠ v) : False := by
  let α := componentMultiplicityAction K I U e hQI hKI hKU hUP hfull
    hIC hPP ζ hgen x hscalar
  let β := QuotientGroup.lift N α hN
  have hb : β = 1 :=
    Representation.AlternatingCentralCoverSmallSixteen.linearAction_eq_one m c β hF hd
  obtain ⟨k, v, hv⟩ := hnontriv
  have hk : α k = 1 := DFunLike.congr_fun hb (QuotientGroup.mk' N k)
  have hh := LinearEquiv.congr_fun hk (Additive.ofMul v)
  rw [show α k (Additive.ofMul v) = Additive.ofMul
    (componentCoreQuotientAction K I U hQI hKI hKU hUP hfull k v) from
      componentMultiplicityAction_apply K I U e hQI hKI hKU hUP hfull
        hIC hPP ζ hgen x hscalar k v] at hh
  exact hv (congrArg Additive.toMul hh)

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups
