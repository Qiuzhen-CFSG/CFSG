module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldCoreRecovery
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixScalarResidual
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointFixed

/-!
# The original Held source centralizer conclusions

The literal ordinary point configuration yields the actual exceptional block,
the full core splitting and C_G(U)=U. Since U≤Lt, the already calculated
fixed group U∩C_G(Lt)=Vt is therefore the entire ambient centralizer of Lt.
The full automorphism fixer identifies this with C_{C_G(t)}(B).

For the literal X=O²(O_{2,Z}(K)), the proved scalar fixed-zero calculation
then supplies C_G(LtX)=C_G(K) and the corrected factorization
C_G(Lt)=Vt C_G(LtX). No block, scalar, Frattini or centralizer callback
is retained. This is the centralizer paragraph of12.7.7, printed p.841;
the subsequent extraspecial construction and ambient Held recognition
remain separate source steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- All four ambient centralizer conclusions from the actual original
ordinary point component, with the original t,Lt,B,U,Vt throughout. -/
theorem original_tripleSix_held_centralizer_consequences
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hB : let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      IsComponent H ((conjugateSpanBy Lt H).subgroupOf H))
    (hcenter :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      centerIn (conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))) = tripleSixPoint D a t)
    (e :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    centralizer (K : Set G) = ⊥ ∧
      centralizer (Lt : Set G) = tripleSixPoint D a t ∧
      H ⊓ centralizer (B : Set G) = tripleSixPoint D a t ∧
      (T : Subgroup G) ⊓ centralizer (K : Set G) = ⊥ := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  have hCU := (original_tripleSix_held_core_recovery h structural D a t ht heven
    hB hcenter e).2.2.2.2
  have hfixed := tripleSixPoint_residual_fixed D a t ht heven
  have hle : centralizer (Lt : Set G) ≤ U :=
    (centralizer_le (tripleSixPointCentralizerResidual_commutator D a t ht heven).2).trans_eq hCU
  have hLt : centralizer (Lt : Set G) = tripleSixPoint D a t := by
    change U ⊓ centralizer (Lt : Set G) = tripleSixPoint D a t at hfixed
    exact (inf_eq_right.mpr hle).symm.trans hfixed
  have hK := original_tripleSix_held_component_centralizer_eq_bot
    h structural D a t ht heven hB hcenter e
  exact ⟨hK.1,hLt,(original_tripleSix_held_seed_centralizer D a t ht heven hcenter e).symm.trans hLt,
    hK.2⟩

/-- The exact original scalar residual supplies both the scalar-centralizer
identity and the source's corrected Vt factorization. -/
theorem original_tripleSix_held_scalar_centralizer_factorization
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hB : let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      IsComponent H ((conjugateSpanBy Lt H).subgroupOf H))
    (hcenter :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      centerIn (conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))) = tripleSixPoint D a t)
    (e :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
      (K ⊓ centralizer ({(t : G)} : Set G)).subtype
    let X := tripleSixScalarResidual K
    centralizer ((Lt ⊔ X : Subgroup G) : Set G) = centralizer (K : Set G) ∧
      centralizer (Lt : Set G) = tripleSixPoint D a t ⊔ centralizer ((Lt ⊔ X : Subgroup G) : Set G) := by
  let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
    (K ⊓ centralizer ({(t : G)} : Set G)).subtype
  let X := tripleSixScalarResidual K
  have hC := original_tripleSix_held_centralizer_consequences
    h structural D a t ht heven hB hcenter e
  have hzero : centralizer ((Lt ⊔ X : Subgroup G) : Set G) = ⊥ := by
    apply le_bot_iff.mp
    rw [←tripleSixScalarResidual_fixed_eq_bot D a]
    apply le_inf ?_ (centralizer_le (show X ≤ (Lt ⊔ X : Subgroup G) from le_sup_right))
    exact (centralizer_le (show Lt ≤ Lt ⊔ X from le_sup_left)).trans
      (hC.2.1.le.trans (tripleSixPoint_properties D a t ht).2.1)
  exact ⟨hzero.trans hC.1.symm,by rw [hzero,sup_bot_eq]; exact hC.2.1⟩

end CFSG.Quasithin.Chapter12.Section07
