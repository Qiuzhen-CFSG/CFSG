module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.ThompsonOffender
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MSCentralOrbit

/-!
# Original nonbinary tensor input to MS93 natural-module recognition

The original outside group H and stabilizer R=T∩N_G(L) supply MS3.
Its central omega layer X=Ω₁(Z(O₂(H))) has centralizer exactly O₂(H),
and the elementary Thompson argument provides an offender for the literal
H/O₂(H) action. All normality, faithfulness and FF premises are discharged
from the original H/K construction and its specified Sp₄(4) quotient.
The subsequent identification of the whole commutator core is separate.

Source: Aschbacher--Smith9.3.6--10 and C.1.31--32;
MS93 (2.2)(vi), (3.2)(vi).
-/

public section
open Subgroup Theory.GroupTheory
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC.MSCentralOrbit
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The initial X-layer is a faithful FF module for the actual quotient H/O₂(H).
The displayed action retains the original element representatives. -/
theorem source_tensor_sp4_msFFModule
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H : Subgroup G)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hLH : L ≤ H) (hout : ¬ H ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H)
    (K : Subgroup H) (hK : K.IsCComponent)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.symplecticGroup (Fin 2) F)
    (hfit : generalizedFitting H = pCore 2 H)
    (hprod : ∀ g : H, ∃ k ∈ K,
      ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H), k * r = g) :
    let X := omegaCenterIn (pCore 2 H)
    ∃ ρ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive X),
      Function.Injective ρ ∧ IsFFModule ρ ∧
      ∀ (h : H) (x : Additive X),
        ((ρ (QuotientGroup.mk' (pCore 2 H) h) x).toMul : H) =
          h * (x.toMul : H) * h⁻¹ := by
  let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H)
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D hn H hRH hLH hout hs
  obtain ⟨_,hfaith,_⟩ :=
    source_tensor_sp4_msCentralOrbit D hn H hRH hLH hout hs K hK hF eK hfit hprod
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    simpa only [hfit] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := H))
  have hne : R ≠ ⊥ := by
    intro hr
    have hz : pCore 2 H = ⊥ := le_bot_iff.mp (hr ▸ hodd.twoCore_le)
    have ht : (⊤ : Subgroup H) ≤ ⊥ := by
      intro h _
      have hc : h ∈ centralizer (pCore 2 H : Set H) := by
        rw [hz]
        intro x hx
        have hx1 : x = 1 := hx
        simp only [hx1, one_mul, mul_one]
      exact hz ▸ hself hc
    exact hK.ne_bot (le_bot_iff.mp (le_top.trans ht))
  let X := omegaCenterIn (pCore 2 H)
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : q.ker = centralizer (X : Set H) :=
    (QuotientGroup.ker_mk' _).trans
      (centralOmega_centralizer R hodd.twoCore_le hself hfaith).symm
  let ρ := NormalElementaryQuotient.representation X q
    (QuotientGroup.mk'_surjective _) hk
  refine ⟨ρ, NormalElementaryQuotient.representation_injective X q
    (QuotientGroup.mk'_surjective _) hk, ?_, ?_⟩
  · exact centralOmega_isFFModule R hms hodd.isPGroup hne hodd.twoCore_le hself hfaith
      q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  · exact NormalElementaryQuotient.representation_apply X q
      (QuotientGroup.mk'_surjective _) hk

end CFSG.Quasithin.Chapter10
