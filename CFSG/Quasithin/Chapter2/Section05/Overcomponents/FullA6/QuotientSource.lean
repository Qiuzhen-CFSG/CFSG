module

public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6.FusionRows
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.A6QuotientSource

/-!
# The remaining full-A₆ overcomponent quotients

Apply the complete fixed-A₆ quotient census to the original component and
its actual involution. The original crossing mark is the product of the
central-core involution and the central A₆ involution. Intrinsic fusion in
PSL₅(2) and Sp₄(4) contradicts that mark's source nonfusion, leaving only
A₈ and the marked inner Higman–Sims row.

Source: Aschbacher–Smith 2.5.19(3)(4), printed pp.561–562, used with
2.5.25 on printed p.568, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6
open ComponentRefinement ComponentSelection
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Fusion screens the full fixed-A₆ catalogue to the A₈ and HS rows,
retaining the original t-action and actual fixed component. -/
theorem source_a8_or_hs_quotient
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (t zK : G) (ht : orderOf t = 2) (hzK : orderOf zK = 2)
    (htC : t ∈ twoCore H) (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hzKK : zK ∈ K) (hz : z = t * zK)
    (i : G) (hi : orderOf i = 2)
    (X : Subgroup (centralizer ({i} : Set G)))
    (hX : IsComponent (centralizer ({i} : Set G)) X)
    (a : MulAut X) (ha : orderOf a = 2)
    (hact : ∀ y : X, ((a y : centralizer ({i} : Set G)) : G) =
      t * ((y : centralizer ({i} : Set G)) : G) * t⁻¹)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eKB : K ≃* B) (eK : K ≃* alternatingGroup (Fin 6))
    (hKX : K ≤ X.map (centralizer ({i} : Set G)).subtype) :
    Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 8)) ∨
      (∃ e : (X ⧸ center X) ≃* Sporadic.LeechRelated.HS.Carrier,
        MulAut.congr e (quotientAut (center X) a) =
          MulAut.conj Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.t) := by
  have hm := source_a6_overcomponent_quotient c hG hempty hgen hb i hi X hX
    a ha B hB eKB eK
  rcases hm with hA8 | hPSL | hSp | hHS
  · exact Or.inl hA8
  · let E := B.map a.fixedSubgroup.subtype
    have hE : E ≤ a.fixedSubgroup := map_subtype_le _
    let eE : E ≃* alternatingGroup (Fin 6) :=
      (B.equivMapOfInjective a.fixedSubgroup.subtype a.fixedSubgroup.subtype_injective).symm.trans
        (eKB.symm.trans eK)
    exact (FusionRows.source_binary_row_false c hgen t zK ht hzK htC htZ hzKK hz
      i X hX a ha hact E hE eE hKX hPSL).elim
  · obtain ⟨F,hF,hFinite,hChar,hcard,e,hmark⟩ := hSp
    exact (FusionRows.source_symplectic_row_false c hgen t zK ht hzK htC htZ hzKK hz
      i X hX a hact hKX hcard e hmark).elim
  · exact Or.inr hHS

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6
