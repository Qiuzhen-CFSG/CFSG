module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralizerFactors
public import Theory.Representation.SL2.OddMinimalNatural
public import Theory.SpecificGroups.SL2.CubicFixedVectors

/-!
# Natural constituents and cubic fixed points in the actual C/W

In the hypothetical reducible case of DGS85 (12.9), both nonzero
constituents have order q². Their irreducibility and the odd defining-field
degree 2n+1 identify both with the natural SL₂(k) action by actual
intertwining equivalences. Every element of order three consequently fixes
only zero on both sections and on the whole literal centralizer quotient.

The quotient is still C_(Q_m)(G_m^(3))/G_m^(2), with the existing
geometric span denominator and original endpoint conjugation formula.
All earlier source hypotheses are retained. This supplies the naturality
and cubic fixed-point step on E in printed pp.189--190; the subsequent
(5.17) application to Q_m/W and its contradiction remain separate.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The hypothetical two constituents have natural coordinates for the same field and action. -/
theorem source_suzuki_centralizer_natural_factors
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let A := star L S i
    let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
    let W := conjugateSpanBy (V F (base F (!i)) 1 ⊓ Q F x) (stabilizer F m)
    ∃ hAC : A ≤ normalizer (C : Set (G₀ L S)),
    ∃ hW : (W.subgroupOf C).Normal,
      letI := hW
      let E := C ⧸ W.subgroupOf C
      Nat.card k ^ 3 ≤ Nat.card E ∧
      Nat.card E ≤ Nat.card k ^ (4 : ℕ) ∧
      ∃ hCE : IsElementaryAbelian 2 E,
        letI := hCE
        ∃ ρ : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) →*
          MulAut E,
          (∀ t : A, ∀ c : C,
            ρ ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t)) (QuotientGroup.mk' (W.subgroupOf C) c) =
              QuotientGroup.mk' (W.subgroupOf C) ⟨(t : G₀ L S)*c*(t : G₀ L S)⁻¹,
                (mem_normalizer_iff.mp (hAC t.property) c).mp c.property⟩) ∧
          let τ : Representation (ZMod 2) SL(2,k) (Additive E) :=
            FrattiniAction.ofAutomorphismHom (ρ.comp e.symm.toMonoidHom)
          ∀ U : Subrepresentation τ, U ≠ ⊥ → U ≠ ⊤ →
            Nat.card (U.toSubmodule : Type _) = Nat.card k ^ (2 : ℕ) ∧
            Nat.card (Additive E ⧸ U.toSubmodule) = Nat.card k ^ (2 : ℕ) ∧
            Representation.SL2.BinarySmall.IsNatural U.toRepresentation ∧
            Representation.SL2.BinarySmall.IsNatural U.quotientRepresentation ∧
            ∀ g : SL(2,k), orderOf g = 3 → ∀ v : Additive E, τ g v = v → v = 0 := by
  let F := reducedFamily L S
  let m := base F i
  let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
  let W := conjugateSpanBy (V F (base F (!i)) 1 ⊓ Q F x) (stabilizer F m)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite C := Finite.of_injective (inclusion
    (show C ≤ stabilizer F m from inf_le_left.trans (Q_le_stabilizer F m))) (inclusion_injective _)
  obtain ⟨hAC,hW,hlo,hup,hCE,ρ,hρ,hfactors⟩ := source_suzuki_centralizer_two_factors
    h i hb3 hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
    hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  let _ := hW
  let _ := hCE
  let E := Additive (C ⧸ W.subgroupOf C)
  let τ := FrattiniAction.ofAutomorphismHom (ρ.comp e.symm.toMonoidHom)
  refine ⟨hAC,hW,hlo,hup,hCE,ρ,hρ,?_⟩
  dsimp only
  intro U hUb hUt
  obtain ⟨hcu,hcq,hi,hq⟩ := hfactors U hUb hUt
  let _ := hi
  let _ := hq
  change Nat.card (E ⧸ U.toSubmodule) = Nat.card k ^ (2 : ℕ) at hcq
  obtain ⟨hNU,hNQ,hfixed⟩ := Representation.SL2.natural_factors_and_cubic_fixed_of_card
    τ U (show Odd (2*n+1) from ⟨n,rfl⟩) (by omega) hfield hcu hcq
  exact ⟨hcu,hcq,hNU,hNQ,hfixed⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
