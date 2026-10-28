module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborTorus
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.OmegaFieldBound

/-!
# Torus control and the omega bound in both initial branches

The actual initial recognition constructs the beta marking and whole natural
residual section. The original edge then supplies a beta torus with the
exact field-minus-one order and the fixed subgroup of 9.4(ii). Corrected
5.12 bounds the original alpha omega-center by the same beta field order.
All three 9.4 preliminary clauses retain their literal subgroups and maps.

The catalogue, Chapter 8 reorientation and source 6.5 remain earlier inputs.
The strict-square comparison, alpha recognition and equal fields, and the
9.5--9.11 distance and field-two arguments remain with Chapter 9 assembly.
Source: DGS, Groups and Graphs (1985), 9.3--9.4, printed pp.142--143.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Both initial branches construct the torus, its exact fixed subgroup,
the full omega action and its field-order bound, with no alpha marking. -/
theorem reduced_critical_initial_alpha_bounds (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z, Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓ Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃* SL(2,F)))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')))
    (Mαsource : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a))) :
    let Γ := Reduction.reducedFamily L S₀
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
        (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧
        (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) = Nat.card F ∧
        (centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) = Nat.card F ∧
        (centralizer ((pResidual 2 (graphLocalGroup Γ beta)).map
          (graphLocalGroup Γ beta).subtype : Set (Reduction.G₀ L S₀))).relIndex (Z Γ a) = Nat.card F ∧
        NaturalResidualSection h beta eβ n ∧
        let Hβ := graphLocalGroup Γ beta
        let W := conjugateSpanBy (Q Γ a) (stabilizer Γ beta)
        let Z₀ := Z Γ a ⊓ (Subgroup.center W).map W.subtype
        ∃ Kβ : Subgroup (Reduction.G₀ L S₀),
          Kβ ≤ Hβ ⊓ stabilizer Γ a ∧ Odd (Nat.card Kβ) ∧ Nat.card Kβ = Nat.card F - 1 ∧
          Kβ ≤ (pResidual 2 Hβ).map Hβ.subtype ∧ Kβ ≤ W ∧
          (∀ k ∈ Kβ, k ≠ 1 →
            Z Γ a ⊓ centralizer ({k} : Set (Reduction.G₀ L S₀)) = Z₀) ∧
          let H := graphLocalGroup Γ a
          let q := QuotientGroup.mk' (pCore 2 H)
          ∃ R : Sylow 2 H,
            (R : Subgroup H).map H.subtype = (stabilizer Γ a ⊓ stabilizer Γ beta).pCoreIn 2 ∧
            let A := omegaCenterIn ((R : Subgroup H).map q)
            let Y := (A.comap q).map H.subtype
            Y ≤ W ∧ ⁅Z Γ a,Y⁆ ≤ Z₀ ∧ Z₀ ≤ centralizer (Y : Set (Reduction.G₀ L S₀)) ∧
              ⁅⁅Z Γ a,Y⁆,Y⁆ = ⊥ ∧ Z₀.relIndex (Z Γ a) = Nat.card F ∧
              Nat.card A ≤ Nat.card F := by
  let Γ := Reduction.reducedFamily L S₀
  let Hβ := graphLocalGroup Γ beta
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,hC,hC',hres⟩ :=
    reduced_critical_recognized_initial_section h hc hab hd hb hcomm htriv h8 hob Mα Mβ Mα'
  let := instF
  let := finF
  let := charF
  obtain ⟨Kβ,hKB,hKo,hKcard,hKR,hKW⟩ := reduced_linear_neighbor_torus h hab (hob a beta hab) hn hF eβ
  have hfixed : ∀ k ∈ Kβ, k ≠ 1 →
      Z Γ a ⊓ centralizer ({k} : Set (Reduction.G₀ L S₀)) =
        Z Γ a ⊓ (Subgroup.center (conjugateSpanBy (Q Γ a) (stabilizer Γ beta))).map
          (conjugateSpanBy (Q Γ a) (stabilizer Γ beta)).subtype := by
    intro k hk hne
    let kH : Hβ := ⟨k,(hKB hk).1⟩
    have ho : Odd (orderOf kH) := by
      simpa only [kH,Subgroup.orderOf_mk] using hKo.of_dvd_nat (_root_.orderOf_dvd_natCard (⟨k,hk⟩ : Kβ))
    exact reduced_natural_residual_neighbor_odd_fixed h hc hab hd hb hcomm
      (hob a beta hab) eβ hres kH ho (fun he => hne (congrArg Subtype.val he))
  obtain ⟨R,hR,hYW,hYZ,hZY,hquad,hindex,hbound,_⟩ :=
    reduced_natural_residual_omega_bound h hob hc hab hd hb hcomm Mα Mαsource hn hF eβ hres
  exact ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,hC,hC',
    reduced_natural_residual_neighbor_index h hc hab hd hb hcomm (hob a beta hab) hn hF eβ hres,
    hres,Kβ,hKB,hKo,hKcard,hKR,hKW,hfixed,R,hR,hYW,hYZ,hZY,hquad,hindex,hbound⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
