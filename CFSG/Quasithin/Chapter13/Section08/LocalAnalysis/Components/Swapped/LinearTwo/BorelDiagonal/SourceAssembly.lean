module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.TerminalCartan
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.FullMarkedImages
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.CoveredAlternative

/-!
# Source assembly of the linear-two Borel and diagonal argument

Starting with the moving relative component and its actual PSL₂(2ⁿ)
isomorphism, we construct marked coordinates on K₀*, choose the Borel through
(T ∩ K₀)*, and lift it inside K₀. The universal solvable-overgroup conclusion
of 13.8.13 puts the lift in M. The theta identity 13.7.3(9) gives three-rank
two and excludes the ordinary A₆ quotient. The earlier natural covered action
then constructs both marked cubic quotients and their inverter. The Cartan
argument forces n = 2; theta identifies L₁ with O²(B₀). Finally the full
marked images coincide under the projection with kernel (Kᵗ)*.

The explicit earlier inputs are the index-two component normalizer and
prime-to-three residual from Chapter 1, the local model alternatives and
natural flag action from §§13.2,13.5 (including 13.2.2(3)), theta from
13.7.3(9), and the universally quantified solvable exclusion from 13.8.13.
None assumes a Borel, diagonal, Cartan power, or final parameter conclusion.
The theorem is the group-theoretic portion of 13.8.16(1); the module
classification and orthogonal contradiction are separate consumers.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
standing setup pp.946–947, proof p.952/PDF p.969, Notation 13.2.1 p.877.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceConclusion
variable {G : Type*} [Group G] [Finite G]

/-- Construct the Borel and the marked group-theoretic conclusions of the
linear-two branch. The standing local action is only requested after the
ordinary A₆ alternative has been excluded. All action and projection premises
of the intrinsic helper theorems are proved inside this assembly. -/
theorem exists_borel_diagonal
    (H K L T V V₁ V₃ M : Subgroup G) {t : G} (ht : t ∈ T)
    (hH : H = (K ⊔ K.conjBy t) ⊔ one L T V₁ ⊔ T)
    (hT : Chapter1.IsSylowIn 2 T H)
    (hcomponent : (K.subgroupOf H).IsCComponent)
    (hqs : IsQuasisimple (Source.starImage H K))
    (hi : (normalizer (K.subgroupOf H : Set H)).index = 2)
    (htn : t ∉ normalizer (K : Set G))
    {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    (hres : (primeToResidual 3 H).map H.subtype = K ⊔ K.conjBy t)
    (htheta : one L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (hq : IsPGroup 3 (one L T V₁ ⧸ pCore 2 (one L T V₁)))
    (hne : one L T V₁ ≠ ⊥)
    [Group.IsSolvable (one L T V₁ ⊔ T : Subgroup G)]
    (hHV₁ : H ≤ normalizer (V₁ : Set G))
    (hML : M ≤ normalizer (L : Set G))
    (hex : ∀ J : Subgroup G, one L T V₁ ⊔ T ≤ J →
      J ≤ normalizer (V₁ : Set G) → Group.IsSolvable J → J ≤ M)
    (hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (ha6 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (one L T V₁ ⧸ pCore 2 (one L T V₁)) = 3)
    (hnatural : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
      Nonempty (LocalAction.NaturalSetup L T V V₁ V₃))
    (hfactor : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
      one L T V₁ = plus L T V₁ ⊔ zero L) :
    ∃ (hK : K ⊔ K.conjBy t ≤ H) (hTH : T ≤ H)
      (e : Source.starImage H (K ⊔ K.conjBy t) ≃*
        Source.starImage H K × Source.starImage H K)
      (S : Sylow 2 (Source.starImage H (K ⊔ K.conjBy t))),
      let Kstar := Source.starImage H (K ⊔ K.conjBy t)
      let Bstar := SourceTorus.chosenStarBorel H (K ⊔ K.conjBy t) S
      let B₀ := SourceTorus.chosenLift H (K ⊔ K.conjBy t) hK S
      let C := SourceActions.CommonTorus H (K ⊔ K.conjBy t) e S
      let Z := SourceActions.D₀ H (K ⊔ K.conjBy t) hK e S hn hmodel L
      let P := SourceActions.Dplus H (K ⊔ K.conjBy t) hK e S hn hmodel L T V₁
      let π := factorProjection H (K ⊔ K.conjBy t) e
      (∀ a b, (e.symm (a, b) : Source.Hstar H) = (a : Source.Hstar H) *
        (QuotientGroup.mk' (pCore 2 H) ⟨t, hTH ht⟩ * b *
          (QuotientGroup.mk' (pCore 2 H) ⟨t, hTH ht⟩)⁻¹)) ∧
      (S : Subgroup Kstar).map Kstar.subtype = Source.starImage H (T ⊓ (K ⊔ K.conjBy t)) ∧
      Source.starImage H (T ⊓ (K ⊔ K.conjBy t)) ≤ Bstar ∧
      Source.starImage H B₀ = Bstar ∧ Group.IsSolvable B₀ ∧
      one L T V₁ ≤ B₀ ∧ B₀ ≤ M ∧ one L T V₁ ⊔ T ≤ normalizer (B₀ : Set G) ∧
      Even n ∧ primeRank 3 B₀ = 2 ∧ primeRank 3 (one L T V₁) = 2 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      (∃ a : ℕ, 2 ^ n - 1 = 3 ^ a) ∧ n = 2 ∧ one L T V₁ = residual B₀ ∧
      zero L ≤ one L T V₁ ∧ plus L T V₁ ≤ one L T V₁ ∧
      Nat.card (zero L ⧸ pCore 2 (zero L)) = 3 ∧
      Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3 ∧
      Function.Injective (fun x : Z => (x : C × C).1) ∧
      Function.Injective (fun x : Z => (x : C × C).2) ∧
      Function.Injective (fun x : P => (x : C × C).1) ∧
      Function.Injective (fun x : P => (x : C × C).2) ∧
      Z.map (MonoidHom.fst C C) = P.map (MonoidHom.fst C C) ∧
      Z.map (MonoidHom.snd C C) = P.map (MonoidHom.snd C C) ∧
      π.ker = (Source.starImage H (K.conjBy t)).subgroupOf Kstar ∧
      ((Source.starImage H (zero L)).subgroupOf Kstar).map π =
        ((Source.starImage H (plus L T V₁)).subgroupOf Kstar).map π := by
  have hK : K ⊔ K.conjBy t ≤ H := by rw [hH]; exact le_sup_left.trans le_sup_left
  have hLH : one L T V₁ ≤ H := by rw [hH]; exact le_sup_right.trans le_sup_left
  have hTH : T ≤ H := by rw [hH]; exact le_sup_right
  have hKH : K ≤ H := le_sup_left.trans hK
  have hAH : one L T V₁ ⊔ T ≤ H := sup_le hLH hTH
  have hperfect : IsPPerfect 2 (one L T V₁) := residual_isPPerfect _
  let _ : ((K ⊔ K.conjBy t).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer
      (SourceActions.normalizes_orbit H K hKH hi (hTH ht) htn)
  obtain ⟨e₀, he₀⟩ := exists_moving_star_coordinates H K hKH hcomponent hqs (hTH ht) htn hmodel
  let e := e₀.symm
  obtain ⟨S, hS, hT₀, hstar, hsol, hLB, hBM, hnorm, heven, hBrank, hLrank⟩ :=
    exists_source_borel_even_rank H (K ⊔ K.conjBy t) (one L T V₁) T
      (normalizer (V₁ : Set G)) M hK hLH hT e hn hmodel hperfect hq hne hres htheta
      (hK.trans hHV₁) (hAH.trans hHV₁) hex
  have hcover := covered_quotient_of_threeRank_two L (one L T V₁) hmodels ha6 hLrank
  obtain ⟨d⟩ := hnatural hcover
  have hfactor' := hfactor hcover
  have hTB := le_sup_right.trans hnorm
  have hBV : SourceTorus.chosenLift H (K ⊔ K.conjBy t) hK S ≤ normalizer (V₁ : Set G) :=
    (borelLift_le H (K ⊔ K.conjBy t) hK _).trans (hK.trans hHV₁)
  obtain ⟨hpower, hn2⟩ := parameter_two H K T hTH ht hK hi htn e he₀ S hn hmodel
    d hfactor' hLB hTB heven (hBM.trans hML) hBV
  have hmodel4 : ClassicalGroup.IsPSL (Source.starImage H K) 2 4 := by simpa [hn2] using hmodel
  have hresidual := SourceTorus.marked_eq_residual_at_four H (K ⊔ K.conjBy t) hK e S M
    (one L T V₁) hLB hBM hperfect htheta hmodel4
  obtain ⟨hz₁, hz₂, hp₁, hp₂, hf, hs⟩ := marked_diagonals H K T hTH ht hK hi htn e he₀
    S hn hmodel d hfactor' hLB hTB
  refine ⟨hK, hTH, e, S, he₀, hS, hT₀, hstar, hsol, hLB, hBM, hnorm,
    heven, hBrank, hLrank, hcover, hpower, hn2, hresidual,
    LocalAction.zero_le_one_of_factorization L T V₁ hfactor',
    plus_le_one L T V₁ d.line_stable, d.zero_core_card, d.plus_core_card hfactor',
    hz₁, hz₂, hp₁, hp₂, hf, hs, ?_, ?_⟩
  · exact factorProjection_kernel H K T hTH ht hK e he₀
  · exact marked_full_images H K T hTH ht hK hi htn e he₀ S hmodel4 d hfactor' hLB hTB hresidual

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceConclusion
end
