module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.Construction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual

/-!
# The ordinary A₇ Thompson/Baumann marking and placement calculation

The ordinary block model gives compatible quotient and faithful permutation
coordinates for the actual action on W_K. The offender calculation marks
J(Tᵥ)⁺ by three disjoint transpositions, and the fixed vectors give
S⁺ = J(Tᵥ)⁺. Baumann heredity gives the Frattini normalizer comparison.
Relative normality of Lᵥ in Mᵥ, together with 13.6.5 and the solvable S₇
calculation, then identifies Lᵥ with O²(N_K(S)). The common fixed letter
gives both six-point placements. A lifted three-cycle supplies a Thompson
actor outside the two-core of the residual lift.

`source_calculation` assembles these conclusions in the same coordinates;
`source_replacement` applies them to `Construction.replacement`. Neither
the marking nor the residual identity is an input to these two theorems.
The earlier conditional transport interfaces are preserved below.

The genuine earlier inputs remain explicit: literal Y_z membership,
13.6.14's normalization, 13.6.20's Lᵥ ≤ K, 13.6.4's Baumann equality,
relative normality in Mᵥ, 13.6.5, and the local {2,3}/Sylow-three data.
The elementary W_K ≤ Tᵥ and two-reduced plus action come from the R₂
statement preceding 13.6.14. The equality [W_K,K] = [Z(O₂(K)),K] is the
identification of U_K in the opening of 13.6.22; its earlier module and
characteristic-normalizer producers are `qt-13-06-selection-modules` and
`qt-13-06-control-characteristic-normalizers`. No 13.6.16 premise is used.

The enclosing source assembly still discharges those earlier inputs and
uses the independent selection theorem to establish membership in Y_z.
The printed equality N_{KTᵥ}(S) = (Tᵥ ∩ K)Lᵥ is not used: its right side
lies in K, whereas its left side contains Tᵥ. The needed relative-normalizer
and residual statements are proved directly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, printed p.932 (PDF p.949).
-/

@[expose] public section
open Subgroup Equiv
open scoped commutatorElement
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement
variable {G : Type*} [Group G]

/-- K is contained in the literal actor defining the plus quotient. -/
theorem K_le_plusActor (K L T : Subgroup G) (v : G) : K ≤ plusActor K L T v :=
  (le_conjugateSpanBy K (Tv T v)).trans (le_sup_left.trans le_sup_left)

/-- Mapping the plus image retains the original restriction to its actor. -/
theorem actionImage_plus (K L T A : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7)) :
    actionImage (plusActor K L T v) (φ.comp (plusMk K L T z v hL hz)) A =
      (plusImage K L T z v hL hz A).map φ :=
  (map_map _ _ _).symm

variable [Finite G]

/-- The two placements and the actor witness follow from a marking of the
actual plus images, compatible on K with the supplied quotient coordinates.
The marking itself remains a separate source obligation. -/
theorem placements_and_actor_of_plus_marking
    (K L T S : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : Tv T v ≤ normalizer (K : Set G))
    (hS : S = ChapterB.baumann (Tv T v))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7))
    (hφ : ∀ k : K,
      φ (plusMk K L T z v hL hz ⟨k, K_le_plusActor K L T v k.property⟩) =
        (blockProjection K e k : Perm (Fin 7)))
    (hJ : (plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ =
      threeTranspositions)
    (hSJ : plusImage K L T z v hL hz S =
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))) :
    K ⊓ normalizer (S : Set G) ≤ ambientPreimage K e 6 ∧
      Tv T v ≤ normalizer (ambientPreimage K e 6 : Set G) ∧
      ∃ j ∈ Stellmacher.elementaryAbelianMaxJ (Tv T v),
        ∃ b ∈ replacement K e 6, ⁅j, b⁆ ∉ (replacement K e 6).pCoreIn 2 := by
  let H := plusActor K L T v
  let ρ := φ.comp (plusMk K L T z v hL hz)
  have hKH : K ≤ H := K_le_plusActor K L T v
  have hTH : Tv T v ≤ H := le_sup_right
  have hSH : S ≤ H := by
    rw [hS]
    exact inf_le_left.trans hTH
  have hρ : ∀ k : K, ρ ⟨k, hKH k.property⟩ = (blockProjection K e k : Perm (Fin 7)) := hφ
  have hJρ : actionImage H ρ (Stellmacher.elementaryAbelianMaxJ (Tv T v)) =
      threeTranspositions := by
    rw [actionImage_plus]
    exact hJ
  have hSρ : actionImage H ρ S = threeTranspositions := by
    rw [actionImage_plus, hSJ, hJ]
  exact ⟨normalizer_le_preimage_of_marking K H S hKH hSH e ρ hρ hSρ,
    normalizes_preimage_of_marking K H (Tv T v) hKH hTH hK e ρ hρ hJρ,
    exists_actor_of_marking K H (Tv T v) hKH e ρ hρ hJρ⟩

/-- Actual application to the constructed replacement, with its A₆ quotient
and a Thompson actor outside its two-core. Final source assembly must supply
the marking and the local normalizer-residual identity used here. -/
theorem replacement_of_plus_marking
    (K L T S : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : Tv T v ≤ normalizer (K : Set G))
    (hS : S = ChapterB.baumann (Tv T v))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7))
    (hφ : ∀ k : K,
      φ (plusMk K L T z v hL hz ⟨k, K_le_plusActor K L T v k.property⟩) =
        (blockProjection K e k : Perm (Fin 7)))
    (hJ : (plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ =
      threeTranspositions)
    (hSJ : plusImage K L T z v hL hz S =
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)))
    (hLv : Lv L v = (pResidual 2 (K ⊓ normalizer (S : Set G) : Subgroup G)).map
      (K ⊓ normalizer (S : Set G)).subtype)
    (hzL : ⁅zpowers z, Lv L v⁆ ≠ ⊥) :
    Lv L v ≤ replacement K e 6 ∧ replacement K e 6 ≤ K ∧
      Tv T v ≤ normalizer (replacement K e 6 : Set G) ∧
      ⁅zpowers z, replacement K e 6⁆ ≠ ⊥ ∧
      Nonempty ((replacement K e 6 ⧸ pCore 2 (replacement K e 6)) ≃*
        alternatingGroup (Fin 6)) ∧
      ∃ j ∈ Stellmacher.elementaryAbelianMaxJ (Tv T v),
        ∃ b ∈ replacement K e 6, ⁅j, b⁆ ∉ (replacement K e 6).pCoreIn 2 := by
  obtain ⟨hN, hT, hactor⟩ := placements_and_actor_of_plus_marking
    K L T S z v hL hz hK hS e φ hφ hJ hSJ
  obtain ⟨hLB, hBK, hTB, hzB, hB⟩ := replacement_spec K e 6 L T S z v hLv hN hT hzL
  exact ⟨hLB, hBK, hTB, hzB, hB, hactor⟩

/-- The ordinary A₇ calculation in one compatible set of coordinates.
The Thompson/Baumann marking, Frattini comparison, local residual identity,
both six-point placements and the nontrivial actor are all conclusions.
Only the earlier local and component-module facts listed in the overview
remain explicit; normality of Lᵥ is relative to Mᵥ. -/
theorem source_calculation
    (K L T M S : Subgroup G) (z v : G)
    (hblock : ChapterC.IsAlternatingBlock K 7)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hS : S = ChapterB.baumann (Tv T v))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hUK : ⁅WK K L T z v, K⁆ =
      ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆)
    (hLM : Lv L v ≤ Mv M v) (hLn : ((Lv L v).subgroupOf (Mv M v)).Normal)
    (h65 : Gv v ⊓ normalizer (S : Set G) ≤ Mv M v)
    (h23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card (plusImage K L T z v hL hz (Lv L v)) →
      p = 2 ∨ p = 3)
    (P3 : Sylow 3 (plusImage K L T z v hL hz (Lv L v))) (hP3 : Nat.card P3 = 3) :
    ∃ (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
      (φ : Gplus K L T z v hL hz →* Perm (Fin 7)), Function.Injective φ ∧
      (∀ k : K,
        φ (plusMk K L T z v hL hz ⟨k, K_le_plusActor K L T v k.property⟩) =
          (blockProjection K e k : Perm (Fin 7))) ∧
      (plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ =
        threeTranspositions ∧
      plusImage K L T z v hL hz S =
        plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)) ∧
      plusImage K L T z v hL hz (K ⊓ normalizer (S : Set G)) =
        plusImage K L T z v hL hz K ⊓
          normalizer (plusImage K L T z v hL hz S : Set _) ∧
      Lv L v = (pResidual 2 (K ⊓ normalizer (S : Set G) : Subgroup G)).map
        (K ⊓ normalizer (S : Set G)).subtype ∧
      K ⊓ normalizer (S : Set G) ≤ ambientPreimage K e 6 ∧
      Tv T v ≤ normalizer (ambientPreimage K e 6 : Set G) ∧
      ∃ j ∈ Stellmacher.elementaryAbelianMaxJ (Tv T v),
        ∃ b ∈ replacement K e 6, ⁅j, b⁆ ∉ (replacement K e 6).pCoreIn 2 := by
  obtain ⟨e, φ, hi, hc, hJ, hSJ⟩ := Marking.exists_ordinary_plus_marking
    K L T S z v hL hz hK hLK hY hS hWT hR hblock hUK
  have hnormalizer := LocalResidual.plus_normalizer_comparison
    K L T S z v hL hz hY hK hLK hS e φ hi hc
  have hresidual := LocalResidual.source_residual_eq
    K L T M S z v hblock hL hz hY hK hLK hS hLM hLn h65 e φ hi hc hJ hSJ h23 P3 hP3
  obtain ⟨hN, hT, hactor⟩ := placements_and_actor_of_plus_marking
    K L T S z v hL hz hK hS e φ hc hJ hSJ
  exact ⟨e, φ, hi, hc, hJ, hSJ, hnormalizer, hresidual, hN, hT, hactor⟩

/-- Apply the complete placement calculation to the actual residual lift.
This supplies every input of the independent Y_z selection calculation:
the residual identity, both placements and the literal Thompson actor.
It also records the constructed A₆ quotient and movement of z. -/
theorem source_replacement
    (K L T M S : Subgroup G) (z v : G)
    (hblock : ChapterC.IsAlternatingBlock K 7)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hS : S = ChapterB.baumann (Tv T v))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hUK : ⁅WK K L T z v, K⁆ =
      ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆)
    (hLM : Lv L v ≤ Mv M v) (hLn : ((Lv L v).subgroupOf (Mv M v)).Normal)
    (h65 : Gv v ⊓ normalizer (S : Set G) ≤ Mv M v)
    (h23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card (plusImage K L T z v hL hz (Lv L v)) →
      p = 2 ∨ p = 3)
    (P3 : Sylow 3 (plusImage K L T z v hL hz (Lv L v))) (hP3 : Nat.card P3 = 3)
    (hzL : ⁅zpowers z, Lv L v⁆ ≠ ⊥) :
    ∃ e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7),
      Lv L v = (pResidual 2 (K ⊓ normalizer (S : Set G) : Subgroup G)).map
        (K ⊓ normalizer (S : Set G)).subtype ∧
      K ⊓ normalizer (S : Set G) ≤ ambientPreimage K e 6 ∧
      Tv T v ≤ normalizer (ambientPreimage K e 6 : Set G) ∧
      Lv L v ≤ replacement K e 6 ∧ replacement K e 6 ≤ K ∧
      Tv T v ≤ normalizer (replacement K e 6 : Set G) ∧
      ⁅zpowers z, replacement K e 6⁆ ≠ ⊥ ∧
      Nonempty ((replacement K e 6 ⧸ pCore 2 (replacement K e 6)) ≃*
        alternatingGroup (Fin 6)) ∧
      ∃ j ∈ Stellmacher.elementaryAbelianMaxJ (Tv T v),
        ∃ b ∈ replacement K e 6, ⁅j, b⁆ ∉ (replacement K e 6).pCoreIn 2 := by
  obtain ⟨e, _, _, _, _, _, _, hresidual, hN, hT, hactor⟩ := source_calculation
    K L T M S z v hblock hL hz hY hK hLK hS hWT hR hUK hLM hLn h65 h23 P3 hP3
  obtain ⟨hLB, hBK, hTB, hzB, hB⟩ :=
    replacement_spec K e 6 L T S z v hresidual hN hT hzL
  exact ⟨e, hresidual, hN, hT, hLB, hBK, hTB, hzB, hB, hactor⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement
end
