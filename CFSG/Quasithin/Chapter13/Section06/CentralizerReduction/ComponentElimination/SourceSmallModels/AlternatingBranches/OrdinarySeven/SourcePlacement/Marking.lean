module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.Construction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.Families
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.Baumann
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.OffenderImages
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison

/-!
# Ordinary A₇: the Thompson/Baumann marking and six-point placement

`exists_ordinary_plus_marking` constructs the actual faithful seven-point
action and quotient coordinates, and proves that J(Tᵥ)⁺ is the group of three
pair swaps and Baum(Tᵥ)⁺ = J(Tᵥ)⁺. The same chosen ordinary block model first
supplies the full W_K fixed-codimension comparison. Sylow localization of the
actual maximal elementary images then supplies the stable offender family.
Simultaneous conjugation preserves compatibility on every element of K.
The concrete fixed vectors prove the Baumann equality. Finally,
`ordinary_placements_and_actor` applies the transport lemmas to the literal
six-point preimage and its residual lift.

The earlier inputs are literal Y_z membership (including the source Sylow
placement), Tᵥ-normalization of K, Lᵥ ≤ K, S = Baum(Tᵥ), elementary abelian
W_K ≤ Tᵥ, the two-reduced plus action, and the source identification
[W_K,K] = [Z(O₂(K)),K]. The component-module and characteristic-normalizer
source producers retain these inputs. The intrinsic block commutator and its
natural coordinates are proved in `ComponentSplitting`; no additional Irr⁺,
splitting, fixed-codimension, family, or fixed-centralizer hypothesis remains.
No 13.6.16 premise is used. The fixed-vector argument also avoids the stronger
unique-offender premise of B.2.20.

The earlier conditional family interfaces remain available. The enclosing
13.6.22 assembly still owns the earlier-source discharge, the local identity
Lᵥ = O²(N_K(S)), and the replacement's membership in Y_z.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 13.6.22,
printed p.932 (PDF p.949), with B.2.9(1), B.2.20 and B.3.2(4).
-/

@[expose] public section
open Subgroup Equiv
open scoped commutatorElement
open Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking

variable {G : Type*} [Group G]

/-- Change quotient coordinates by the same permutation used for the action. -/
def conjugateQuotient (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (g : Perm (Fin 7)) :
    (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7) :=
  e.trans (MulAut.conjNormal g)

/-- The marking conjugation preserves compatibility on every original k. -/
theorem conjugate_compatible (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7))
    (hc : ∀ k : K, φ (plusMk K L T z v hL hz
      ⟨k, ComponentSelection.K_le_plusActor K L T v k.property⟩) =
        (blockProjection K e k : Perm (Fin 7))) (g : Perm (Fin 7)) (k : K) :
    ((MulAut.conj g).toMonoidHom.comp φ) (plusMk K L T z v hL hz
      ⟨k, ComponentSelection.K_le_plusActor K L T v k.property⟩) =
        (blockProjection K (conjugateQuotient K e g) k : Perm (Fin 7)) := by
  rw [MonoidHom.comp_apply, hc]
  rfl

/-- Derive the literal three-transposition marking from the stable-family
identification, allowing simultaneous conjugation of both coordinates. -/
theorem exists_marked_action_of_family
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7)) (hφ : Function.Injective φ)
    (hc : ∀ k : K, φ (plusMk K L T z v hL hz
      ⟨k, ComponentSelection.K_le_plusActor K L T v k.property⟩) =
        (blockProjection K e k : Perm (Fin 7)))
    (P : Set (Subgroup (Perm (Fin 7))))
    (hP : IsStable (BinaryPermutation.naturalRepresentation (Fin 7)) P)
    (R : Sylow 2 (Perm (Fin 7)))
    (hgen : (plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ =
      generatedBy P (R : Subgroup _)) :
    ∃ (e' : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
      (φ' : Gplus K L T z v hL hz →* Perm (Fin 7)), Function.Injective φ' ∧
      (∀ k : K, φ' (plusMk K L T z v hL hz
        ⟨k, ComponentSelection.K_le_plusActor K L T v k.property⟩) =
          (blockProjection K e' k : Perm (Fin 7))) ∧
      (plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ' =
        threeTranspositions := by
  obtain ⟨g, hg⟩ := exists_generatedBy_marking hP R
  refine ⟨conjugateQuotient K e g, (MulAut.conj g).toMonoidHom.comp φ,
    (MulAut.conj g).injective.comp hφ, conjugate_compatible K L T z v hL hz e φ hc g, ?_⟩
  rw [← map_map, hgen]
  exact hg

variable [Finite G]

/-- Actual application to the six-point placement and Thompson actor. The
remaining module/family obligations are independent of the residual lift. -/
theorem placements_of_family_and_fixed_centralizer
    (K L T S : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hS : S = ChapterB.baumann (Tv T v))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7)) (hφ : Function.Injective φ)
    (hc : ∀ k : K, φ (plusMk K L T z v hL hz
      ⟨k, ComponentSelection.K_le_plusActor K L T v k.property⟩) =
        (blockProjection K e k : Perm (Fin 7)))
    (P : Set (Subgroup (Perm (Fin 7))))
    (hP : IsStable (BinaryPermutation.naturalRepresentation (Fin 7)) P)
    (R : Sylow 2 (Perm (Fin 7)))
    (hgen : (plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ =
      generatedBy P (R : Subgroup _))
    (hfixed : plusImage K L T z v hL hz
      (Tv T v ⊓ centralizer
        (WK K L T z v ⊓ centralizer
          (Stellmacher.elementaryAbelianMaxJ (Tv T v) : Set G) : Set G)) ≤
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))) :
    ∃ e' : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7),
      K ⊓ normalizer (S : Set G) ≤ ambientPreimage K e' 6 ∧
      Tv T v ≤ normalizer (ambientPreimage K e' 6 : Set G) ∧
      ∃ j ∈ Stellmacher.elementaryAbelianMaxJ (Tv T v),
        ∃ b ∈ replacement K e' 6, ⁅j, b⁆ ∉ (replacement K e' 6).pCoreIn 2 := by
  obtain ⟨e', φ', _, hc', hJ⟩ := exists_marked_action_of_family
    K L T z v hL hz e φ hφ hc P hP R hgen
  have hSJ : plusImage K L T z v hL hz S =
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)) := by
    rw [hS]
    exact baumann_plus_eq_of_fixed_centralizer K L T z v hL hz hWT hfixed
  let H := plusActor K L T v
  let ρ := φ'.comp (plusMk K L T z v hL hz)
  have hKH : K ≤ H := ComponentSelection.K_le_plusActor K L T v
  have hTH : Tv T v ≤ H := le_sup_right
  have hSH : S ≤ H := by rw [hS]; exact inf_le_left.trans hTH
  have hJρ : actionImage H ρ (Stellmacher.elementaryAbelianMaxJ (Tv T v)) =
      threeTranspositions := by
    change ((Stellmacher.elementaryAbelianMaxJ (Tv T v)).subgroupOf H).map
      (φ'.comp (plusMk K L T z v hL hz)) = _
    rw [← map_map]
    exact hJ
  have hSρ : actionImage H ρ S = threeTranspositions := by
    change (S.subgroupOf H).map (φ'.comp (plusMk K L T z v hL hz)) = _
    rw [← map_map]
    change (plusImage K L T z v hL hz S).map φ' = _
    rw [hSJ, hJ]
  exact ⟨e', normalizer_le_preimage_of_marking K H S hKH hSH e' ρ hc' hSρ,
    normalizes_preimage_of_marking K H (Tv T v) hKH hTH hn e' ρ hc' hJρ,
    exists_actor_of_marking K H (Tv T v) hKH e' ρ hc' hJρ⟩

/-- Construct compatible quotient and permutation coordinates for the source
Thompson/Baumann marking. The earlier commutator identity is the literal
identification of U_K with [Z(O₂(K)),K]; the fixed-codimension comparison,
offender family and fixed-centralizer bound are all discharged here. -/
theorem exists_ordinary_plus_marking
    (K L T S : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hY : K ∈ Yz L T z v)
    (hS : S = ChapterB.baumann (Tv T v))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hblock : ChapterC.IsAlternatingBlock K 7)
    (hUK : ⁅WK K L T z v, K⁆ =
      ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆) :
    ∃ (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
      (φ : Gplus K L T z v hL hz →* Perm (Fin 7)), Function.Injective φ ∧
      (∀ k : K, φ (plusMk K L T z v hL hz
        ⟨k, ComponentSelection.K_le_plusActor K L T v k.property⟩) =
          (blockProjection K e k : Perm (Fin 7))) ∧
      (plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ =
        threeTranspositions ∧
      plusImage K L T z v hL hz S =
        plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)) := by
  obtain ⟨φ, hi, hAlt, hc, hcodim, hfixed⟩ :=
    ModuleComparison.ordinary_comparison_exists K L T z v hL hz hWT hn hLv hY hR hblock hUK
  obtain ⟨g, hg⟩ := plus_exists_conjugated_marking
    K L T z v hL hz hn hLv hY hWT φ hi hAlt hcodim
  have hg' : ((plusImage K L T z v hL hz
      (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ).map
        (MulAut.conj g).toMonoidHom = threeTranspositions := by
    rw [map_map]
    exact hg
  refine ⟨conjugateQuotient K (ordinaryQuotientEquiv K hblock) g,
    (MulAut.conj g).toMonoidHom.comp φ, (MulAut.conj g).injective.comp hi,
    conjugate_compatible K L T z v hL hz (ordinaryQuotientEquiv K hblock) φ hc g,
    hg, ?_⟩
  rw [hS]
  exact (hfixed g hg').2

/-- Apply the proved ordinary-block marking to the literal six-point preimage
and residual lift. Only the genuine earlier source inputs remain. -/
theorem ordinary_placements_and_actor
    (K L T S : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hY : K ∈ Yz L T z v)
    (hS : S = ChapterB.baumann (Tv T v))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hblock : ChapterC.IsAlternatingBlock K 7)
    (hUK : ⁅WK K L T z v, K⁆ =
      ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆) :
    ∃ e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7),
      K ⊓ normalizer (S : Set G) ≤ ambientPreimage K e 6 ∧
      Tv T v ≤ normalizer (ambientPreimage K e 6 : Set G) ∧
      ∃ j ∈ Stellmacher.elementaryAbelianMaxJ (Tv T v),
        ∃ b ∈ replacement K e 6, ⁅j, b⁆ ∉ (replacement K e 6).pCoreIn 2 := by
  obtain ⟨e, φ, _, hc, hJ, hSJ⟩ := exists_ordinary_plus_marking
    K L T S z v hL hz hn hLv hY hS hWT hR hblock hUK
  let H := plusActor K L T v
  let ρ := φ.comp (plusMk K L T z v hL hz)
  have hKH : K ≤ H := ComponentSelection.K_le_plusActor K L T v
  have hTH : Tv T v ≤ H := le_sup_right
  have hSH : S ≤ H := by rw [hS]; exact inf_le_left.trans hTH
  have hJρ : actionImage H ρ (Stellmacher.elementaryAbelianMaxJ (Tv T v)) =
      threeTranspositions := by
    change ((Stellmacher.elementaryAbelianMaxJ (Tv T v)).subgroupOf H).map
      (φ.comp (plusMk K L T z v hL hz)) = _
    rw [← map_map]
    exact hJ
  have hSρ : actionImage H ρ S = threeTranspositions := by
    change (S.subgroupOf H).map (φ.comp (plusMk K L T z v hL hz)) = _
    rw [← map_map]
    change (plusImage K L T z v hL hz S).map φ = _
    rw [hSJ, hJ]
  exact ⟨e, normalizer_le_preimage_of_marking K H S hKH hSH e ρ hc hSρ,
    normalizes_preimage_of_marking K H (Tv T v) hKH hTH hn e ρ hc hJρ,
    exists_actor_of_marking K H (Tv T v) hKH e ρ hc hJρ⟩


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking
end
