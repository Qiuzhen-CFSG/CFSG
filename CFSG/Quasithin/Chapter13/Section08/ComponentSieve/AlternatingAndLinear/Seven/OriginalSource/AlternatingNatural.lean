module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.Structure
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# The actual 13.7.6 input in the pair-partition argument

The natural section in `CentralAction` is the same literal commutator image
modulo its component-fixed vectors as in the earlier source recognition
interface. Their actor maps agree on every component representative. A
C-component cannot have a solvable alternating quotient, so its degree is
at least five and the original 13.7.6 implication applies. In degree seven
the concrete hexacode marking constructs the perfect central triple cover
used by the pair-partition contradiction.

This discharges `Earlier.alternating_natural` from the preceding source
input already used by 13.8.5. It does not assume a new natural-section
recognition theorem or a conclusion of 13.8.24.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.7.6(3), pp.938–940, and 13.8.24, p.959.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open PairsBranch.CentralAction

private theorem triple_cover_of_hex {Q : Type*} [Group Q]
    (e : Q ≃* Atlas.Codes.HexEvenAutomorphisms) : IsTripleCoverSix Q := by
  let : IsQuasisimple Atlas.Codes.HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let : IsQuasisimple Q := IsQuasisimple.of_mulEquiv e.symm
  have hm : (center Q).map e.toMonoidHom = center Atlas.Codes.HexEvenAutomorphisms := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (centerCongr e ⟨y, hy⟩).property
    · intro hx
      exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩
  let a := (QuotientGroup.congr _ _ e hm).trans Hexacode.even_quotient_center_equiv
  let f : Q →* alternatingGroup (Fin 6) :=
    a.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hk : f.ker = center Q := by
    ext x
    change a (QuotientGroup.mk' (center Q) x) = 1 ↔ x ∈ center Q
    rw [map_eq_one_iff _ a.injective]
    exact QuotientGroup.eq_one_iff (N := center Q) x
  refine ⟨inferInstance, f, a.surjective.comp (QuotientGroup.mk'_surjective _), hk.le, ?_⟩
  rw [hk, Nat.card_congr (centerCongr e).toEquiv, Hexacode.even_center_card]

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))

include d earlier

/-- Construct the pair-branch's universal natural-section implication from
the original earlier source theorem, with the same quotient and actor map. -/
theorem alternating_natural :
    AlternatingNaturalImplication L (sourceOne L T V₁) (T : Subgroup G) G₁ M ρ := by
  intro hH _ hρ J hJH hJ n e hnat
  have hn : 5 ≤ n := by
    by_contra! hn
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let a := (Components.componentStarEquiv H J hJH hJ).symm.trans e
    let f := (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (by omega : n ≤ 4))).comp
      ((alternatingGroup (Fin n)).subtype.comp a.toMonoidHom)
    have hf : Function.Injective f :=
      (Equiv.Perm.viaEmbeddingHom_injective _).comp (Subtype.val_injective.comp a.injective)
    exact (Components.starImage_isCComponent H J hJ).not_isSolvable
      (Group.isSolvable_of_isSolvable_injective hf)
  have hs : HasSectionModel H V₃ V₁ ρ J hJH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) e := by
    obtain ⟨hs, a, ha⟩ := hnat
    exact ⟨hs, a, ha⟩
  obtain ⟨hgen, hle, hprod, h6 | h7⟩ := earlier.alternating d H hH ρ hρ J hJH hJ n hn e hs
  · exact ⟨hgen, hle, hprod, Or.inl ⟨h6.1, h6.2.1⟩⟩
  · exact ⟨hgen, hle, hprod, Or.inr ⟨h7.1, triple_cover_of_hex (Classical.choice h7.2)⟩⟩

/-- In the actual pair-partition consumer, a natural maximal quotient and
the ordinary A₆ local quotient force K to move the submodule. The previous
13.7.6 callback and the line-containment premise are both discharged. -/
theorem source_nontrivial_on_submodule
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hρ : IsSourceAction H V₃ V₁ ρ) (K : Subgroup G)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 7)) (hφ : Function.Injective φ)
    (hφK : (Source.starImage H K).map φ = alternatingGroup (Fin 7))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Subrepresentation ρ)
    (a : (Additive (Source.Utilde H V₃ V₁) ⧸ W.toSubmodule) ≃ₗ[ZMod 2]
      BinaryPermutation.core (Fin 7))
    (ha : ∀ g q, a (W.quotientRepresentation g q) =
      BinaryPermutation.coreRepresentation _ (φ g) (a q)) :
    ∃ k ∈ Source.starImage H K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w := by
  exact nontrivial_on_submodule L (sourceOne L T V₁) (T : Subgroup G) G₁ M K ρ
    hH (d.line_le_uh H) hρ hKH hK hgen φ hφ hφK eL W a ha (alternating_natural d earlier ρ)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
