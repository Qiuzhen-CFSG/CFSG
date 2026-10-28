module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.GraphCounting
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.Reduced
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.OuterTransport

/-!
# The actual mixed-pair application of the graph seed count

Use the published reduced graph of the original A₅/S₃ pair. Its elementary
alpha core and (11.3)(h) generation identity identify the beta core with
the two neighboring seeds. The graph count gives order 64 for the literal
reduced Sylow, embedded in the reduced completion. Transport through that
inclusion and the original Borel-core index formula yields order 64 or 128
for the original S.

No conjugator, auxiliary normalizer, finite completion, or model
identification is supplied as an extra premise. The earlier source core
product, alpha-core identity and seed cardinalities remain explicit. This
is a conditional mixed-size application, not a proof of the complete
Chapter 11 branch or its exhaustion from the original F.1.11 hypotheses.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.3)(h), (11.4), (11.7)(c,e), pp.169--175; (15.1), p.226.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]
variable (K U S : Subgroup G)
local notation "F" => Reduction.reducedFamily ![K,U] S
local notation "M" => Reduction.G₀ ![K,U] S
local notation "R₀" => Subgroup.subgroupOf (twoCore (commonBorel ![K,U] S)) M
local notation "α" => base F false
local notation "β" => base F true

/-- The graph-level premises feed the original, unmodified mixed-pair Sylow. -/
theorem mixed_binary_graph_row_size (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (c : Vertex F) (hbc : (graph F).Adj β c)
    (hR : R₀ = Q F α ⊔ Q F β)
    (hgen : Q F β = pairSpan (Z F α) (Z F c) (Q F β) ⊔ (Q F α ⊓ Q F β))
    (hQa : Q F α = Z F α)
    (hZ : Nat.card (Z F α) = 16)
    (hindex : (Z F α ⊓ Q F β).relIndex (Z F α) = 2)
    (hinter : Nat.card ((Z F α ⊓ Q F β) ⊓ (Z F c ⊓ Q F β) : Subgroup M) = 2) :
    Nat.card (twoCore (commonBorel ![K,U] S)) = 64 ∧
      (Nat.card S = 64 ∨ Nat.card S = 128) := by
  have ht := Reduction.reduced_triple h
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base F false true⟩
  have hpair := beta_core_eq_pairSpan_of_alpha_core_eq _ _ _ _ hgen hQa
  have hR' : R₀ = Z F α ⊔ Q F β := hR.trans (congrArg (· ⊔ Q F β) hQa)
  have hcount : Nat.card R₀ = 64 := by
    simpa using source_sylow_card_of_pair_core ht hab hbc R₀ hpair hR'
      4 2 (by decide) (by decide) (by norm_num; exact hZ) hindex hinter
  have hle : twoCore (commonBorel ![K,U] S) ≤ M :=
    (show twoCore (commonBorel ![K,U] S) ≤ Reduction.B₀ ![K,U] S from le_sup_right).trans
      ((show Reduction.B₀ ![K,U] S ≤ Reduction.P₀ ![K,U] S 0 from le_sup_right).trans le_sup_left)
  have hc : Nat.card (twoCore (commonBorel ![K,U] S)) = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).symm.trans hcount
  have hc' : Nat.card (pCore 2 (commonBorel ![K,U] S)) = 64 :=
    (card_map_of_injective (commonBorel ![K,U] S).subtype_injective).symm.trans hc
  have hs := h.mixed_sylow_card_borel_core_cases eK eU
  rw [hc'] at hs
  exact ⟨hc,by simpa using hs⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
