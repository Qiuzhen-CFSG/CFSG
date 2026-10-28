module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.PairwiseRecognition.Images
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.PairwiseRecognition.Modules
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition

/-!
# Exceptional pairwise recognition after 15.4.23

For each choice of `X i` and `Y j`, a normal A₆ Sylow supplement and an actual
`I/C_T(K) ≃* S₆` identify both factors as A₄, both embedded two-cores as groups
of order four, and their join as D₈ with nontrivial intersection.

Two-perfectness puts the factor join inside the normal supplement. Its trivial
center makes the centralizer quotient faithful on that entire join. The image
local overgroups have a common Sylow two-subgroup of index three and generate
S₆; finite-model recognition identifies their residuals and cores. Faithful
transport then gives the original factors, core join and intersection. The
source normal E₄ commutator modules equal these cores by their orders.

Source: Aschbacher–Smith, the paragraph after 15.4.23, printed p.1165
(PDF p.1182 of the combined manuscript, 1 March 2004). These are conditional
recognition theorems; construction of the exceptional witnesses in 15.4.22
and the proof of 15.4.23 remain with their source-theorem owner.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.Source
variable {G : Type*} [Group G] [Finite G] {d : Geometry G} (h : LocalData d)

/-- The six-letter residual-pair recognition lifts to the original factors and
cores through the actual centralizer quotient. The same map is injective on
their whole join, so the intersection conclusion also lifts. -/
theorem LocalData.pairwise_recognition_of_centralizer_quotient (i j : Bool)
    (K : Subgroup (d.I i j)) [K.Normal]
    (hgen : K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤)
    (eK : K ≃* alternatingGroup (Fin 6))
    (eQ : ((d.I i j) ⧸ centralizer (K : Set (d.I i j))) ≃* Equiv.Perm (Fin 6)) :
    Nonempty (d.X i ≃* alternatingGroup (Fin 4)) ∧
      Nonempty (d.Y j ≃* alternatingGroup (Fin 4)) ∧
      Nat.card ((d.X i).pCoreIn 2) = 4 ∧ Nat.card ((d.Y j).pCoreIn 2) = 4 ∧
      Nonempty (↥((d.X i).pCoreIn 2 ⊔ (d.Y j).pCoreIn 2) ≃* DihedralGroup 4) ∧
      (d.X i).pCoreIn 2 ⊓ (d.Y j).pCoreIn 2 ≠ ⊥ := by
  let f := recognitionMap i j K eQ
  have hf : Function.Surjective f := recognitionMap_surjective i j K eQ
  have hk := h.recognitionMap_ker_le_sylow i j K hgen eK eQ
  obtain ⟨h₁, h₂, hi₁, hi₂, hpair⟩ := h.quotient_pair_inputs i j f hf hk
  have hm := Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.residual_pair_recognition
    ((h.sylow i j).mapSurjective hf)
    (((d.G₁ i).subgroupOf (d.I i j)).map f)
    (((d.G₂ j).subgroupOf (d.I i j)).map f) h₁ h₂ hi₁ hi₂ hpair
  dsimp only at hm
  rw [h.quotient_residual_G₁ i j f, h.quotient_residual_G₂ i j f,
    ← h.recognition_core_map i j K hgen eK eQ (d.X i) le_sup_left,
    ← h.recognition_core_map i j K hgen eK eQ (d.Y j) le_sup_right] at hm
  obtain ⟨⟨eX⟩, ⟨eY⟩, hcX, hcY, ⟨eU⟩, hU⟩ := hm
  have hUX : (d.X i).pCoreIn 2 ≤ d.X i ⊔ d.Y j :=
    (pCoreIn_le 2 (d.X i)).trans le_sup_left
  have hUY : (d.Y j).pCoreIn 2 ≤ d.X i ⊔ d.Y j :=
    (pCoreIn_le 2 (d.Y j)).trans le_sup_right
  have hXI := (pCoreIn_le 2 (d.X i)).trans (d.X_le_I i j)
  have hYI := (pCoreIn_le 2 (d.Y j)).trans (d.Y_le_I i j)
  refine ⟨⟨(h.recognitionEquiv i j K hgen eK eQ (d.X i) le_sup_left).trans eX⟩,
    ⟨(h.recognitionEquiv i j K hgen eK eQ (d.Y j) le_sup_right).trans eY⟩,
    (Nat.card_congr (h.recognitionEquiv i j K hgen eK eQ _ hUX).toEquiv).trans hcX,
    (Nat.card_congr (h.recognitionEquiv i j K hgen eK eQ _ hUY).toEquiv).trans hcY,
    ?_, ?_⟩
  · have he := h.recognitionEquiv i j K hgen eK eQ
      ((d.X i).pCoreIn 2 ⊔ (d.Y j).pCoreIn 2) (sup_le hUX hUY)
    rw [subgroupOf_sup hXI hYI, Subgroup.map_sup] at he
    exact ⟨he.trans eU⟩
  · intro hbot
    apply hU
    rw [← h.recognition_inf_map i j K hgen eK eQ _ _ hUX hUY, hbot]
    simp

/-- Conditional recognition from the exceptional witnesses of 15.4.22, in
exactly its quotient convention `I/C_T(K)`. The choices `i` and `j` are arbitrary,
so this also applies to the alternate X-factor with the same Y-factor.

The normal A₆ supplement and quotient equivalence are explicit inputs to be
constructed by the source-theorem owner. No factor or core identification is
assumed. Normality of the displayed quotient kernel also follows from
`exceptional_centralizer_T`. -/
theorem LocalData.pairwise_recognition (i j : Bool)
    (K : Subgroup (d.I i j)) [K.Normal]
    (hgen : K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤)
    (eK : K ≃* alternatingGroup (Fin 6))
    [(((d.T : Subgroup G) ⊓ centralizer (K.map (d.I i j).subtype : Set G)).subgroupOf
      (d.I i j)).Normal]
    (eT : ((d.I i j) ⧸ (((d.T : Subgroup G) ⊓
      centralizer (K.map (d.I i j).subtype : Set G)).subgroupOf (d.I i j))) ≃*
      Equiv.Perm (Fin 6)) :
    Nonempty (d.X i ≃* alternatingGroup (Fin 4)) ∧
      Nonempty (d.Y j ≃* alternatingGroup (Fin 4)) ∧
      Nat.card ((d.X i).pCoreIn 2) = 4 ∧ Nat.card ((d.Y j).pCoreIn 2) = 4 ∧
      Nonempty (↥((d.X i).pCoreIn 2 ⊔ (d.Y j).pCoreIn 2) ≃* DihedralGroup 4) ∧
      (d.X i).pCoreIn 2 ⊓ (d.Y j).pCoreIn 2 ≠ ⊥ :=
  h.pairwise_recognition_of_centralizer_quotient i j K hgen eK
    (h.exceptionalQuotientEquiv i j K hgen eK eT)

/-- The normal E₄ commutator modules are the recognized two-cores. This ties
the D₈ and intersection conclusions to the source modules, whose sibling
disjointness is available for the final contradiction on printed p.1165. -/
theorem LocalData.pairwise_commutator_modules (i j : Bool)
    (K : Subgroup (d.I i j)) [K.Normal]
    (hgen : K ⊔ (h.sylow i j : Subgroup (d.I i j)) = ⊤)
    (eK : K ≃* alternatingGroup (Fin 6))
    [(((d.T : Subgroup G) ⊓ centralizer (K.map (d.I i j).subtype : Set G)).subgroupOf
      (d.I i j)).Normal]
    (eT : ((d.I i j) ⧸ (((d.T : Subgroup G) ⊓
      centralizer (K.map (d.I i j).subtype : Set G)).subgroupOf (d.I i j))) ≃*
      Equiv.Perm (Fin 6)) :
    d.V₁ i = (d.X i).pCoreIn 2 ∧ d.V₂ j = (d.Y j).pCoreIn 2 ∧
      Nonempty (↥(d.V₁ i ⊔ d.V₂ j) ≃* DihedralGroup 4) ∧ d.V₁ i ⊓ d.V₂ j ≠ ⊥ := by
  obtain ⟨_, _, hcX, hcY, hjoin, hinf⟩ := h.pairwise_recognition i j K hgen eK eT
  have hX := h.V₁_eq_twoCore_of_card i hcX
  have hY := h.V₂_eq_twoCore_of_card j hcY
  exact ⟨hX, hY, by rw [hX, hY]; exact hjoin,
    by simpa only [hX, hY] using hinf⟩

end CFSG.Quasithin.Chapter15.Section04.Source
