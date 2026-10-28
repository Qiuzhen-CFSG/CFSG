module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source.SylowAction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.AmbientAction

/-!
# E.6.7 rank-one geometry on the original subgroup V

Apply the intrinsic block torus to the original Sylow intersection. The
source inner-action theorem and coprime decomposition identify its moved
line with [V,X]. This gives every rank-one conclusion of E.6.7, together
with the actual regular action needed later in E.6.11. The only remaining
earlier-source input is the typed Borel identification from C.1.29.

Source: Aschbacher–Smith, E.6.7(3), printed p.246, and E.6.11, p.249.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Every rank-one clause and its regular-action strengthening for the same
actual torus. C.1.29 supplies the explicitly named Borel premise. -/
theorem source_rankOne_of_borel {𝒦 : GroupClass} {T : Sylow 2 G}
    {M V W H L : Subgroup G} {n : ℕ}
    (h : HypothesisE61 𝒦 T M V) (hW : W ∈ obstructionFamily M V)
    (hQH : sylowCentralizer (T : Subgroup G) V ≤ H)
    (hHC : H ≤ centralizer (W : Set G)) (hc : HasCharacteristicTwo H)
    (hLH : L ≤ H) (hL : ChapterC.IsBlock (L.subgroupOf H))
    (hout : ¬ L ≤ M) (hType : ChapterC.IsL2EvenBlock L n)
    (hB : L2BlockBorel L (M.subgroupOf L) n) :
    V ≤ normalizer (L : Set G) ∧
    ∃ X : Subgroup G, X ≤ L ⊓ M ∧ IsCyclic X ∧ Nat.card X = 2^n-1 ∧
      V = (V ⊓ centralizer (L : Set G)) ⊔ ⁅V,X⁆ ∧
      Disjoint (V ⊓ centralizer (L : Set G)) ⁅V,X⁆ ∧ Nat.card ↥⁅V,X⁆ = 2^n ∧
      (L ⊓ M : Set G) = ((L ⊓ sylowCentralizer (T : Subgroup G) V : Subgroup G) : Set G) *
        (X : Set G) ∧
      L2BlockBorel L (M.subgroupOf L) n ∧ n ≤ subgroupCorank V W ∧
      RegularConjugationOnNonidentity X ⁅V,X⁆ := by
  let : IsElementaryAbelian 2 V := h.elementary
  obtain ⟨S, hS, hVN, hi⟩ := source_block_action h hW hQH hHC hc hLH hL
  have hSB : (S : Subgroup L) ≤ M.subgroupOf L := by
    rw [hS]
    intro x hx
    exact h.sylow_le hx.1
  obtain ⟨d⟩ := exists_rankOneBlockTorus hType S hSB hB
  let X := d.torus.map L.subtype
  have hXM : X ≤ L ⊓ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.property, d.le_borel hx⟩
  have hn : X ≤ normalizer (V : Set G) :=
    (le_inf (hXM.trans inf_le_right) ((hXM.trans inf_le_left).trans (hLH.trans hHC))).trans
      (h.localCentralizer_le_normalizer hW.2.1 hW.1)
  have he : ¬ V ≤ centralizer (L : Set G) :=
    fun hh => hout ((le_centralizer_iff.mp hh).trans h.centralizer_le)
  obtain ⟨hg, hd, hcD, hr⟩ := d.ambient_decomposition hType.1 hi he hn
  have hcyclic : IsCyclic X := by
    let : IsCyclic d.torus := d.cyclic
    exact isCyclic_of_surjective
      (d.torus.equivMapOfInjective L.subtype L.subtype_injective)
      (d.torus.equivMapOfInjective L.subtype L.subtype_injective).surjective
  have hcard : Nat.card X = 2^n-1 :=
    (card_map_of_injective L.subtype_injective).trans d.order
  have hprod : (L ⊓ M : Set G) =
      ((L ⊓ sylowCentralizer (T : Subgroup G) V : Subgroup G) : Set G) * (X : Set G) := by
    ext g
    constructor
    · intro hg
      have hh : (⟨g, hg.1⟩ : L) ∈ (M.subgroupOf L : Set L) := hg.2
      rw [d.borel_product] at hh
      obtain ⟨s, hs, x, hx, he⟩ := Set.mem_mul.mp hh
      have hsQ : s ∈ (sylowCentralizer (T : Subgroup G) V).subgroupOf L := hS ▸ hs
      exact Set.mem_mul.mpr ⟨s, ⟨s.property, hsQ⟩,
        x, mem_map_of_mem L.subtype hx, congrArg Subtype.val he⟩
    · rintro ⟨s, hs, x, hx, rfl⟩
      exact (L ⊓ M).mul_mem ⟨hs.1, h.sylow_le hs.2.1⟩ (hXM hx)
  have hDV : ⁅V,X⁆ ≤ V :=
    (le_sup_right : ⁅V,X⁆ ≤ (V ⊓ centralizer (L : Set G)) ⊔ ⁅V,X⁆).trans hg.ge
  have hDC : ⁅V,X⁆ ≤ normalizer (V ⊓ centralizer (L : Set G) : Set G) :=
    (hDV.trans (V.le_centralizer.trans (centralizer_le inf_le_left))).trans
      (centralizer_le_normalizer _)
  have hcor := corank_of_direct_decomposition hg hDC hd hcD
  have hbound : n ≤ subgroupCorank V W := by
    rw [← hcor]
    exact fixedSpace_corank_le_obstruction hW.1 (hLH.trans hHC)
  exact ⟨hVN, X, hXM, hcyclic, hcard, hg, hd, hcD, hprod, hB, hbound, hr⟩

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
