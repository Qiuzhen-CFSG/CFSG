module

public import Stellmacher.SectionThree.LemmaThreeEight
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# The core subgroup in Stellmacher (3.8)

The first subgroup in the normal series of (3.8) is exactly
`S ⊓ O₂(H)`.  To prove this, adjoin `O₂(H)` to the maximal normal subgroup
`N`.  This join still avoids both local 2-residuals: otherwise residual
idempotence and the 2-group quotient put the offending residual back in `N`.
Maximality therefore gives `O₂(H) ≤ N`.

Conversely, the subgroup produced by (3.8) is normal in `H`, lies in `S`, and
is a 2-group.  It consequently lies in `O₂(H)`, yielding equality.  This is
the final core-identification paragraph in the proof of Stellmacher (3.8),
journal p. 23, as transcribed in `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionThree

open BenderSuzuki.External

universe u

private theorem twoResidualAmbient_idempotent_38core
    {G : Type u} [Group G] [Finite G] (P : Subgroup G) :
    twoResidualAmbient (twoResidualAmbient P) = twoResidualAmbient P := by
  classical
  let R : Subgroup G := twoResidualAmbient P
  have htop : twoResidualAmbient (⊤ : Subgroup R) = ⊤ := by
    rw [twoResidualAmbient_top_eq_hktPResidual]
    exact twoResidualAmbient_has_top_twoResidual P
  have hmap := map_twoResidualAmbient_of_subgroup_image
    (⊤ : Subgroup R) R.subtype R (by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  exact hmap.symm

private theorem twoCoreAmbient_normal_in_self_38core
    {G : Type u} [Group G] (H : Subgroup G) :
    ((twoCoreAmbient H).subgroupOf H).Normal := by
  unfold twoCoreAmbient
  rw [subgroupOf_map_subtype_eq]
  exact pCore_normal

private theorem twoCoreAmbient_isPGroup_38core
    {G : Type u} [Group G] (H : Subgroup G) :
    IsPGroup 2 (twoCoreAmbient H) := by
  exact (pCore_isPGroup (p := 2) (G := H)).map H.subtype

/-- In the normal series supplied by (3.8), the first subgroup is the
intersection of the fixed 2-subgroup with the 2-core of the generated group. -/
public theorem lemma_three_eight_core_eq_twoCore
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P₁ P₂ H N : Subgroup G)
    (hP₁ : P₁ ∈ PSet (⊤ : Subgroup G) S)
    (hP₂ : P₂ ∈ PSet (⊤ : Subgroup G) S)
    (hH : H = P₁ ⊔ P₂)
    (hN : N ≤ H ∧ (N.subgroupOf H).Normal ∧
      ¬ twoResidualAmbient P₁ ≤ N ∧
      ¬ twoResidualAmbient P₂ ≤ N ∧
      ∀ N' : Subgroup G, N ≤ N' → N' ≤ H →
        (N'.subgroupOf H).Normal →
        (¬ twoResidualAmbient P₁ ≤ N' ∧
          ¬ twoResidualAmbient P₂ ≤ N') → N' = N)
    (hsolv₁ : Group.IsSolvable P₁)
    (hsolv₂ : Group.IsSolvable P₂) :
    ∃ H₀ H₁ : Subgroup G,
      LemmaThreeEightConclusion S P₁ P₂ H N
        (S ⊓ twoCoreAmbient H) H₀ H₁ := by
  classical
  let O : Subgroup G := twoCoreAmbient H
  have hOH : O ≤ H := Subgroup.map_subtype_le _
  have hOp : IsPGroup 2 O := twoCoreAmbient_isPGroup_38core H
  have hOnormalH : (O.subgroupOf H).Normal :=
    twoCoreAmbient_normal_in_self_38core H
  let K : Subgroup G := N ⊔ O
  have hKH : K ≤ H := sup_le hN.1 hOH
  have hKnormalH : (K.subgroupOf H).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr
    exact (le_inf
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hN.1).mp hN.2.1)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mp hOnormalH)).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup N O)
  have hNnormalK : (N.subgroupOf K).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    exact hKH.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hN.1).mp hN.2.1)
  have hRi_le_N_of_le_K (P : Subgroup G)
      (hR : twoResidualAmbient P ≤ K) : twoResidualAmbient P ≤ N := by
    have hres : twoResidualAmbient (twoResidualAmbient P) ≤ N :=
      twoResidualAmbient_le_left_of_le_sup N O (twoResidualAmbient P)
        (by simpa [K] using hNnormalK) hOp (by simpa [K] using hR)
    simpa [twoResidualAmbient_idempotent_38core P] using hres
  have hR₁notK : ¬ twoResidualAmbient P₁ ≤ K := fun hR =>
    hN.2.2.1 (hRi_le_N_of_le_K P₁ hR)
  have hR₂notK : ¬ twoResidualAmbient P₂ ≤ K := fun hR =>
    hN.2.2.2.1 (hRi_le_N_of_le_K P₂ hR)
  have hKN : K = N := hN.2.2.2.2 K le_sup_left hKH hKnormalH
    ⟨hR₁notK, hR₂notK⟩
  have hON : O ≤ N := by
    rw [← hKN]
    exact le_sup_right
  obtain ⟨Q₀, H₀, H₁, h38⟩ :=
    lemma_three_eight S h P₁ P₂ H N hP₁ hP₂ hH hN hsolv₁ hsolv₂
  have hQ₀S : Q₀ ≤ S := by
    rw [h38.part_a.1]
    exact inf_le_left
  have hQ₀p : IsPGroup 2 Q₀ := h.nontrivial_two_subgroup.2.to_le hQ₀S
  have hQ₀H : Q₀ ≤ H := hQ₀S.trans (by
    have hSP₁ : S ≤ P₁ := by
      obtain ⟨U, hU⟩ := hP₁.1.2.1
      rw [← hU]
      exact Subgroup.map_subtype_le _
    rw [hH]
    exact hSP₁.trans le_sup_left)
  have hQ₀O : Q₀ ≤ O := by
    let QH : Subgroup H := Q₀.subgroupOf H
    have hQHp : IsPGroup 2 QH := hQ₀p.comap_subtype
    have hQHcore : QH ≤ pCore 2 H := le_sSup ⟨h38.part_a.2.1, hQHp⟩
    have hm := Subgroup.map_mono (f := H.subtype) hQHcore
    simpa [QH, O, twoCoreAmbient,
      Subgroup.map_subgroupOf_eq_of_le hQ₀H] using hm
  have hQeq : S ⊓ O = Q₀ := by
    apply le_antisymm
    · rw [h38.part_a.1]
      exact inf_le_inf le_rfl hON
    · exact le_inf hQ₀S hQ₀O
  refine ⟨H₀, H₁, ?_⟩
  simpa [O, hQeq] using h38

end Stellmacher.SectionThree
