module
public import ABG.ChapterII.Section1.WreathedFrameFusion
public import ABG.ChapterII.Section1.WreathedLowNormalizerFusion

/-!
# Global fusion in the low wreathed automizer cases

For an actual wreathed fusion frame in a finite group, outer automizer
index two at `V` prevents any element of the abelian base `U` from being
conjugate to an element outside `U` in the specified Sylow subgroup.
If the automizer of `U` also has index two, all ambient conjugacies between
Sylow elements already occur inside that Sylow subgroup. These are the
fusion-control assertions used in cases (iii) and (iv) of ABG Chapter II,
Section 1, Proposition 2, article p.13, first two paragraphs in
`refs/latex/alperin-brauer-gorenstein-pages/page-014.tex`.

Apply the frame fusion relation theorem to base-membership equivalence
and to Sylow conjugacy, respectively. The base is normal in the Sylow
subgroup because it has index two, so Sylow conjugacy preserves base
membership. Base normalizer steps preserve membership directly, and
index-two `V` steps are already Sylow conjugacies by the local control
theorem. When both indices are two, both kinds of normalizer step give
Sylow conjugacy; the ordinary and outer base indices agree because the
base is abelian.
-/

namespace ABG.Wreathed
variable {G : Type*} [Group G] [Finite G]

/-- A low outer automizer at `V` prevents fusion between the base and its complement in `S`. -/
public theorem mem_base_iff_of_isConj_of_v_index_two
    (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G)
    (hf : WreathedFusionFrame S n U V) (hV : outerAutomizerIndex V = 2)
    {x y : S} (hxy : IsConj (x : G) (y : G)) :
    (x : G) ∈ U ↔ (y : G) ∈ U := by
  obtain ⟨P⟩ := nonempty_presentation hf.1
  have hUP : U.subgroupOf (S : Subgroup G) = P.U := by
    rw [(hf.presentation_representatives P).1]
    exact Subgroup.comap_map_eq_self_of_injective
      (S : Subgroup G).subtype_injective P.U
  have hn : (U.subgroupOf (S : Subgroup G)).Normal := by
    rw [hUP]
    exact Subgroup.normal_of_index_eq_two P.index_U
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hf.2.1).mp hn
  have hconj {a b : S} (hab : IsConj a b) : (a : G) ∈ U ↔ (b : G) ∈ U := by
    obtain ⟨s, rfl⟩ := isConj_iff.mp hab
    exact Subgroup.mem_normalizer_iff.mp (hSN s.property) a
  apply wreathed_representative_fusion_relation S n U V hf
    (fun a b => (a : G) ∈ U ↔ (b : G) ∈ U) (fun _ => Iff.rfl)
    (fun h₁ h₂ => h₁.trans h₂) hconj ?_ ?_ hxy
  · intro g hg a b _hUa hab
    rw [← hab]
    exact Subgroup.mem_normalizer_iff''.mp hg a
  · intro g hg a b hVa hab
    exact hconj (low_normalizer_fusion_control S n U V V hf (Or.inr rfl)
      hV g hg a b hVa hab)

/-- If both wreathed automizers have order two, the Sylow subgroup controls element fusion. -/
public theorem isConj_of_indices_two
    (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G)
    (hf : WreathedFusionFrame S n U V)
    (hU : automizerIndex U = 2) (hV : outerAutomizerIndex V = 2)
    {x y : S} (hxy : IsConj (x : G) (y : G)) : IsConj x y := by
  let : IsMulCommutative U := hf.2.2.1
  have hUout : outerAutomizerIndex U = 2 := by
    unfold outerAutomizerIndex automizerIndex at *
    rw [sup_eq_right.mpr (Subgroup.le_centralizer (H := U))]
    exact hU
  exact wreathed_representative_fusion_relation S n U V hf IsConj IsConj.refl
    (fun h₁ h₂ => h₁.trans h₂) (fun h => h)
    (low_normalizer_fusion_control S n U V U hf (Or.inl rfl) hUout)
    (low_normalizer_fusion_control S n U V V hf (Or.inr rfl) hV) hxy

end ABG.Wreathed
