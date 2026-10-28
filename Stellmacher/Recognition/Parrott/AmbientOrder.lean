module

public import Stellmacher.Recognition.Parrott.PresentationRealization
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.SpecificGroups.Tits.GeneratedImage

/-!
# The ambient order in Parrott's characterization

A finite nonsolvable simple N₂-group satisfying the original centralizer
hypotheses has order 17971200. The local realization gives one compatible
assignment of all ten generators satisfying all 37 relators and generating
the ambient group. Generation comes from the two full involution centralizers
and their Sylow fusion, through Thompson's mixed-involution counting theorem.

The induced presentation map is surjective by generation. Simplicity of the
presented model makes its kernel trivial: the alternative would kill the word
s₁s₅², whose image is the prescribed involution. The resulting bijection
transfers the certified model order. We retain that same assignment and its
anchor identity for the subsequent isomorphism construction.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§5, p.683 (the presentation), and §6, p.684 (the global order comparison).
-/

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {z : G}

/-- The actual generating realization induces a bijection from the presented
model, retaining the word for the original involution. -/
public theorem parrott_exists_bijective_lift
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    ∃ g : Tits.ParrottGenerator → G, ∃ hrels : Tits.SatisfiesParrottRelations g,
      g .s1 * (g .s5) ^ 2 = z ∧ Function.Bijective (Tits.parrottLift g hrels) := by
  obtain ⟨g, hrels, hanchor, hgen⟩ :=
    parrott_generating_presentation_realization hns hN h
  refine ⟨g, hrels, hanchor, ?_, (Tits.parrottLift_surjective_iff g hrels).mpr hgen⟩
  let φ := Tits.parrottLift g hrels
  apply φ.ker_eq_bot_iff.mp
  rcases φ.normal_ker.eq_bot_or_eq_top with hker | hker
  · exact hker
  · have htrivial : φ = 1 := MonoidHom.ker_eq_top_iff.mp hker
    have hword : φ (Tits.parrottGenerator .s1 * Tits.parrottGenerator .s5 ^ 2) = z := by
      simpa only [φ, map_mul, map_pow, Tits.parrottLift_generator] using hanchor
    have hz : z = 1 := by simpa only [htrivial, MonoidHom.one_apply] using hword.symm
    have ho := h.involution
    rw [hz, orderOf_one] at ho
    norm_num at ho

/-- Parrott's original hypotheses in a finite nonsolvable simple N₂-group
force the ambient order to be 17971200. -/
public theorem parrott_ambient_order
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) : Nat.card G = 17971200 := by
  obtain ⟨g, hrels, _, hbij⟩ := parrott_exists_bijective_lift hns hN h
  exact (Nat.card_congr (Equiv.ofBijective (Tits.parrottLift g hrels) hbij)).symm.trans
    Tits.parrottGroup_card

end Stellmacher.Recognition
