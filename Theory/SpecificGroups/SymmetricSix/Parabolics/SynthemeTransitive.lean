module
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals
public import Theory.SpecificGroups.SymmetricFour.ResidualFactorization
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PPerfectHom

/-!
# Transitive two-perfect subgroups of a syntheme stabilizer

A nontrivial two-perfect subgroup normalized by the marked syntheme S₄ is
its A₄ residual. The tetrahedral edge action makes that A₄ transitive on
six letters. We transport this criterion through arbitrary S₆ conjugates,
matching the markings in the natural A₆ source row.

The proof first passes to S₄, where two-perfectness places the subgroup
in A₄. Its normal-subgroup classification leaves only the trivial subgroup,
the Klein four-group, and A₄; the first two are excluded. A finite kernel
check verifies transitivity of the existing edge action.

Source application: Aschbacher–Smith, C.2.7 and 15.3.21, combined manuscript
of 1 March 2004, pp.145–147 and1127. Together with the natural-module cocycle
calculation, transitivity detects component-fixed vectors in the second
choice without assuming that the ambient module extension splits.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Equiv Equiv.Perm
namespace Theory.SpecificGroups.SymmetricSix

private theorem four_normal_twoPerfect_eq (B : Subgroup (Equiv.Perm (Fin 4)))
    [B.Normal] (hp : IsPPerfect 2 B) (hne : B ≠ ⊥) :
    B = alternatingGroup (Fin 4) := by
  have hBA : B ≤ alternatingGroup (Fin 4) := by
    rw [← Theory.SpecificGroups.SymmetricFourResidual.residual_eq]
    exact le_pResidual_of_isPPerfect B hp
  let D := B.subgroupOf (alternatingGroup (Fin 4))
  let e : D ≃* B := subgroupOfEquivOfLe hBA
  have hpD : IsPPerfect 2 D := hp.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hz : D ≠ ⊥ := by
    intro h
    apply hne
    apply eq_bot_iff.mpr
    intro b hb
    have he : (⟨b, hBA hb⟩ : alternatingGroup (Fin 4)) = 1 := by
      apply mem_bot.mp
      rw [← h]
      exact hb
    exact congrArg (fun x : alternatingGroup (Fin 4) => x.val) he
  rcases AlternatingFourPair.normalA4 D with h | h | h
  · exact (hz h).elim
  · have hpg : IsPGroup 2 D := by
      rw [h]
      exact IsPGroup.of_card (n := 2) (alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num))
    have hi := hpD.hom_eq_one_of_isPGroup hpg (MonoidHom.id D)
    apply (hz (eq_bot_iff.mpr ?_)).elim
    intro d hd
    exact congrArg Subtype.val (DFunLike.congr_fun hi ⟨d, hd⟩)
  · exact le_antisymm hBA (subgroupOf_eq_top.mp h)

private theorem syntheme_residual_transitive :
    ∀ i j : Fin 6, ∃ a : ResidualPairRecognition.A,
      ResidualPairRecognition.synthemeHom a i = j := by
  decide +kernel

/-- A nontrivial two-perfect subgroup normalized by the syntheme S₄ is
its A₄ residual, so its six-letter action is transitive. -/
theorem syntheme_normal_twoPerfect_transitive
    (N : Subgroup (alternatingGroup (Fin 6)))
    (hN : N ≤ a6SynthemeStabilizer)
    (hNN : a6SynthemeStabilizer ≤ normalizer (N : Set (alternatingGroup (Fin 6))))
    (hp : IsPPerfect 2 N) (hne : N ≠ ⊥) :
    ∀ i j : Fin 6, ∃ g : N, g.val.val i = j := by
  let S := a6SynthemeStabilizer
  let Q := N.subgroupOf S
  let e := ResidualPairRecognition.ComponentLocals.edgeEquiv
  let B := Q.map e.symm.toMonoidHom
  have hQn : Q.Normal := normal_subgroupOf_of_le_normalizer hNN
  let : B.Normal := Subgroup.Normal.map hQn _ e.symm.surjective
  let a : N ≃* Q := (subgroupOfEquivOfLe hN).symm
  let b : Q ≃* B := equivMapOfInjective Q e.symm.toMonoidHom e.symm.injective
  have hpB : IsPPerfect 2 B := hp.of_surjective (a.trans b).toMonoidHom (a.trans b).surjective
  have hneB : B ≠ ⊥ := by
    intro hb
    apply hne
    apply eq_bot_iff.mpr
    intro n hn
    have hz : (a.trans b) ⟨n, hn⟩ = 1 := Subtype.ext (mem_bot.mp (hb ▸ ((a.trans b) ⟨n, hn⟩).property))
    exact congrArg Subtype.val ((a.trans b).injective (hz.trans (map_one _).symm))
  have hB := four_normal_twoPerfect_eq B hpB hneB
  intro i j
  obtain ⟨u, hu⟩ := syntheme_residual_transitive i j
  have huB : (u : Equiv.Perm (Fin 4)) ∈ B := hB ▸ u.property
  obtain ⟨v, hv, huv⟩ := huB
  refine ⟨⟨v.val, hv⟩, ?_⟩
  have he : e u.val = v := by rw [← huv]; exact e.apply_symm_apply v
  have hev := congrArg (fun x : S => x.val.val) he
  change v.val.val i = j
  rw [← hev]
  exact hu

/-- The transitivity criterion with the conjugate marking used by the source
parabolic placement. Conjugation is allowed by any permutation of six letters. -/
theorem conjugate_syntheme_normal_twoPerfect_transitive
    (g : Equiv.Perm (Fin 6)) (N : Subgroup (alternatingGroup (Fin 6)))
    (hN : N ≤ a6SynthemeStabilizer.map (MulAut.conjNormal g).toMonoidHom)
    (hNN : a6SynthemeStabilizer.map (MulAut.conjNormal g).toMonoidHom ≤
      normalizer (N : Set (alternatingGroup (Fin 6))))
    (hp : IsPPerfect 2 N) (hne : N ≠ ⊥) :
    ∀ i j : Fin 6, ∃ n : N, n.val.val i = j := by
  let α : MulAut (alternatingGroup (Fin 6)) := MulAut.conjNormal g
  let B := N.map α.symm.toMonoidHom
  have hBS : B ≤ a6SynthemeStabilizer := by
    rintro b ⟨n, hn, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hN hn
    change α.symm (α s) ∈ a6SynthemeStabilizer
    rw [α.symm_apply_apply]
    exact hs
  have hBN : a6SynthemeStabilizer ≤ normalizer (B : Set (alternatingGroup (Fin 6))) := by
    calc
      a6SynthemeStabilizer =
          (a6SynthemeStabilizer.map α.toMonoidHom).map α.symm.toMonoidHom := by
        ext x
        constructor
        · intro hx
          exact ⟨α x, ⟨x, hx, rfl⟩, α.symm_apply_apply x⟩
        · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          change α.symm (α z) ∈ a6SynthemeStabilizer
          rw [α.symm_apply_apply]
          exact hz
      _ ≤ (normalizer (N : Set (alternatingGroup (Fin 6)))).map α.symm.toMonoidHom := map_mono hNN
      _ ≤ normalizer (B : Set (alternatingGroup (Fin 6))) := N.le_normalizer_map _
  have hpB : IsPPerfect 2 B := hp.of_surjective (α.symm.subgroupMap N).toMonoidHom
    (α.symm.subgroupMap N).surjective
  have hneB : B ≠ ⊥ := by
    intro h
    apply hne
    apply eq_bot_iff.mpr
    intro n hn
    apply α.symm.injective
    exact (mem_bot.mp (h ▸ mem_map_of_mem α.symm.toMonoidHom hn)).trans (map_one _).symm
  intro i j
  obtain ⟨b, hb⟩ := syntheme_normal_twoPerfect_transitive B hBS hBN hpB hneB (g⁻¹ i) (g⁻¹ j)
  obtain ⟨n, hn, he⟩ := b.property
  refine ⟨⟨n, hn⟩, ?_⟩
  have hnval : (α b.val).val = n.val := congrArg Subtype.val (by
    rw [← he]
    exact α.apply_symm_apply n)
  change n.val i = j
  rw [← hnval]
  change (g * b.val.val * g⁻¹) i = j
  simp only [Perm.mul_apply, hb]
  exact g.apply_symm_apply j

end Theory.SpecificGroups.SymmetricSix
