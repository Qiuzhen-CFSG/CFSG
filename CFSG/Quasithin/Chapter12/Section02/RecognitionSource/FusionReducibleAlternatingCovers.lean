module

public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Definitions
public import Theory.Representation.BinaryPermutation.CentralCoverRecognition

/-!
# Reconstructing the alternating cores in reducible row (d)

Reindex the faithful action on the original chosen space by the given
row-(d) actor isomorphism. Its literal fixed-space quotient is a perfect
central cover of the natural module: the Irr⁺ condition supplies commutator
generation. Nonzero C_V(L) makes its kernel nonzero. Vanishing odd-degree
cohomology excludes degrees five and seven, and universal-cover recognition
identifies V with the augmentation core in degree six or eight.

The marking here is still L/C_L(V), exactly as in row (d). Identification
of that quotient with L/O₂(L), and the orbit and Sylow arguments needed
for the A₈ fusion seed, are separate source steps.

Source: Aschbacher–Smith, 12.2.2(3d), p.795; 12.2.16, pp.799–800,
using I.1.5–6, p.408.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The nonzero fixed subgroup in row (d) forces degree six or eight and
recovers the whole augmentation core under the original faithful actor. -/
theorem alternating_core_of_nonzero_fixed (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (n : ℕ) (hlo : 5 ≤ n) (hhi : n ≤ 8)
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulCentralAction (alternatingNatural n)) :
    (n = 6 ∨ n = 8) ∧
      (letI := D.actionCentralizer_normal
       Nonempty (ActionEquiv D.faithfulAction
         (BinaryPermutation.alternatingCoreRepresentation (Fin n)))) := by
  let := D.actionCentralizer_normal
  let C := (fixedSpace (reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G)))).comap D.space.subtype
  let σ : Representation (ZMod 2) (alternatingGroup (Fin n)) D.space :=
    D.faithfulAction.comp e.groupEquiv.symm.toMonoidHom
  have hσ (l : L) (v : D.space) :
      σ (e.groupEquiv (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l)) v =
        D.chosenAction l v := by
    change D.faithfulAction (e.groupEquiv.symm (e.groupEquiv _)) v = _
    rw [e.groupEquiv.symm_apply_apply]
    rfl
  have hsurj : Function.Surjective (fun l : L =>
      e.groupEquiv (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l)) :=
    e.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  let p : σ.IntertwiningMap (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) :=
    (e.linearEquiv.toLinearMap.comp C.mkQ).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro a v
      obtain ⟨l,rfl⟩ := hsurj a
      change e.linearEquiv (C.mkQ (σ _ v)) = _
      rw [hσ]
      exact e.intertwines
        (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l) (C.mkQ v))
  have hpker : p.toLinearMap.ker = C := by
    ext v
    change e.linearEquiv (C.mkQ v) = 0 ↔ v ∈ C
    rw [e.linearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hp : IsCover p := by
    refine ⟨e.linearEquiv.surjective.comp (Submodule.mkQ_surjective C), ?_, ?_⟩
    · intro v hv a
      obtain ⟨l,rfl⟩ := hsurj a
      rw [hσ]
      have hvC : v ∈ C := hpker ▸ hv
      exact Subtype.ext (hvC ((subgroupOfEquivOfLe
        (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm l))
    · have hle : D.space ≤ (Coinvariants.ker σ).map D.space.subtype := by
        apply D.irrPlus.isIrrPlus.choose_spec.1.ge.trans
        apply Submodule.span_le.mpr
        rintro _ ⟨l, hl, v, hv, rfl⟩
        let l' : L := ⟨l.val,hl⟩
        let v' : D.space := ⟨v,hv⟩
        refine ⟨σ (e.groupEquiv (QuotientGroup.mk'
          ((centralizer (V : Set G)).subgroupOf L) l')) v' - v',
          Coinvariants.sub_mem_ker _ _, ?_⟩
        rw [hσ]
        rfl
      apply top_unique
      intro v _
      obtain ⟨w,hw,he⟩ := hle v.property
      exact (Subtype.ext he : w = v) ▸ hw
  have hk : p.toLinearMap.ker ≠ ⊥ := by
    rw [hpker]
    obtain ⟨z,hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    let v := (D.spaceEquiv.symm ⟨z,z.property.1⟩).toAdd
    have hv : (v.val.toMul.val : G) = z :=
      (D.spaceEquiv_apply v).symm.trans
        (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply ⟨z,z.property.1⟩))
    have hvC : v ∈ C := by
      intro l
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      change (l.val.val : G) * (v.val.toMul.val : G) * (l.val.val : G)⁻¹ =
        (v.val.toMul.val : G)
      rw [hv]
      exact mul_inv_eq_iff_eq_mul.mpr (z.property.2 _ l.property)
    intro he
    have hv0 : v = 0 := (Submodule.mem_bot (R := ZMod 2)).mp (he ▸ hvC)
    apply hzne
    exact Subtype.ext (hv.symm.trans
      (congrArg (fun w : D.space => (w.val.toMul.val : G)) hv0))
  have heven : n = 6 ∨ n = 8 := by
    by_contra hn
    have ho : Odd n := by
      have hn' : n = 5 ∨ n = 7 := by omega
      rcases hn' with rfl | rfl <;> decide
    exact hk (LinearMap.ker_eq_bot.mpr
      (BinaryPermutation.alternating_odd_cover_injective (by omega) ho σ p hp))
  obtain ⟨E,hE,_⟩ := BinaryPermutation.alternating_even_cover_equiv_core heven σ p hp hk
  refine ⟨heven, ⟨⟨e.groupEquiv,E,?_⟩⟩⟩
  intro q v
  have hh := hE (e.groupEquiv q) v
  change E (D.faithfulAction (e.groupEquiv.symm (e.groupEquiv q)) v) = _ at hh
  rwa [e.groupEquiv.symm_apply_apply] at hh

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
