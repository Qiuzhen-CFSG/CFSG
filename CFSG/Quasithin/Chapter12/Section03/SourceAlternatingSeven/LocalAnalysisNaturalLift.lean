module

public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Definitions
public import Theory.Representation.BinaryPermutation.CentralCoverRecognition

/-!
# Lifting the odd alternating natural quotient of an original Irr⁺ choice

The map from the whole chosen space to its fixed-space quotient is a
perfect central cover: Irr⁺ supplies generation by commutators, and its
kernel is fixed by the original actor. Vanishing dual first cohomology
makes this very map injective. Thus the natural marking lifts to the whole
chosen space, with the original faithful actor unchanged.

Source: Aschbacher--Smith, Lemma 12.3.3, printed pp.807--808, using I.1.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The natural quotient in odd degree determines the entire original choice.
The perfect-cover hypothesis, including V=[V,L], is proved from Irr⁺. -/
theorem fullAction_of_odd_alternating_quotient (D : ChosenModule T L V)
    {n : ℕ} (hn : 3 ≤ n) (ho : Odd n)
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulCentralAction (alternatingNatural n)) :
    letI := D.actionCentralizer_normal
    Nonempty (ActionEquiv D.faithfulAction (alternatingNatural n)) := by
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
  let E := LinearEquiv.ofBijective p.toLinearMap
    ⟨BinaryPermutation.alternating_odd_cover_injective hn ho σ p hp, hp.1⟩
  refine ⟨⟨e.groupEquiv, E, ?_⟩⟩
  intro q v
  have h := LinearMap.congr_fun (p.isIntertwining' (e.groupEquiv q)) v
  change E (D.faithfulAction (e.groupEquiv.symm (e.groupEquiv q)) v) = _ at h
  rwa [e.groupEquiv.symm_apply_apply] at h

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
