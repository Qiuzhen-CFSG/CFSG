module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.Track
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.ChiefActions
public import Theory.GroupAction.RankTwoCosetGeometry.CentralKernel

/-!
# The literal quintic graph's core layers and escaping conjugate

In the marked-five, single-S₃ branch, the odd critical track places the
chosen V in the first vertex's radius-three kernel. Its entire H-span
therefore lies in the cubic vertex's radius-two kernel. The two faithful
noncentral chief factors give this kernel order at least sixteen. The
original nontrivial central seed Z(T) ∩ V survives in the radius-four
kernel at that same cubic vertex.

Parity also constructs a conjugate of V under the actual generated group
⟨YT,H⟩ which lies in T and escapes O₂(H). Thus the weak-closure premise
that would force even track cannot be inserted into the recognition step.
All subgroup maps are the original inclusions; no model or recognition
hypothesis is introduced.

These are Chapter 15 inputs to the remaining marked (5,3) recognition,
whose shared engine belongs to qt-e-quintic-recognition. The adapter,
source exclusions and final assembly remain with qt-e-152-small-parabolic.
Source: Aschbacher--Smith 15.2.6--8, printed pp.1109--1110, and
F.7.10--11, printed pp.313--314.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open ChapterF.Section07.Track ChapterF.Section07.CriticalPairs Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- The original elementary H-span and its central seed survive in the
literal radius-two and radius-four kernels at the cubic endpoint. -/
theorem ChosenSmallSource.marked_five_symmetricThree_kernel_data
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    let P := h.residual ⊔ (T : Subgroup G)
    let W := P ⊔ H
    let F : Bool → Subgroup W := fun i => if i then H.subgroupOf W else P.subgroupOf W
    (conjugateSpan H V).subgroupOf W ≤ ballKernel F (base F true) 2 ∧
      (centralInvolutions T ⊓ V).subgroupOf W ≤ ballKernel F (base F true) 4 ∧
      16 ≤ Nat.card (ballKernel F (base F true) 2) ∧
      ballKernel F (base F true) 4 ≠ ⊥ := by
  let P := h.residual ⊔ (T : Subgroup G)
  let W := P ⊔ H
  let F : Bool → Subgroup W := fun i => if i then H.subgroupOf W else P.subgroupOf W
  obtain ⟨D,hn,hseed,_,_,_,_,hb,_,_⟩ := h.marked_five_symmetricThree_source_track hd hH he
  have hVH : V ≤ H := (h.prepared.inside_core H hH).trans (twoCore_le H)
  have hVW : V ≤ W := hVH.trans le_sup_right
  have hUW : conjugateSpan H V ≤ W := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact (conjugateSpanBy_le_self hVH).trans le_sup_right
  have hseed' : D.seed = V.subgroupOf W := by
    apply map_injective W.subtype_injective
    rw [hseed,map_subgroupOf_eq_of_le hVW]
  have hseed3 : D.seed ≤ ballKernel F (base F false) 3 :=
    (D.track_spec hn).2.1.trans (ballKernel_antitone F _ hb)
  have hspan : conjugateSpanBy D.seed (F true) = (conjugateSpan H V).subgroupOf W := by
    apply map_injective W.subtype_injective
    rw [map_conjugateSpanBy,hseed,
      show (F true).map W.subtype = H from map_subgroupOf_eq_of_le le_sup_right,
      map_subgroupOf_eq_of_le hUW,UniqueFactor.conjugateSpan_eq]
  have hU := conjugateSpan_le_opposite_ballKernel F D.seed 2 hseed3
  rw [hspan] at hU
  let Z := centralInvolutions T ⊓ V
  have hZW : Z ≤ W := inf_le_right.trans hVW
  have hZseed : Z.subgroupOf W ≤ D.seed := by
    rw [hseed']
    exact subgroupOf_mono W inf_le_right
  have hZH : Z.subgroupOf W ≤ F true := fun _ hx => hVH hx.2
  have hc : F true ≤ centralizer (Z.subgroupOf W : Set W) := by
    intro a ha z hz
    exact Subtype.ext ((source_centralizing_HStar_le_seed_centralizer
      h.ambient T h.maximal hH h.centralizing ha) z hz.1)
  have hZ := central_subgroup_le_opposite_ballKernel F D.generates
    (Z.subgroupOf W) 3 (hZseed.trans hseed3) hZH hc
  have hZne : Z ≠ ⊥ := by
    intro hz
    have hs := h.prepared.seed_span
    change V = conjugateSpanBy Z M at hs
    apply h.prepared.nontrivial
    rw [hs,hz]
    exact bot_unique (conjugateSpanBy_le bot_le (by
      rw [normalizer_eq_top]
      exact le_top))
  have hZne' : Z.subgroupOf W ≠ ⊥ := by
    intro hz
    have hh := congrArg (map W.subtype) hz
    rw [map_subgroupOf_eq_of_le hZW,Subgroup.map_bot] at hh
    exact hZne hh
  have hcard := card_le_of_le hU
  rw [Nat.card_congr (subgroupOfEquivOfLe hUW).toEquiv] at hcard
  exact ⟨hU,hZ,(h.symmetricThree_span_card hprior hH he).trans hcard,
    fun hh => hZne' (bot_unique (hZ.trans hh.le))⟩

/-- Odd track supplies an actual conjugate inside T but outside O₂(H),
with the conjugator in the original generated pair. -/
theorem ChosenSmallSource.marked_five_symmetricThree_escaping_conjugate
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    ∃ g : ((h.residual ⊔ (T : Subgroup G)) ⊔ H : Subgroup G),
      V.map (MulAut.conj (g : G)).toMonoidHom ≤ (T : Subgroup G) ∧
      ¬ V.map (MulAut.conj (g : G)).toMonoidHom ≤ H.pCoreIn 2 := by
  classical
  let P := h.residual ⊔ (T : Subgroup G)
  let W := P ⊔ H
  let F : Bool → Subgroup W := fun i => if i then H.subgroupOf W else P.subgroupOf W
  obtain ⟨D,hn,hseed,hsyl,_,_,hodd,_,_,_⟩ :=
    h.marked_five_symmetricThree_source_track hd hH he
  by_contra! hno
  have hclosure : ChapterE.indexedWeakClosure D.seed
      ((D.sylow false : Subgroup (F false)).map (F false).subtype) 0 ≤
      (F true).pCoreIn 2 := by
    rw [ChapterE.weakClosure_eq_sSup_gamma]
    apply sSup_le
    intro A hA
    obtain ⟨g,rfl,hT⟩ := (ChapterE.mem_gamma_zero_iff _ _ _).mp hA
    have hmap : (D.seed.map (MulAut.conj g).toMonoidHom).map W.subtype =
        V.map (MulAut.conj (g : G)).toMonoidHom := by
      have hf : W.subtype.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj (g : G)).toMonoidHom.comp W.subtype := by
        ext x
        rfl
      rw [map_map,hf,←map_map,hseed]
    have hT' := map_mono (f := W.subtype) hT
    rw [hmap,map_map,hsyl] at hT'
    have hcore := hno g hT'
    apply (map_le_map_iff_of_injective W.subtype_injective).mp
    rw [hmap,←AmalgamLocalCores.pCoreIn_map_of_injective 2 W.subtype W.subtype_injective,
      show (F true).map W.subtype = H from map_subgroupOf_eq_of_le le_sup_right]
    exact hcore
  exact (Nat.not_even_iff_odd.mpr hodd)
    (Completion.even_track_of_weakClosure_core F D hn hclosure)

end CFSG.Quasithin.Chapter15.Section02
