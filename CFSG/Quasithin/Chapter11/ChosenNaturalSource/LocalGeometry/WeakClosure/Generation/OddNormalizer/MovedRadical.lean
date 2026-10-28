module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedJankoCentralizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedNormalizer
public import Theory.GroupTheory.PRadicalSylowNormalizer

/-!
# The radical and maximal two-local attached to the actual moved residual

The original module is mapped through the literal component embedding and its
central quotient. It remains nonzero, elementary and fully moved by the same
projected residual, so that residual has a nontrivial two-core.

Enlarge this two-core to a radical subgroup without shrinking its normalizer.
The established two-local control gives equality with the full residual
normalizer. Consequently the radical is precisely O₂(N(X)), and N(X) is maximal
among two-locals. This does not assert that N(X) contains an ambient Sylow.

These are the actual local objects used in the remaining J₄ inspection of
Aschbacher--Smith 4.4.7 and the proof of 4.4.3, printed pp.620,622. Source and
its literal Hall-kernel application retain the original module and full cover.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private def inclusionIntoAmbient (A : Subgroup G)
    (K : Subgroup (normalizer (A : Set G))) : K →* G :=
  (normalizer (A : Set G)).subtype.comp K.subtype

omit [Finite G] in
private theorem inclusionIntoAmbient_injective (A : Subgroup G)
    (K : Subgroup (normalizer (A : Set G))) :
    Function.Injective (inclusionIntoAmbient A K) :=
  (normalizer (A : Set G)).subtype_injective.comp K.subtype_injective

omit [Finite G] in
private theorem component_map {A B : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (h : B ≤ K.map (normalizer (A : Set G)).subtype) :
    (movedComponentSubgroup A B K).map (inclusionIntoAmbient A K) = B := by
  have hb : B.subgroupOf (normalizer (A : Set G)) ≤ K := by
    intro b hb
    obtain ⟨k,hk,he⟩ := h hb
    exact (Subtype.ext he : k = b) ▸ hk
  rw [inclusionIntoAmbient,←map_map,map_subgroupOf_eq_of_le hb,
    map_subgroupOf_eq_of_le (h.trans (map_subtype_le _))]

/-- Central projection preserves a nonzero fully moved image of the original V.
All subgroups and maps use the selected component of the original N_G(A). -/
theorem moved_projected_module
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A)) (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    let q := QuotientGroup.mk' (center K)
    let X := (movedComponentSubgroup A (oddActorResidual L A) K).map q
    let U := (movedComponentSubgroup A V K).map q
    IsElementaryAbelian 2 U ∧ U ≠ ⊥ ∧ U ≤ X.pCoreIn 2 ∧ U = ⁅U,X⁆ := by
  let F := oddActorResidual L A
  let Y := movedComponentSubgroup A F K
  let E := movedComponentSubgroup A V K
  let q := QuotientGroup.mk' (center K)
  obtain ⟨hc,hm,hVc,_⟩ := actor_cover D S hA hodd
  have hVF : V ≤ F := hVc.trans (pCoreIn_le 2 F)
  have hVK := hVF.trans hFK
  have hmove : E = ⁅E,Y⁆ := by
    apply map_injective (inclusionIntoAmbient_injective A K)
    rw [map_commutator,component_map K hVK,component_map K hFK]
    exact hm
  have hE : IsElementaryAbelian 2 E := by
    let := D.elementary
    let j : E →* V := {
      toFun v := ⟨v.val.val.val,v.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact IsElementaryAbelian.of_injective j (by
      intro x y h
      have hg : x.val.val.val = y.val.val.val := congrArg (fun v : V => (v : G)) h
      exact Subtype.ext (Subtype.ext (Subtype.ext hg)))
  have hU : IsElementaryAbelian 2 (E.map q) := by
    let := hE
    exact IsElementaryAbelian.map q
  have hUm : E.map q = ⁅E.map q,Y.map q⁆ := by rw [←map_commutator,←hmove]
  have hne : E.map q ≠ ⊥ := by
    intro hz
    have hec : E ≤ center K := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff E).mp hz
    have he : E = ⊥ := by
      rw [hmove]
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro v hv y hy
      exact mem_center_iff.mp (hec hv) y
    have hv := component_map K hVK
    change E.map (inclusionIntoAmbient A K) = V at hv
    rw [he,Subgroup.map_bot] at hv
    exact D.ne_bot hv.symm
  have hUX : E.map q ≤ Y.map q := map_mono (fun _ hv => hVF hv)
  have hn : Y.map q ≤ normalizer (E.map q : Set (K ⧸ center K)) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [commutator_comm,←hUm]
  exact ⟨hU,hne,le_pCoreIn_of_normalizes hU.isPGroup hUX hn,hUm⟩

private theorem residual_radical {Q : Type*} [Group Q] [Finite Q]
    (X : Subgroup Q) (hne : X.pCoreIn 2 ≠ ⊥)
    (hlocal : ∀ B : Subgroup Q, IsPGroup 2 B → B ≠ ⊥ →
      X ≤ normalizer (B : Set Q) → normalizer (B : Set Q) ≤ normalizer (X : Set Q)) :
    IsPRadical 2 ((normalizer (X : Set Q)).pCoreIn 2) ∧
      normalizer ((normalizer (X : Set Q)).pCoreIn 2 : Set Q) =
        normalizer (X : Set Q) ∧ IsMaximalTwoLocal (normalizer (X : Set Q)) := by
  obtain ⟨P,hP,hXP,hNP⟩ := exists_isPRadical_of_isPGroup (X.pCoreIn 2)
    (isPGroup_pCoreIn 2 X) hne
  have hn : normalizer (X : Set Q) ≤ normalizer (P : Set Q) :=
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X)).trans hNP
  have he : normalizer (P : Set Q) = normalizer (X : Set Q) :=
    le_antisymm (hlocal P hP.isPGroup hP.1 (X.le_normalizer.trans hn)) hn
  have hp : (normalizer (X : Set Q)).pCoreIn 2 = P := by
    rw [←he]
    exact hP.2
  refine ⟨hp.symm ▸ hP,?_,?_⟩
  · rw [hp,he]
  · refine ⟨⟨P,hP.1,hP.isPGroup,he.symm⟩,?_⟩
    intro M hM hXM
    obtain ⟨B,hB,hBp,rfl⟩ := hM
    exact hlocal B hBp hB (X.le_normalizer.trans hXM)

/-- The full projected residual normalizer is a maximal two-local, and its
intrinsic two-core is a radical with exactly that full normalizer. -/
theorem moved_projected_radical
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    let X := (movedComponentSubgroup A (oddActorResidual L A) K).map
      (QuotientGroup.mk' (center K))
    let P := (normalizer (X : Set (K ⧸ center K))).pCoreIn 2
    IsPRadical 2 P ∧ normalizer (P : Set (K ⧸ center K)) =
      normalizer (X : Set (K ⧸ center K)) ∧
      IsMaximalTwoLocal (normalizer (X : Set (K ⧸ center K))) := by
  obtain ⟨hU,hne,hUc,hm⟩ := moved_projected_module D S hA hodd K hFK
  apply residual_radical _ (fun hz => hne (bot_unique (hz ▸ hUc)))
  exact moved_projected_two_normalizer hu K hFK

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
