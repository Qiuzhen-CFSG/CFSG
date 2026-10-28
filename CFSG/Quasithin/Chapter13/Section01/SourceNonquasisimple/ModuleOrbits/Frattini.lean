module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Action
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.TI

/-!
# Comparing the actual odd Frattini and moved-module actions

The canonical odd radical's Frattini action has a proper kernel on L:
the original Sylow intersection already has a faithful quaternion image.
C-component minimality therefore puts this kernel in O∞(L). Since
O∞(L) is exactly the moved-module kernel, the latter action factors
through the former. We retain the resulting surjection and its equation
on each original element of L. In particular noncommutativity of a
point-centralizer image on U is detected by its odd Frattini action.

Source: Aschbacher--Smith, proof of 13.1.12(1), printed p.872.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Chapter1 Chapter1.Section02 Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Restricting the actor keeps both characteristic quotient maps unchanged. -/
theorem xiFrattiniAction_restrict {A B X : Subgroup G}
    (hAB : A ≤ B) (hB : B ≤ normalizer (X : Set G)) (a : A) :
    xiFrattiniAction A X (hAB.trans hB) a =
      xiFrattiniAction B X hB (inclusion hAB a) := by
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with | H x =>
    induction x using QuotientGroup.induction_on with | H x => rfl

/-- The Frattini-action kernel on L is solvable, for every original odd radical. -/
theorem component_frattini_kernel_le_radical
    {T : Sylow 2 G} (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    (xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)).ker ≤
      solvableRadical L := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  let σ := xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)
  let r := xiFrattiniAction ((T : Subgroup G) ⊓ L) (XiP p L)
    (inf_le_right.trans (XiP_invariant p L.le_normalizer))
  obtain ⟨f,hf⟩ := (RadicalActions.XiP_intersection_actions_of_A36 h36 hL
    (uniqueness_local_quotient_sqtk hG hL.2.2) hn ho hd).2
  have hk : σ.ker ≠ ⊤ := by
    intro hk
    have hr (t : ((T : Subgroup G) ⊓ L : Subgroup G)) : r t = 1 := by
      rw [show r t = σ (inclusion inf_le_right t) from
        xiFrattiniAction_restrict inf_le_right (XiP_invariant p L.le_normalizer) t]
      apply MonoidHom.mem_ker.mp
      rw [hk]
      exact mem_top _
    have hz (a : r.range) : a = 1 := by
      apply Subtype.ext
      obtain ⟨t,ht⟩ := a.property
      exact ht.symm.trans (hr t)
    let : Subsingleton r.range := ⟨fun a b => (hz a).trans (hz b).symm⟩
    exact not_subsingleton (QuaternionGroup 2) hf.subsingleton
  have ht : (⊤ : Subgroup L).IsCComponent := by
    simpa only [subgroupOf_self] using hL.1.subgroupOf_of_le le_rfl le_sup_left
  exact kernel_le_solvableRadical_of_top_isCComponent ht σ hk

/-- The literal moved action is a quotient of the odd Frattini action;
the homomorphism commutes with the original maps from L. -/
theorem moved_action_factors_frattini
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    let σ := xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)
    ∃ f : σ.range →* componentImage L, Function.Surjective f ∧
      ∀ l : L, f (σ.rangeRestrict l) = (componentAction L).rangeRestrict l := by
  let σ := xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)
  have hk : σ.rangeRestrict.ker ≤ (componentAction L).rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict,MonoidHom.ker_rangeRestrict,
      componentAction_ker_eq_radical h hmany hL hn]
    exact component_frattini_kernel_le_radical h.simpleQTKE hL.1.1 hn ho hd
  let f : σ.range →* componentImage L := σ.rangeRestrict.liftOfSurjective
    σ.rangeRestrict_surjective ⟨(componentAction L).rangeRestrict,hk⟩
  have he (l : L) : f (σ.rangeRestrict l) = (componentAction L).rangeRestrict l := by
    simp [f]
    rfl
  refine ⟨f,?_,he⟩
  intro y
  obtain ⟨l,rfl⟩ := (componentAction L).rangeRestrict_surjective y
  exact ⟨σ.rangeRestrict l,he l⟩

/-- Noncommutativity in the actual moved-module centralizer image survives
in the literal radical action. No irreducibility assertion is assumed. -/
theorem centralizer_frattini_image_not_commutative
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : G)
    (hnc : ¬ IsMulCommutative
      (((centralizer ({u} : Set G)).subgroupOf L).map (componentAction L))) :
    ¬ IsMulCommutative (xiFrattiniAction
      (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) (XiP p L)
      (XiP_invariant p inf_le_left)).range := by
  obtain ⟨f,_,hf⟩ := moved_action_factors_frattini h hmany hL hn ho hd
  let σ := xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)
  let C := normalizer (L : Set G) ⊓ centralizer ({u} : Set G)
  let τ := xiFrattiniAction C (XiP p L) (XiP_invariant p inf_le_left)
  intro hc
  apply hnc
  apply isMulCommutative_iff.mpr
  intro a b
  obtain ⟨l,hl,hel⟩ := a.property
  obtain ⟨k,hk,hek⟩ := b.property
  let lC : C := ⟨l,L.le_normalizer l.property,hl⟩
  let kC : C := ⟨k,L.le_normalizer k.property,hk⟩
  have he (x : L) (hx : (x : G) ∈ centralizer ({u} : Set G)) :
      τ ⟨x,L.le_normalizer x.property,hx⟩ = σ x := by
    apply MulEquiv.ext
    intro v
    induction v using QuotientGroup.induction_on with | H v =>
      induction v using QuotientGroup.induction_on with | H v => rfl
  have hh := congrArg Subtype.val
    ((isMulCommutative_iff.mp hc) (τ.rangeRestrict lC) (τ.rangeRestrict kC))
  change τ lC * τ kC = τ kC * τ lC at hh
  rw [he l hl,he k hk] at hh
  have hh' : σ.rangeRestrict l * σ.rangeRestrict k =
      σ.rangeRestrict k * σ.rangeRestrict l := Subtype.ext hh
  have hf' (x : L) : (f (σ.rangeRestrict x) : MulAut (normalizerMoved L)) =
      componentAction L x := congrArg Subtype.val (hf x)
  have hh'' := congrArg (fun x => (f x : MulAut (normalizerMoved L))) hh'
  simp only [map_mul,Subgroup.coe_mul] at hh''
  rw [hf' l,hf' k] at hh''
  apply Subtype.ext
  change (a : MulAut (normalizerMoved L))*(b : MulAut (normalizerMoved L)) = _
  rwa [hel,hek] at hh''

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
