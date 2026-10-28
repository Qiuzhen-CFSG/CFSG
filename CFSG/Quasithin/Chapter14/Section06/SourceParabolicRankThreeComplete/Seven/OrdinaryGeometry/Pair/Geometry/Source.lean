module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Pair.Inputs
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Pair.Geometry.Certificates

/-!
# The ordinary seven-letter plane and its original fixed point

The source residual makes all three nonzero plane vectors conjugate, hence of
equal weight. Small checked certificates identify the invariant plane in each
partition orientation. A common even involution identifies its fixed point.
The normalizer of the standard plane is exactly the three-pair centralizer:
the two coordinate rows recover its pairs and its unique remaining letter.

This proves the finite module input without a parabolic marking assumption
beyond the explicitly supplied permutation subgroups. The source transport
uses fixation of the original point to rule out the reversed orientation.
Source: Aschbacher--Smith, original14.6.10(5), printed p.1029.
-/

@[expose] public section
open Subgroup Equiv Module BinaryPermutation BinaryPermutation.SevenParabolic
open BinaryPermutation.SevenParabolic.Ordinary
namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.FiniteGeometry
private local instance : DecidablePred (fun v : Full (Fin 7) => v ∈ core (Fin 7)) :=
  fun v => inferInstanceAs (Decidable ((augmentation (Fin 7)) v = 0))
private local instance : Fintype Space :=
  Fintype.ofFinset (Finset.univ.filter fun v => v ∈ core (Fin 7)) (by simp)
private instance (u v w : Space) : Decidable (inPlane u v w) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
private lemma mem_span_iff (u v w : Space) :
    w ∈ Submodule.span (ZMod 2) {u,v} ↔ inPlane u v w := by
  constructor
  · intro hw
    obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hw
    have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases hc a with rfl | rfl <;> rcases hc b with rfl | rfl <;> simp [inPlane]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_insert _ _))
        (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

private lemma plane_card :
    Nat.card (Submodule.span (ZMod 2) {firstFour,secondFour}) = 4 := by
  let e : Submodule.span (ZMod 2) {firstFour,secondFour} ≃
      {v : Space // inPlane firstFour secondFour v} :=
    Equiv.subtypeEquivRight (fun v => mem_span_iff firstFour secondFour v)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

private lemma plane_le_of_cert (P : Submodule (ZMod 2) Space)
    (hcard : Nat.card P = 4)
    (hw : ∀ u ∈ P, u ≠ 0 → ∀ v ∈ P, v ≠ 0 → weight u = weight v)
    (a b c : Perm (Fin 7)) (x y : Space)
    (hi : ∀ g ∈ ({a,b,c} : Set (Perm (Fin 7))), ∀ v ∈ P, action g v ∈ P)
    (cert : ∀ u v : Space,
      u ≠ 0 → v ≠ 0 → u ≠ v → weight v = weight u → weight (u+v) = weight u →
      preservesPair a u v → preservesPair b u v → preservesPair c u v →
      inPlane x y u ∧ inPlane x y v) :
    P ≤ Submodule.span (ZMod 2) {x,y} := by
  have hd : Module.finrank (ZMod 2) P = 2 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := P)
    rw [Nat.card_zmod,hcard] at hh
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hh.symm
  let e : Basis (Fin 2) (ZMod 2) P := (Module.finBasis (ZMod 2) P).reindex (finCongr hd)
  let u : Space := e 0
  let v : Space := e 1
  have hu : u ≠ 0 := fun h => e.ne_zero 0 (Subtype.ext h)
  have hv : v ≠ 0 := fun h => e.ne_zero 1 (Subtype.ext h)
  have huv : u ≠ v := fun h => by
    have h01 := e.injective (Subtype.ext h)
    exact (by decide : (0 : Fin 2) ≠ 1) h01
  have huv0 : u+v ≠ 0 := by
    intro hz
    apply huv
    have he := congrArg (fun w : Space => w+v) hz
    have htwo : v+v = 0 := by
      simpa only [show (2 : ZMod 2) = 0 from by decide,zero_smul] using
        (two_smul (ZMod 2) v).symm
    simpa only [add_assoc,htwo,add_zero,zero_add] using he
  have hspan : P = Submodule.span (ZMod 2) {u,v} := by
    have hh := congrArg (Submodule.map P.subtype) e.span_eq
    rw [Submodule.map_span,Submodule.map_top,Submodule.range_subtype] at hh
    have hs : Set.range (fun i : Fin 2 => (e i : Space)) = {u,v} := by
      ext w
      constructor
      · rintro ⟨i,rfl⟩
        fin_cases i <;> simp [u,v]
      · rintro (rfl | rfl)
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
    rw [←Set.range_comp] at hh
    change Submodule.span (ZMod 2) (Set.range (fun i : Fin 2 => (e i : Space))) = P at hh
    rw [hs] at hh
    exact hh.symm
  have hp (g : Perm (Fin 7)) (hg : g ∈ ({a,b,c} : Set (Perm (Fin 7)))) :
      preservesPair g u v :=
    ⟨(mem_span_iff u v _).mp (hspan ▸ hi g hg u (e 0).property),
      (mem_span_iff u v _).mp (hspan ▸ hi g hg v (e 1).property)⟩
  obtain ⟨huD,hvD⟩ := cert u v hu hv huv
    (hw v (e 1).property hv u (e 0).property hu)
    (hw (u+v) (P.add_mem (e 0).property (e 1).property) huv0 u (e 0).property hu)
    (hp a (by simp)) (hp b (by simp)) (hp c (by simp))
  rw [hspan]
  apply Submodule.span_le.mpr
  rintro w (rfl | rfl)
  · exact (mem_span_iff x y _).mpr huD
  · exact (mem_span_iff x y _).mpr hvD

private lemma lambda_gens :
    ∀ g ∈ ({pairRotate,doubleSwap,pairExchange} : Set (Perm (Fin 7))),
      g ∈ alternatingGroup (Fin 7) ∧ g ∈ lambda := by
  rintro g (rfl | rfl | rfl)
  all_goals constructor
  all_goals first
    | (rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel)
    | (rw [lambda,mem_centralizer_singleton_iff]; decide +kernel)

private lemma theta_gens :
    ∀ g ∈ ({complementCycle,mixedSwap,pairExchange} : Set (Perm (Fin 7))),
      g ∈ alternatingGroup (Fin 7) ∧ g ∈ theta := by
  rintro g (rfl | rfl | rfl)
  all_goals constructor
  all_goals first
    | (rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel)
    | (rw [theta,mem_centralizer_singleton_iff]; decide +kernel)

private lemma common_gens :
    ∀ g ∈ ({mixedSwap,pairExchange} : Set (Perm (Fin 7))),
      g ∈ alternatingGroup (Fin 7) ∧ g ∈ lambda ∧ g ∈ theta := by
  rintro g (rfl | rfl)
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel)
    | (rw [lambda,mem_centralizer_singleton_iff]; decide +kernel)
    | (rw [theta,mem_centralizer_singleton_iff]; decide +kernel)

private lemma lambda_point_cert (z : Space) :
    inPlane firstFour secondFour z → z ≠ 0 → action pairExchange z = z → z = firstFour :=
  (by decide +kernel : ∀ z : Space,
    inPlane firstFour secondFour z → z ≠ 0 → action pairExchange z = z → z = firstFour) z

private lemma theta_point_cert (z : Space) :
    inPlane pair56 pair57 z → z ≠ 0 → action mixedSwap z = z → z = pair56 :=
  (by decide +kernel : ∀ z : Space,
    inPlane pair56 pair57 z → z ≠ 0 → action mixedSwap z = z → z = pair56) z

private lemma coordinates (w : Space) (hw : inPlane firstFour secondFour w) :
    (∀ i : Fin 7, w.val (tripleSwap i) = w.val i) ∧ w.val 6 = 0 :=
  (by decide +kernel : ∀ w : Space, inPlane firstFour secondFour w →
    (∀ i : Fin 7, w.val (tripleSwap i) = w.val i) ∧ w.val 6 = 0) w hw
private lemma code_zero (i : Fin 7) : firstFour.val i = 0 → secondFour.val i = 0 → i = 6 :=
  (by decide : ∀ i : Fin 7, firstFour.val i = 0 → secondFour.val i = 0 → i = 6) i
private lemma code_pair (i j : Fin 7) : i ≠ j →
    firstFour.val i = firstFour.val j → secondFour.val i = secondFour.val j → tripleSwap i = j :=
  (by decide : ∀ i j : Fin 7, i ≠ j →
    firstFour.val i = firstFour.val j → secondFour.val i = secondFour.val j → tripleSwap i = j) i j
private lemma paired_weight_four (w : Space) :
    (∀ i : Fin 7, w.val (tripleSwap i) = w.val i) → weight w = 4 →
      inPlane firstFour secondFour w :=
  (by decide +kernel : ∀ w : Space,
    (∀ i : Fin 7, w.val (tripleSwap i) = w.val i) → weight w = 4 →
      inPlane firstFour secondFour w) w

private lemma stabilizer (g : Perm (Fin 7)) :
    (∀ v ∈ Submodule.span (ZMod 2) {firstFour,secondFour},
      action g v ∈ Submodule.span (ZMod 2) {firstFour,secondFour}) ↔ g ∈ lambda := by
  constructor
  · intro hi
    have h1 := coordinates _ ((mem_span_iff _ _ _).mp
      (hi firstFour (Submodule.subset_span (Set.mem_insert _ _))))
    have h2 := coordinates _ ((mem_span_iff _ _ _).mp
      (hi secondFour (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))
    have h6 : g.symm 6 = 6 := code_zero _ h1.2 h2.2
    have hc (i : Fin 7) : tripleSwap (g.symm i) = g.symm (tripleSwap i) := by
      by_cases he : tripleSwap i = i
      · have hi6 := (tripleSwap_fixed i).mp he
        subst i
        rw [h6,show tripleSwap 6 = 6 by decide,h6]
      · exact code_pair _ _ (fun hh => he (g.symm.injective hh).symm)
          (h1.1 i).symm (h2.1 i).symm
    have hm : g⁻¹ ∈ lambda := by
      rw [lambda,mem_centralizer_singleton_iff]
      exact Equiv.ext (fun i => (hc i).symm)
    exact inv_mem_iff.mp hm
  · intro hg
    have hc (i : Fin 7) : g.symm (tripleSwap i) = tripleSwap (g.symm i) :=
      congrArg (fun p : Perm (Fin 7) => p i)
        (mem_centralizer_singleton_iff.mp (lambda.inv_mem hg))
    change Submodule.span (ZMod 2) {firstFour,secondFour} ≤
      (Submodule.span (ZMod 2) {firstFour,secondFour}).comap (action g)
    apply Submodule.span_le.mpr
    rintro v (rfl | rfl)
    all_goals
      apply (mem_span_iff _ _ _).mpr
      apply paired_weight_four
    · intro i
      change firstFour.val (g.symm (tripleSwap i)) = firstFour.val (g.symm i)
      rw [hc]
      exact (coordinates firstFour (Or.inr (Or.inl rfl))).1 _
    · rw [weight_permute]
      exact firstFour_weight
    · intro i
      change secondFour.val (g.symm (tripleSwap i)) = secondFour.val (g.symm i)
      rw [hc]
      exact (coordinates secondFour (Or.inr (Or.inr (Or.inl rfl)))).1 _
    · rw [weight_permute]
      decide

private lemma weights {A : Subgroup (Perm (Fin 7))} {P : Submodule (ZMod 2) Space}
    (h : TransitivePlane A P) :
    ∀ u ∈ P, u ≠ 0 → ∀ v ∈ P, v ≠ 0 → weight u = weight v := by
  intro u hu hu0 v hv hv0
  obtain ⟨a,_,he⟩ := h.2 u hu hu0 v hv hv0
  exact (weight_permute a u).symm.trans (congrArg weight he)

theorem recognition : PlaneRecognition where
  lambda_plane J P z hJ hP hi hz hn hf := by
    have hle := plane_le_of_cert P hP (weights hi) pairRotate doubleSwap pairExchange
      firstFour secondFour (fun g hg => hi.1 g ⟨hJ (lambda_gens g hg).1,(lambda_gens g hg).2⟩)
      lambda_cert
    have he : P = Submodule.span (ZMod 2) {firstFour,secondFour} :=
      Submodule.toAddSubgroup_injective
        (AddSubgroup.eq_of_le_of_card_ge hle (by
          change Nat.card (Submodule.span (ZMod 2) {firstFour,secondFour}) ≤ Nat.card P
          rw [hP,plane_card]))
    refine ⟨he,lambda_point_cert z ((mem_span_iff _ _ _).mp (hle hz)) hn ?_⟩
    have hg := common_gens pairExchange (by simp)
    exact hf ⟨⟨hJ hg.1,hg.2.1⟩,hg.2.2⟩
  theta_point J P z hJ hP hi hz hn hf := by
    have hle := plane_le_of_cert P hP (weights hi) complementCycle mixedSwap pairExchange
      pair56 pair57 (fun g hg => hi.1 g ⟨hJ (theta_gens g hg).1,(theta_gens g hg).2⟩)
      theta_cert
    apply theta_point_cert z ((mem_span_iff _ _ _).mp (hle hz)) hn
    have hg := common_gens mixedSwap (by simp)
    exact hf ⟨⟨hJ hg.1,hg.2.1⟩,hg.2.2⟩
  stabilizer := stabilizer

end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.FiniteGeometry
