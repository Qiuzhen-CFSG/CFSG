module

public import Theory.Representation.KrullSchmidt

/-!
# Matching and selecting indecomposable summands in finite products

An indecomposable finite-dimensional module that splits from a finite product
splits from one factor. Its identity endomorphism is the sum of the composites
through the factors, and locality makes one composite a unit.

For a splitting `A × B ≃ ∀ i, V i` into indecomposable finite-dimensional
factors, `Module.exists_complementary_subfamily` assigns complementary subsets
of the original index type to `A` and `B`, retaining multiplicities. Inductively,
a chosen factor splits from one side; cancel it and select the remaining
factors. No finite-dimensionality assumptions on `A` and `B` are needed.

The source of the local-endomorphism and cancellation steps is
`Theory.Representation.KrullSchmidt`, implementing the classical finite-length
Krull--Schmidt argument.
-/

public section
noncomputable section

namespace Module

/-- An indecomposable summand of a finite product is a summand of one factor.
The family of factor modules may be dependent. -/
theorem IsSplitSummand.exists_factor
    {F R U I : Type*} {V : I → Type*} [Field F] [Ring R] [Algebra F R]
    [AddCommGroup U] [Module F U] [Module R U] [IsScalarTower F R U]
    [FiniteDimensional F U] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (hU : IsIndecomposable R U) (h : IsSplitSummand R U (∀ i, V i)) :
    ∃ i, IsSplitSummand R U (V i) := by
  classical
  let : IsLocalRing (Module.End R U) :=
    end_isLocalRing_of_isIndecomposable (F := F) hU
  let : IsDedekindFiniteMonoid (Module.End R U) :=
    end_isDedekindFiniteMonoid (F := F)
  obtain ⟨j, q, hqj⟩ := h
  let ji (i : I) : U →ₗ[R] V i := (LinearMap.proj i).comp j
  let qi (i : I) : V i →ₗ[R] U := q.comp (LinearMap.single R V i)
  have hsum : (∑ i, (qi i).comp (ji i)) = (1 : Module.End R U) := by
    ext u
    rw [LinearMap.sum_apply]
    change (∑ i, q (Pi.single i (j u i))) = u
    rw [← map_sum, LinearMap.sum_single_apply]
    exact DFunLike.congr_fun hqj u
  obtain ⟨i, hi⟩ := exists_isUnit_of_isUnit_sum
    (fun i => (qi i).comp (ji i)) (hsum ▸ isUnit_one)
  let t : Module.End R U := (qi i).comp (ji i)
  let e : U ≃ₗ[R] U := LinearEquiv.ofBijective t ((Module.End.isUnit_iff t).mp hi)
  refine ⟨i, ji i, e.symm.toLinearMap.comp (qi i), ?_⟩
  ext u
  change e.symm (t u) = u
  simp [e]

private theorem splitSummand_of_isUnit_comp
    {R U X : Type*} [Ring R]
    [AddCommGroup U] [Module R U] [AddCommGroup X] [Module R X]
    (a : U →ₗ[R] X) (b : X →ₗ[R] U) (h : IsUnit (b.comp a)) :
    IsSplitSummand R U X := by
  let t : U ≃ₗ[R] U := LinearEquiv.ofBijective (b.comp a)
    ((Module.End.isUnit_iff _).mp h)
  refine ⟨a, t.symm.toLinearMap.comp b, ?_⟩
  ext u
  exact t.symm_apply_apply u

/-- An indecomposable summand of a binary product splits from one side. -/
theorem IsSplitSummand.of_prod
    {F R U A B : Type*} [Field F] [Ring R] [Algebra F R]
    [AddCommGroup U] [Module F U] [Module R U] [IsScalarTower F R U]
    [FiniteDimensional F U]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (hU : IsIndecomposable R U) (h : IsSplitSummand R U (A × B)) :
    IsSplitSummand R U A ∨ IsSplitSummand R U B := by
  let : IsLocalRing (Module.End R U) :=
    end_isLocalRing_of_isIndecomposable (F := F) hU
  obtain ⟨j, q, hqj⟩ := h
  let ja := (LinearMap.fst R A B).comp j
  let jb := (LinearMap.snd R A B).comp j
  let qa := q.comp (LinearMap.inl R A B)
  let qb := q.comp (LinearMap.inr R A B)
  have hsum : qa.comp ja + qb.comp jb = (1 : Module.End R U) := by
    ext u
    change q ((j u).1, 0) + q (0, (j u).2) = u
    rw [← map_add]
    simpa using DFunLike.congr_fun hqj u
  exact (IsLocalRing.isUnit_or_isUnit_of_add_one hsum).elim
    (fun ha => Or.inl (splitSummand_of_isUnit_comp ja qa ha))
    (fun hb => Or.inr (splitSummand_of_isUnit_comp jb qb hb))

private def piSplitAtLinearEquiv
    {R I : Type*} [Ring R] (V : I → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] (i : I) :
    (∀ j, V j) ≃ₗ[R] V i × (∀ j : {j // j ≠ i}, V j.val) := by
  classical
  exact { Equiv.piSplitAt i V with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

private theorem extend_selection
    {R I : Type*} [Ring R] (V : I → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (i : I) (t : Set {j // j ≠ i}) :
    ∃ s : Set I,
      Nonempty ((V i × (∀ j : t, V j.val.val)) ≃ₗ[R] (∀ j : s, V j.val)) ∧
      Nonempty ((∀ j : ↥(tᶜ), V j.val.val) ≃ₗ[R] (∀ j : ↥(sᶜ), V j.val)) := by
  classical
  let s : Set I := {j | j = i ∨ ∃ h : j ≠ i, (⟨j, h⟩ : {j // j ≠ i}) ∈ t}
  have hi : i ∈ s := Or.inl rfl
  let k : s := ⟨i, hi⟩
  let f : t ≃ {j : s // j ≠ k} :=
    { toFun := fun j => ⟨⟨j.val.val, Or.inr ⟨j.val.property, j.property⟩⟩,
        fun h => j.val.property (congrArg (fun x : s => x.val) h)⟩
      invFun := fun j =>
        have hn : j.val.val ≠ i := fun h => j.property (Subtype.ext h)
        ⟨⟨j.val.val, hn⟩, by
          rcases j.val.property with h | ⟨h, ht⟩
          · exact (hn h).elim
          · exact ht⟩
      left_inv := by intro j; rfl
      right_inv := by intro j; rfl }
  let g : ↥(tᶜ) ≃ ↥(sᶜ) :=
    { toFun := fun j => ⟨j.val.val, by
        rintro (h | ⟨h, ht⟩)
        · exact j.val.property h
        · exact j.property ht⟩
      invFun := fun j =>
        ⟨⟨j.val, fun h => j.property (Or.inl h)⟩,
          fun ht => j.property (Or.inr ⟨_, ht⟩)⟩
      left_inv := by intro j; rfl
      right_inv := by intro j; rfl }
  refine ⟨s, ⟨?_, ?_⟩⟩
  · exact ⟨((LinearEquiv.refl R (V i)).prodCongr
      (LinearEquiv.piCongrLeft R (fun j : {j : s // j ≠ k} => V j.val.val) f)).trans
        (piSplitAtLinearEquiv (R := R) (fun j : s => V j.val) k).symm⟩
  · exact ⟨LinearEquiv.piCongrLeft R (fun j : ↥(sᶜ) => V j.val) g⟩

/-- Finite Krull--Schmidt summand selection: a splitting of a finite product of
indecomposable finite-dimensional modules partitions the given indexed family.
The indexing retains multiplicities, and the two selected families are complementary. -/
theorem exists_complementary_subfamily
    {F R I A B : Type*} {V : I → Type*}
    [Field F] [Ring R] [Algebra F R] [Finite I]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)] [∀ i, Module R (V i)]
    [∀ i, IsScalarTower F R (V i)] [∀ i, FiniteDimensional F (V i)]
    (hV : ∀ i, IsIndecomposable R (V i))
    (e : (A × B) ≃ₗ[R] (∀ i, V i)) :
    ∃ s : Set I, Nonempty (A ≃ₗ[R] (∀ i : s, V i.val)) ∧
      Nonempty (B ≃ₗ[R] (∀ i : ↥(sᶜ), V i.val)) := by
  classical
  let := Fintype.ofFinite I
  induction hn : Nat.card I using Nat.strong_induction_on generalizing I A B with
  | h n ih =>
    cases isEmpty_or_nonempty I with
    | inl hempty =>
      let := hempty
      let : Subsingleton A := ⟨fun a b => by
        have h : e (a, 0) = e (b, 0) := Subsingleton.elim _ _
        exact congrArg Prod.fst (e.injective h)⟩
      let : Subsingleton B := ⟨fun a b => by
        have h : e (0, a) = e (0, b) := Subsingleton.elim _ _
        exact congrArg Prod.snd (e.injective h)⟩
      exact ⟨∅, ⟨LinearEquiv.ofSubsingleton _ _⟩, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
    | inr hnonempty =>
      obtain ⟨i⟩ := hnonempty
      let J := {j : I // j ≠ i}
      let d := piSplitAtLinearEquiv (R := R) V i
      have hsplit : IsSplitSummand R (V i) (A × B) := by
        refine ⟨e.symm.toLinearMap.comp (LinearMap.single R V i),
          (LinearMap.proj i).comp e.toLinearMap, ?_⟩
        ext x
        simp
      have hlocal := end_isLocalRing_of_isIndecomposable (F := F) (hV i)
      have hlt : Nat.card J < n := by
        rw [← hn, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact Fintype.card_subtype_lt (x := i) (by simp)
      rcases hsplit.of_prod (F := F) (hV i) with ha | hb
      · obtain ⟨C, ⟨a⟩⟩ := ha.exists_linearEquiv_prod
        let d' : (V i × (C × B)) ≃ₗ[R] (V i × (∀ j : J, V j.val)) :=
          (LinearEquiv.prodAssoc R (V i) C B).symm.trans
            ((a.prodCongr (LinearEquiv.refl R B)).trans (e.trans d))
        obtain ⟨e'⟩ := linearEquiv_cancel_of_end_isLocalRing (F := F) hlocal d'
        obtain ⟨t, ⟨ea⟩, ⟨eb⟩⟩ := ih (Nat.card J) hlt
          (hV := fun j : J => hV j.val) e' rfl
        obtain ⟨s, ⟨es⟩, ⟨ec⟩⟩ := extend_selection (R := R) V i t
        exact ⟨s, ⟨a.symm.trans (((LinearEquiv.refl R _).prodCongr ea).trans es)⟩,
          ⟨eb.trans ec⟩⟩
      · obtain ⟨C, ⟨b⟩⟩ := hb.exists_linearEquiv_prod
        let rearrange : (V i × (A × C)) ≃ₗ[R] (A × (V i × C)) :=
          (LinearEquiv.prodAssoc R (V i) A C).symm.trans
            (((LinearEquiv.prodComm R (V i) A).prodCongr (LinearEquiv.refl R C)).trans
              (LinearEquiv.prodAssoc R A (V i) C))
        let d' : (V i × (A × C)) ≃ₗ[R] (V i × (∀ j : J, V j.val)) :=
          rearrange.trans (((LinearEquiv.refl R A).prodCongr b).trans (e.trans d))
        obtain ⟨e'⟩ := linearEquiv_cancel_of_end_isLocalRing (F := F) hlocal d'
        obtain ⟨t, ⟨ea⟩, ⟨eb⟩⟩ := ih (Nat.card J) hlt
          (hV := fun j : J => hV j.val) e' rfl
        obtain ⟨s, ⟨es⟩, ⟨ec⟩⟩ := extend_selection (R := R) V i tᶜ
        refine ⟨sᶜ, ?_, ?_⟩
        · let et := LinearEquiv.piCongrLeft R
            (fun j : ↥(tᶜᶜ) => V j.val.val) (Equiv.setCongr (compl_compl t).symm)
          exact ⟨ea.trans (et.trans ec)⟩
        · let et := LinearEquiv.piCongrLeft R
            (fun j : ↥(sᶜᶜ) => V j.val) (Equiv.setCongr (compl_compl s).symm)
          exact ⟨b.symm.trans
            (((LinearEquiv.refl R _).prodCongr eb).trans (es.trans et))⟩

/-- An idempotent on a finite product of indecomposable modules becomes a
coordinate projection after a module automorphism. -/
theorem exists_equiv_pi_of_idempotent
    {F R I M : Type*} {V : I → Type*}
    [Field F] [Ring R] [Algebra F R] [Finite I]
    [AddCommGroup M] [Module R M]
    [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)] [∀ i, Module R (V i)]
    [∀ i, IsScalarTower F R (V i)] [∀ i, FiniteDimensional F (V i)]
    (hV : ∀ i, IsIndecomposable R (V i))
    (e : M ≃ₗ[R] (∀ i, V i)) (P : Module.End R M) (hP : IsIdempotentElem P) :
    ∃ (s : Set I) (d : M ≃ₗ[R] (∀ i, V i)),
      ∀ (v : M) (i : I),
        (i ∈ s → d (P v) i = d v i) ∧ (i ∉ s → d (P v) i = 0) := by
  classical
  let a := P.range.prodEquivOfIsCompl P.ker (LinearMap.IsIdempotentElem.isCompl hP)
  obtain ⟨s, ⟨ea⟩, ⟨eb⟩⟩ := exists_complementary_subfamily (F := F) hV (a.trans e)
  let b : (∀ i, V i) ≃ₗ[R] ((∀ i : s, V i.val) × (∀ i : ↥(sᶜ), V i.val)) :=
    { Equiv.piEquivPiSubtypeProd (· ∈ s) V with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let d := a.symm.trans ((ea.prodCongr eb).trans b.symm)
  refine ⟨s, d, ?_⟩
  have hp (v : M) : a.symm (P v) = ((a.symm v).1, 0) := by
    apply a.injective
    have hv := a.apply_symm_apply v
    have hfix : P ((a.symm v).1 : M) = (a.symm v).1 :=
      (LinearMap.IsIdempotentElem.mem_range_iff hP).mp (a.symm v).1.property
    have hzero : P ((a.symm v).2 : M) = 0 := (a.symm v).2.property
    rw [a.apply_symm_apply]
    change P v = (a.symm v).1.val + 0
    calc
      P v = P (a (a.symm v)) := congrArg P hv.symm
      _ = _ := by rw [Submodule.coe_prodEquivOfIsCompl', map_add, hfix, hzero]
  intro v i
  have h := congrArg (fun w => b.symm ((ea.prodCongr eb) w)) (hp v)
  change d (P v) = b.symm (ea (a.symm v).1, eb 0) at h
  rw [map_zero] at h
  rw [h]
  constructor
  · intro hi
    simp [b, Equiv.piEquivPiSubtypeProd, hi, d]
  · intro hi
    simp [b, Equiv.piEquivPiSubtypeProd, hi]

end Module
