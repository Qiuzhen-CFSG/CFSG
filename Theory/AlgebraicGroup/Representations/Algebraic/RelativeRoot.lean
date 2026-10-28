module

public import Theory.AlgebraicGroup.Representations.Algebraic.HighestWeight
public import Theory.AlgebraicGroup.RootData.RelativeRoots
public import Theory.AlgebraicGroup.RootSystems.Weyl

universe u v w

set_option linter.ambiguousOpen false
set_option linter.style.haveILetI false

open scoped BigOperators

/-! Relative-root fibers and their representations. -/

namespace Theory.AlgebraicGroup

section

open Set Submodule

/-- A positive root in the span of `J` admits a height-decreasing simple
reflection indexed by `J`. -/
private lemma isPos_exists_mem_J_pos_pairingIn_of_root_mem_span
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (J : Set ι) (hJ : J ⊆ base.support)
    (i : ι) (hi : base.IsPos i)
    (hspan : P.root i ∈ Submodule.span ℝ (P.root '' J)) :
    ∃ j ∈ J, 0 < P.pairingIn ℤ j i := by
  classical
  by_contra! hnone
  obtain ⟨f, hfsub, hfsgn, hfroot⟩ := base.exists_root_eq_sum_int i
  have hcoeff_pos : 0 < f := by
    rcases hfsgn with hfpos | hfneg
    · exact hfpos
    · exfalso
      have hheight := base.height_eq_sum hfroot
      rw [RootPairing.Base.isPos_iff, hheight] at hi
      have hsum_nonpos : ∑ j ∈ base.support, f j ≤ 0 := by
        apply Finset.sum_nonpos
        intro j hj
        have hjneg := (Pi.lt_def.mp hfneg).1 j
        simpa [sub_nonneg] using hjneg
      linarith
  have hrepr_zero : ∀ (x : M), x ∈ Submodule.span ℝ (P.root '' J) →
      ∀ j : base.support, j.1 ∉ J → base.toWeightBasis.repr x j = 0 := by
    intro x hx
    refine Submodule.span_induction (p := fun y _ =>
      ∀ j : base.support, j.1 ∉ J → base.toWeightBasis.repr y j = 0) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨a, haJ, rfl⟩ j hj
      have hja : (⟨a, hJ haJ⟩ : base.support) ≠ j := by
        intro h
        apply hj
        have hh := congrArg Subtype.val h
        simpa [← hh] using haJ
      change base.toWeightBasis.repr
        (P.root (↑(⟨a, hJ haJ⟩ : base.support))) j = 0
      rw [base.toWeightBasis_repr_root]
      exact Finsupp.single_eq_of_ne hja.symm
    · intro j _
      simp
    · intro y z _ _ hy hz j hj
      simp [map_add, hy j hj, hz j hj]
    · intro c y _ hy j hj
      simp [map_smul, hy j hj]
  have hrepr_i := hrepr_zero (P.root i) hspan
  have hfJ : ∀ j, f j ≠ 0 → j ∈ J := by
    intro j hjnz
    by_contra hjJ
    have hjbase : j ∈ base.support := hfsub hjnz
    let jb : base.support := ⟨j, hjbase⟩
    have hcoord := hrepr_i jb hjJ
    have hcoord' : (f j : ℝ) = 0 := by
      have hrepr_eq := congrArg (fun z => base.toWeightBasis.repr z jb) hfroot
      rw [hcoord] at hrepr_eq
      rw [map_sum] at hrepr_eq
      simp_rw [map_zsmul] at hrepr_eq
      rw [Finset.sum_apply'] at hrepr_eq
      rw [Finset.sum_eq_single j] at hrepr_eq
      · have hrepret : base.toWeightBasis.repr (P.root j) jb = (1 : ℝ) := by
          change base.toWeightBasis.repr (P.root (↑jb)) jb = 1
          simp [base.toWeightBasis_repr_root]
        have hrepr_eq' := hrepr_eq.symm
        simpa [hrepret] using hrepr_eq'
      · intro y hy hne
        have hne' : (⟨y, hy⟩ : base.support) ≠ jb := by
          intro h
          apply hne
          exact congrArg Subtype.val h
        have hrootrepr : base.toWeightBasis.repr (P.root y) jb = 0 := by
          change base.toWeightBasis.repr (P.root (↑(⟨y, hy⟩ : base.support))) jb = 0
          rw [base.toWeightBasis_repr_root]
          exact Finsupp.single_eq_of_ne hne'.symm
        simp [Pi.smul_apply, hrootrepr]
      · intro hjnot
        exact False.elim (hjnot hjbase)
    exact hjnz (by exact_mod_cast hcoord')
  have hpair_eq : P.pairingIn ℤ i i =
      ∑ j ∈ base.support, f j • P.pairingIn ℤ j i := by
    apply FaithfulSMul.algebraMap_injective ℤ ℝ
    rw [P.algebraMap_pairingIn]
    simp only [map_sum]
    have h := congrArg (P.coroot' i) hfroot
    simpa [map_sum, map_zsmul, ← P.algebraMap_pairingIn ℤ,
      zsmul_eq_mul] using h
  have hpair_le : P.pairingIn ℤ i i ≤ 0 := by
    rw [hpair_eq]
    apply Finset.sum_nonpos
    intro j hj
    by_cases hjJ : j ∈ J
    · exact smul_nonpos_of_nonneg_of_nonpos (hcoeff_pos.le j) (hnone j hjJ)
    · have hfj : f j = 0 := by
        by_contra hfj
        exact hjJ (hfJ j hfj)
      simp [hfj]
  have hself : P.pairingIn ℤ i i = 2 := by
    exact RootPairing.pairingIn_same (P := P) (S := ℤ) i
  omega

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public def relativeRootLayer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    (coeff : D.Root → D.Root → ℤ)
    (J : Set D.Root) {V : Type v} [AddCommGroup V] [Module k V]
    (rootVector : D.Root → k → V) (i : ℤ) : Submodule k V :=
  Submodule.span k {v | ∃ γ t,
    i ≤ RelativeRootHeight coeff D.simple.toFinite.toFinset J γ ∧ v = rootVector γ t}

@[expose]
public def relativeRootFiberAtHeight
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    (coeff : D.Root → D.Root → ℤ) (J : Set D.Root)
    (i : ℤ) (β : D.Root) : Set D.Root :=
  {γ | γ ∈ RelativeRootFiber coeff D.simple J Set.univ
      (RelativeRootProjection coeff D.simple J β) ∧
    RelativeRootHeight coeff D.simple.toFinite.toFinset J γ = i}

@[expose]
public def relativeRootFiberSpan
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    (coeff : D.Root → D.Root → ℤ) (J : Set D.Root)
    {V : Type v} [AddCommGroup V] [Module k V]
    (rootVector : D.Root → k → V) (i : ℤ) (β : D.Root) : Submodule k V :=
  Submodule.span k {v | ∃ γ ∈ relativeRootFiberAtHeight D coeff J i β,
    ∃ t, v = rootVector γ t}

@[expose]
public def relativeRootFiberSubmodule
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    (coeff : D.Root → D.Root → ℤ) (J : Set D.Root)
    {V : Type v} [AddCommGroup V] [Module k V]
    (rootVector : D.Root → k → V) (i : ℤ) (β : D.Root) :
    Submodule k (V ⧸ relativeRootLayer D coeff J rootVector (i + 1)) :=
  (relativeRootFiberSpan D coeff J rootVector i β).map
    (relativeRootLayer D coeff J rootVector (i + 1)).mkQ

end

section

@[expose]
public noncomputable def parabolicWeylSubgroup
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (J : Set ι) : Subgroup P.weylGroup :=
  Subgroup.closure (Set.range fun α : J => RootPairing.weylGroup.ofIdx P α.1)

@[expose]
public def rootFiber
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (J : Set ι) (γ : M) : Set ι :=
  {α | P.root α - γ ∈ Submodule.span R (P.root '' J)}

end

section

variable {k : Type u} [Field k]

/-- Explicit equivariance of root vectors preserves the span generated by one
relative-root fiber at a fixed relative height. -/
public lemma relativeRootFiberSpan_invariant
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    (J : Set D.Root) (coeff : D.Root → D.Root → ℤ)
    (i : ℤ) (β : D.Root)
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V)
    (rootVector : D.Root → k → V)
    (rootAction : Variety.Point K → D.Root → D.Root)
    (rootScalar : Variety.Point K → D.Root → k → k)
    (hRootVector : ∀ g γ t,
      (ρ.action g).1 (rootVector γ t) =
        rootVector (rootAction g γ) (rootScalar g γ t))
    (hProjection : ∀ g γ,
      RelativeRootProjection coeff D.simple J (rootAction g γ) =
        RelativeRootProjection coeff D.simple J γ)
    (hHeight : ∀ g γ,
      RelativeRootHeight coeff D.simple.toFinite.toFinset J (rootAction g γ) =
        RelativeRootHeight coeff D.simple.toFinite.toFinset J γ) :
    IsInvariantSubmodule ρ (relativeRootFiberSpan D coeff J rootVector i β) := by
  intro g v hv
  refine Submodule.span_induction (p := fun x _ =>
    (ρ.action g).1 x ∈ relativeRootFiberSpan D coeff J rootVector i β) ?_ ?_ ?_ ?_ hv
  · intro x hx
    rcases hx with ⟨γ, hγ, t, rfl⟩
    rw [hRootVector]
    apply Submodule.subset_span
    refine ⟨rootAction g γ, ?_, rootScalar g γ t, rfl⟩
    refine ⟨?_, hHeight g γ |>.trans hγ.2⟩
    rcases hγ.1 with ⟨hγRoot, hγProjection⟩
    exact ⟨hγRoot, (hProjection g γ).trans hγProjection⟩
  · simp
  · intro x y _ _ hx hy
    simpa using (relativeRootFiberSpan D coeff J rootVector i β).add_mem hx hy
  · intro c x _ hx
    simpa using (relativeRootFiberSpan D coeff J rootVector i β).smul_mem c hx

end

section

variable {k : Type u} [Field k]

/-- A root fiber at a fixed relative height has a maximal absolute-height root
whenever the specified root witnesses its nonemptiness. -/
public lemma relativeRootFiber_exists_max_height
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Fintype D.Root]
    (J : Set D.Root) (coeff : D.Root → D.Root → ℤ)
    (i : ℤ) (β : D.Root)
    (hβ : RelativeRootHeight coeff D.simple.toFinite.toFinset J β = i) :
    ∃ γ, γ ∈ relativeRootFiberAtHeight D coeff J i β ∧
      ∀ δ, δ ∈ relativeRootFiberAtHeight D coeff J i β →
        D.height δ ≤ D.height γ := by
  let fiber := relativeRootFiberAtHeight D coeff J i β
  have hβFiber : β ∈ fiber := by
    refine ⟨?_, hβ⟩
    exact ⟨Set.mem_univ β, rfl⟩
  exact Set.exists_max_image fiber D.height fiber.toFinite ⟨β, hβFiber⟩

end

section

/-- Every parabolic Weyl orbit contains a root of minimal full base height. -/
public lemma exists_parabolicWeylSubgroup_baseHeight_minimal
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    (base : P.Base) (J : Set ι) (α : ι) :
    ∃ w : parabolicWeylSubgroup P J, ∀ v : parabolicWeylSubgroup P J,
      base.height (P.weylGroupToPerm w.1 α) ≤
        base.height (P.weylGroupToPerm v.1 α) := by
  let : Finite P.weylGroup := weylGroup_finite P
  letI : Fintype (parabolicWeylSubgroup P J) := Fintype.ofFinite _
  obtain ⟨w, -, hw⟩ := Finset.exists_min_image Finset.univ
    (fun v : parabolicWeylSubgroup P J =>
      base.height (P.weylGroupToPerm v.1 α)) Finset.univ_nonempty
  exact ⟨w, fun v => hw v (Finset.mem_univ v)⟩

end

section

/-- The subgroup generated by reflections in `J` preserves every root fiber
modulo the span of `J`. -/
public lemma parabolicWeylSubgroup_rootFiber_invariant
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (J : Set ι) (γ : M)
    (w : parabolicWeylSubgroup P J) (α : ι)
    (hα : α ∈ rootFiber P J γ) :
    P.weylGroupToPerm w.1 α ∈ rootFiber P J γ := by
  let F := rootFiber P J γ
  have hreflection (δ : J) (β : ι) :
      β ∈ F ↔ P.reflectionPerm δ.1 β ∈ F := by
    have hδspan : P.root δ.1 ∈ Submodule.span R (P.root '' J) := by
      apply Submodule.subset_span
      exact ⟨δ.1, δ.2, rfl⟩
    have hforward (η : ι) : η ∈ F → P.reflectionPerm δ.1 η ∈ F := by
      intro hη
      change P.root η - γ ∈ Submodule.span R (P.root '' J) at hη
      change P.root (P.reflectionPerm δ.1 η) - γ ∈
        Submodule.span R (P.root '' J)
      rw [P.root_reflectionPerm, P.reflection_apply_root]
      change (P.root η - (P.pairing η δ.1) • P.root δ.1) - γ ∈ _
      have hreorder :
          (P.root η - (P.pairing η δ.1) • P.root δ.1) - γ =
            (P.root η - γ) - (P.pairing η δ.1) • P.root δ.1 := by
        abel
      rw [hreorder]
      exact Submodule.sub_mem _ hη (Submodule.smul_mem _ _ hδspan)
    constructor
    · exact hforward β
    · intro h
      have hh := hforward (P.reflectionPerm δ.1 β) h
      simpa using hh
  have hclosure : ∀ x : P.weylGroup,
      x ∈ parabolicWeylSubgroup P J →
      ∀ β, β ∈ F ↔ P.weylGroupToPerm x β ∈ F := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        rcases hx with ⟨δ, rfl⟩
        exact hreflection δ
    | one => simp
    | mul x y hx hy hx' hy' =>
        intro β
        rw [map_mul, Equiv.Perm.mul_apply]
        exact (hy' β).trans (hx' (P.weylGroupToPerm y β))
    | inv x hx hx' =>
        intro β
        have h := hx' (P.weylGroupToPerm x⁻¹ β)
        simp at h
        exact h.symm
  exact (hclosure w.1 w.2 α).mp hα

end

section

/-- A root of minimal base height in its parabolic Weyl orbit has nonpositive
Cartan pairing with every simple root in `J`. -/
public lemma rootFiber_minimal_pairingIn_le_zero
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (J : Set ι) (hJ : J ⊆ base.support)
    (α δ : ι) (hδ : δ ∈ J)
    (hmin : ∀ w : parabolicWeylSubgroup P J,
      base.height α ≤ base.height (P.weylGroupToPerm w.1 α)) :
    P.pairingIn ℤ α δ ≤ 0 := by
  let δJ : J := ⟨δ, hδ⟩
  let s : P.weylGroup := RootPairing.weylGroup.ofIdx P δ
  have hs : s ∈ parabolicWeylSubgroup P J := by
    apply Subgroup.subset_closure
    exact ⟨δJ, rfl⟩
  let w : parabolicWeylSubgroup P J := ⟨s, hs⟩
  have hle := hmin w
  change base.height α ≤ base.height (P.reflectionPerm δ α) at hle
  have hroot : P.root (P.reflectionPerm δ α) =
      P.root α + (-P.pairingIn ℤ α δ) • P.root δ := by
    rw [P.root_reflectionPerm, P.reflection_apply_root' ℤ]
    simp [sub_eq_add_neg]
  have hheight := base.height_add_zsmul hroot
  rw [base.height_one_of_mem_support (hJ hδ)] at hheight
  simp at hheight
  omega

end

section

/-- Any two roots in one root fiber differ by an element of the span of `J`. -/
public lemma rootFiber_root_sub_mem_span
    {ι R M N : Type*} [Fintype ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (J : Set ι) (γ : M)
    {α β : ι} (hα : α ∈ rootFiber P J γ)
    (hβ : β ∈ rootFiber P J γ) :
    P.root α - P.root β ∈ Submodule.span R (P.root '' J) := by
  change P.root α - γ ∈ Submodule.span R (P.root '' J) at hα
  change P.root β - γ ∈ Submodule.span R (P.root '' J) at hβ
  have hrewrite : P.root α - P.root β =
      (P.root α - γ) - (P.root β - γ) := by
    abel
  rw [hrewrite]
  exact Submodule.sub_mem _ hα hβ

end

section
open Set Submodule

public lemma root_mem_span_reflection_mem_parabolicWeylSubgroup
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (J : Set ι) (hJ : J ⊆ base.support)
    (i : ι) (hiQ : P.root i ∈ Submodule.span ℝ (P.root '' J)) :
    RootPairing.weylGroup.ofIdx P i ∈ parabolicWeylSubgroup P J := by
  let Q : Submodule ℝ M := Submodule.span ℝ (P.root '' J)
  let S := parabolicWeylSubgroup P J
  have hpos : ∀ i : ι, base.IsPos i → P.root i ∈ Q →
      RootPairing.weylGroup.ofIdx P i ∈ S := by
    intro r hrpos hrQ
    generalize hN : (base.height r).natAbs = n
    induction n using Nat.strongRecOn generalizing r with
    | ind n ih =>
        obtain ⟨j, hjJ, hjpos⟩ :=
          isPos_exists_mem_J_pos_pairingIn_of_root_mem_span P base J hJ r hrpos hrQ
        have hjbase : j ∈ base.support := hJ hjJ
        rcases eq_or_ne r j with rfl | hrj
        · apply Subgroup.subset_closure
          exact ⟨⟨r, hjJ⟩, rfl⟩
        · have hkpos : base.IsPos (P.reflectionPerm j r) :=
            hrpos.reflectionPerm hjbase hrj
          have hkQ : P.root (P.reflectionPerm j r) ∈ Q := by
            rw [P.root_reflectionPerm, P.reflection_apply_root' ℤ]
            apply Q.sub_mem hrQ
            rw [← Int.cast_smul_eq_zsmul ℝ]
            exact Q.smul_mem (P.pairingIn ℤ r j : ℝ)
              (Submodule.subset_span ⟨j, hjJ, rfl⟩)
          have hlt : (base.height (P.reflectionPerm j r)).natAbs < n := by
            suffices hheightlt : base.height (P.reflectionPerm j r) < base.height r by
              have hk_nonneg : 0 ≤ base.height (P.reflectionPerm j r) :=
                (base.isPos_iff').mp hkpos
              have hr_nonneg : 0 ≤ base.height r := (base.isPos_iff').mp hrpos
              have hcast :
                  ((base.height (P.reflectionPerm j r)).natAbs : ℤ) <
                    ((base.height r).natAbs : ℤ) := by
                simpa [Int.natAbs_of_nonneg hk_nonneg,
                  Int.natAbs_of_nonneg hr_nonneg] using hheightlt
              have habs : (base.height (P.reflectionPerm j r)).natAbs <
                  (base.height r).natAbs := by
                exact_mod_cast hcast
              simpa [hN] using habs
            have hroot : P.root (P.reflectionPerm j r) =
                P.root r + (-P.pairingIn ℤ r j) • P.root j := by
              rw [P.root_reflectionPerm, P.reflection_apply_root' ℤ]
              simp [sub_eq_add_neg]
            have hheight := base.height_add_zsmul hroot
            rw [base.height_one_of_mem_support hjbase] at hheight
            simp at hheight
            have hjpos' : 0 < P.pairingIn ℤ r j := by
              rw [P.zero_lt_pairingIn_iff']
              exact hjpos
            omega
          have hkS := ih (base.height (P.reflectionPerm j r)).natAbs hlt
            (P.reflectionPerm j r) hkpos hkQ rfl
          have hjS : RootPairing.weylGroup.ofIdx P j ∈ S := by
            apply Subgroup.subset_closure
            exact ⟨⟨j, hjJ⟩, rfl⟩
          have hkEq : RootPairing.weylGroup.ofIdx P (P.reflectionPerm j r) =
              RootPairing.weylGroup.ofIdx P j *
                RootPairing.weylGroup.ofIdx P r *
                  RootPairing.weylGroup.ofIdx P j := by
            apply Subtype.ext
            exact _root_.RootPairing.Equiv.reflection_reflectionPerm P r j
          have hjSq : RootPairing.weylGroup.ofIdx P j *
              RootPairing.weylGroup.ofIdx P j = 1 := by
            apply Subtype.ext
            change RootPairing.Equiv.reflection P j *
              RootPairing.Equiv.reflection P j = 1
            rw [mul_eq_one_iff_inv_eq]
            exact RootPairing.Equiv.reflection_inv P j
          have heq : RootPairing.weylGroup.ofIdx P r =
              RootPairing.weylGroup.ofIdx P j *
                RootPairing.weylGroup.ofIdx P (P.reflectionPerm j r) *
                  RootPairing.weylGroup.ofIdx P j := by
            rw [hkEq]
            calc
              RootPairing.weylGroup.ofIdx P r =
                  1 * RootPairing.weylGroup.ofIdx P r * 1 := by simp
              _ = (RootPairing.weylGroup.ofIdx P j *
                    RootPairing.weylGroup.ofIdx P j) *
                    RootPairing.weylGroup.ofIdx P r *
                    (RootPairing.weylGroup.ofIdx P j *
                      RootPairing.weylGroup.ofIdx P j) := by rw [hjSq]
              _ = RootPairing.weylGroup.ofIdx P j *
                    (RootPairing.weylGroup.ofIdx P j *
                      RootPairing.weylGroup.ofIdx P r *
                        RootPairing.weylGroup.ofIdx P j) *
                          RootPairing.weylGroup.ofIdx P j := by
                    simp only [mul_assoc]
          rw [heq]
          exact S.mul_mem (S.mul_mem hjS hkS) hjS
  letI := P.indexNeg
  rcases RootPairing.Base.IsPos.or_neg base i with hi | hi
  · exact hpos i hi hiQ
  · have hnegQ : P.root (-i) ∈ Q := by
      simpa using Q.neg_mem hiQ
    have hnegS := hpos (-i) hi hnegQ
    have hiSq : RootPairing.weylGroup.ofIdx P i *
        RootPairing.weylGroup.ofIdx P i = 1 := by
      apply Subtype.ext
      change RootPairing.Equiv.reflection P i *
        RootPairing.Equiv.reflection P i = 1
      rw [mul_eq_one_iff_inv_eq]
      exact RootPairing.Equiv.reflection_inv P i
    have heq : RootPairing.weylGroup.ofIdx P (-i) =
        RootPairing.weylGroup.ofIdx P i := by
      have hreflect : RootPairing.weylGroup.ofIdx P (-i) =
          RootPairing.weylGroup.ofIdx P i *
            RootPairing.weylGroup.ofIdx P i *
              RootPairing.weylGroup.ofIdx P i := by
        apply Subtype.ext
        exact _root_.RootPairing.Equiv.reflection_reflectionPerm P i i
      rw [hreflect, hiSq, one_mul]
    rwa [heq] at hnegS

end

section

variable {k : Type u} [Field k]

/-- Invariance of the root-vector span descends to its image in an invariant
layer quotient. -/
public lemma relativeRootFiberSubmodule_invariant
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Fintype D.Root]
    (J : Set D.Root) (coeff : D.Root → D.Root → ℤ)
    (i : ℤ) (β : D.Root)
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V)
    (rootVector : D.Root → k → V)
    (ρquot : RationalRepresentation K
      (V ⧸ relativeRootLayer D coeff J rootVector (i + 1)))
    (hQuot : IsQuotientRepresentation ρ
      (relativeRootLayer D coeff J rootVector (i + 1)) ρquot)
    (hSpan : IsInvariantSubmodule ρ
      (relativeRootFiberSpan D coeff J rootVector i β)) :
    IsInvariantSubmodule ρquot
      (relativeRootFiberSubmodule D coeff J rootVector i β) := by
  intro g x hx
  rcases hx with ⟨y, hy, rfl⟩
  change (ρquot.action g).1 (Submodule.Quotient.mk y) ∈
    relativeRootFiberSubmodule D coeff J rootVector i β
  rw [hQuot]
  exact ⟨(ρ.action g).1 y, hSpan g y hy, rfl⟩

end

section

open Set Submodule

/-- Two distinct roots of minimal height in their parabolic Weyl orbits and
in the same nontrivial root fiber have a difference which is itself a root of
the subsystem spanned by `J`. -/
public lemma rootFiber_minimal_sub_isRoot
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (J : Set ι) (hJ : J ⊆ base.support) (γ : M)
    (hγ : γ ∉ Submodule.span ℝ (P.root '' J))
    (α β : ι) (hα : α ∈ rootFiber P J γ) (hβ : β ∈ rootFiber P J γ)
    (hαβ : α ≠ β)
    (hαmin : ∀ w : parabolicWeylSubgroup P J,
      base.height α ≤ base.height (P.weylGroupToPerm w.1 α))
    (hβmin : ∀ w : parabolicWeylSubgroup P J,
      base.height β ≤ base.height (P.weylGroupToPerm w.1 β)) :
    ∃ δ, P.root δ = P.root α - P.root β ∧
      P.root δ ∈ Submodule.span ℝ (P.root '' J) := by
  let Q : Submodule ℝ M := Submodule.span ℝ (P.root '' J)
  have hαQ : P.root α - γ ∈ Q := hα
  have hβQ : P.root β - γ ∈ Q := hβ
  have hsubQ : P.root α - P.root β ∈ Q := by
    exact rootFiber_root_sub_mem_span P J γ hα hβ
  have hαnotJ : α ∉ J := by
    intro hαJ
    apply hγ
    have hrα : P.root α ∈ Q := Submodule.subset_span ⟨α, hαJ, rfl⟩
    have : γ = P.root α - (P.root α - γ) := by abel
    rw [this]
    exact Q.sub_mem hrα hαQ
  have hβnotJ : β ∉ J := by
    intro hβJ
    apply hγ
    have hrβ : P.root β ∈ Q := Submodule.subset_span ⟨β, hβJ, rfl⟩
    have : γ = P.root β - (P.root β - γ) := by abel
    rw [this]
    exact Q.sub_mem hrβ hβQ
  have hαnotspan : P.root α ∉ Q := by
    intro hrα
    apply hγ
    have : γ = P.root α - (P.root α - γ) := by abel
    rw [this]
    exact Q.sub_mem hrα hαQ
  have hβmemspanInsert : P.root β ∈
      Submodule.span ℝ (P.root '' (insert α J)) := by
    have hQle : Q ≤ Submodule.span ℝ (P.root '' (insert α J)) := by
      apply Submodule.span_mono
      exact image_mono (subset_insert α J)
    have hrα : P.root α ∈ Submodule.span ℝ (P.root '' (insert α J)) := by
      apply Submodule.subset_span
      exact ⟨α, mem_insert α J, rfl⟩
    have : P.root β = P.root α - (P.root α - P.root β) := by abel
    rw [this]
    exact Submodule.sub_mem _ hrα (hQle hsubQ)
  have hnotLI : ¬ LinearIndepOn ℝ P.root (insert β (insert α J)) := by
    intro hli
    have hβnot : β ∉ insert α J := by simp [hαβ.symm, hβnotJ]
    have hi := (linearIndepOn_insert hβnot).mp hli
    exact hi.2 hβmemspanInsert
  have hpairpos : 0 < P.pairingIn ℤ α β := by
    by_contra hnotpos
    have hpairle : P.pairingIn ℤ α β ≤ 0 := le_of_not_gt hnotpos
    let zeroQ : Q →ₗ[ℝ] ℝ := 0
    obtain ⟨q, hqQ, hqγ⟩ := LinearMap.exists_extend_of_notMem zeroQ hγ 1
    have hq_mem {x : M} (hx : x ∈ Q) : q x = 0 := by
      have heq := congrArg (fun L : Q →ₗ[ℝ] ℝ => L ⟨x, hx⟩) hqQ
      simpa [zeroQ] using heq
    have hqα : q (P.root α) = 1 := by
      have hz := hq_mem hαQ
      simp only [map_sub] at hz
      linarith
    have hqβ : q (P.root β) = 1 := by
      have hz := hq_mem hβQ
      simp only [map_sub] at hz
      linarith
    let c : ℝ := max (-base.chamberFunctional (P.root α))
      (-base.chamberFunctional (P.root β)) + 1
    let f : Module.Dual ℝ M := base.chamberFunctional + c • q
    let S : Set ι := insert β (insert α J)
    let v : S → P.rootSpan ℝ := fun i => P.rootSpanMem ℝ i.1
    let f' : Module.Dual ℝ (P.rootSpan ℝ) := f.comp (P.rootSpan ℝ).subtype
    have hp : ∀ i : S, 0 < f' (v i) := by
      rintro ⟨i, hiS⟩
      change 0 < base.chamberFunctional (P.root i) + c * q (P.root i)
      rcases hiS with hi | hi
      · subst i
        rw [hqβ]
        dsimp [c]
        linarith [le_max_right (-base.chamberFunctional (P.root α))
          (-base.chamberFunctional (P.root β))]
      · rcases hi with hi | hi
        · subst i
          rw [hqα]
          dsimp [c]
          linarith [le_max_left (-base.chamberFunctional (P.root α))
            (-base.chamberFunctional (P.root β))]
        · let j : base.support := ⟨i, hJ hi⟩
          have hqj : q (P.root i) = 0 := by
            apply hq_mem
            exact Submodule.subset_span ⟨i, hi, rfl⟩
          rw [hqj, base.chamberFunctional_root j]
          norm_num
    have cast_nonpos {i j : ι} (h : P.pairingIn ℤ i j ≤ 0) :
        P.pairingIn ℝ i j ≤ 0 := by
      rw [← P.algebraMap_pairingIn' ℝ ℤ]
      change ((P.pairingIn ℤ i j : ℤ) : ℝ) ≤ 0
      exact_mod_cast h
    have hn : Pairwise fun i j : S =>
        (P.posRootForm ℝ).posForm (v i) (v j) ≤ 0 := by
      rintro ⟨i, hiS⟩ ⟨j, hjS⟩ hij
      have hijv : i ≠ j := fun h => hij (Subtype.ext h)
      rw [(P.posRootForm ℝ).posForm_apply_root_root_le_zero_iff]
      change P.pairingIn ℝ i j ≤ 0
      rcases hiS with hi | hi <;> rcases hjS with hj | hj
      · subst i; subst j; exact (hijv rfl).elim
      · rcases hj with hj | hj
        · subst i; subst j
          have hswap : P.pairingIn ℤ β α ≤ 0 := by
            rw [P.pairingIn_le_zero_iff ℤ]
            exact hpairle
          exact cast_nonpos hswap
        · subst i
          exact cast_nonpos
            (rootFiber_minimal_pairingIn_le_zero P base J hJ β j hj hβmin)
      · rcases hi with hi | hi
        · subst i; subst j
          exact cast_nonpos hpairle
        · subst j
          have hβi := rootFiber_minimal_pairingIn_le_zero P base J hJ β i hi hβmin
          have hswap : P.pairingIn ℤ i β ≤ 0 := by
            rw [P.pairingIn_le_zero_iff ℤ]
            exact hβi
          exact cast_nonpos hswap
      · rcases hi with hi | hi <;> rcases hj with hj | hj
        · subst i; subst j; exact (hijv rfl).elim
        · subst i
          exact cast_nonpos
            (rootFiber_minimal_pairingIn_le_zero P base J hJ α j hj hαmin)
        · subst j
          have hαi := rootFiber_minimal_pairingIn_le_zero P base J hJ α i hi hαmin
          have hswap : P.pairingIn ℤ i α ≤ 0 := by
            rw [P.pairingIn_le_zero_iff ℤ]
            exact hαi
          exact cast_nonpos hswap
        · exact cast_nonpos (base.pairingIn_le_zero_of_ne hijv (hJ hi) (hJ hj))
    have hliSpan : LinearIndependent ℝ v :=
      LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero
        (P.posRootForm ℝ).posForm (by simpa using P.posRootForm_rootFormIn_posDef ℝ)
        f' v hp hn
    have hliM : LinearIndependent ℝ (fun i : S => P.root i.1) := by
      simpa [v, Function.comp_def] using
        hliSpan.map' (P.rootSpan ℝ).subtype (Submodule.ker_subtype _)
    exact hnotLI hliM
  obtain ⟨δ, hδ⟩ := P.root_sub_root_mem_of_pairingIn_pos hpairpos hαβ
  exact ⟨δ, hδ, hδ ▸ hsubQ⟩

end

section

variable {k : Type u} [Field k]

/-- A canonical root-vector generator of a fixed relative-root fiber in the
corresponding layer quotient. -/
@[expose]
public def relativeRootFiberGenerator
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    (J : Set D.Root) (coeff : D.Root → D.Root → ℤ)
    {V : Type v} [AddCommGroup V] [Module k V]
    (rootVector : D.Root → k → V) (i : ℤ) (β : D.Root)
    (z : {γ : D.Root // γ ∈ relativeRootFiberAtHeight D coeff J i β} × k) :
    relativeRootFiberSubmodule D coeff J rootVector i β :=
  ⟨Submodule.Quotient.mk (rootVector z.1.1 z.2), by
    change Submodule.Quotient.mk (rootVector z.1.1 z.2) ∈
      (relativeRootFiberSpan D coeff J rootVector i β).map
        (relativeRootLayer D coeff J rootVector (i + 1)).mkQ
    apply Submodule.mem_map_of_mem
    apply Submodule.subset_span
    exact ⟨z.1.1, z.1.2, z.2, rfl⟩⟩

/-- The canonical root-vector generators span the fixed relative-root fiber. -/
public lemma relativeRootFiberGenerator_span_eq_top
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Fintype D.Root]
    (J : Set D.Root) (coeff : D.Root → D.Root → ℤ)
    {V : Type v} [AddCommGroup V] [Module k V]
    (rootVector : D.Root → k → V) (i : ℤ) (β : D.Root) :
    Submodule.span k
      (Set.range (relativeRootFiberGenerator D J coeff rootVector i β)) = ⊤ := by
  rw [Submodule.span_range_subtype_eq_top_iff]
  dsimp [relativeRootFiberGenerator, relativeRootFiberSubmodule,
    relativeRootFiberSpan]
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨rootVector z.1.1 z.2, ⟨z.1.1, z.1.2, z.2, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨γ, hγ, t, rfl⟩, rfl⟩
    exact ⟨(⟨γ, hγ⟩, t), rfl⟩

/-- The quotient, Levi pullback, and fiber restriction transport the explicit
root-vector action to the canonical generators of a relative-root fiber. -/
public lemma relativeRootFiberGenerator_action
    {K L : Variety k} [AlgebraicGroup K] [AlgebraicGroup L]
    {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Fintype D.Root]
    (J : Set D.Root) (coeff : D.Root → D.Root → ℤ)
    (i : ℤ) (β : D.Root)
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V)
    (rootVector : D.Root → k → V)
    (rootAction : Variety.Point K → D.Root → D.Root)
    (rootScalar : Variety.Point K → D.Root → k → k)
    (ρquot : RationalRepresentation K
      (V ⧸ relativeRootLayer D coeff J rootVector (i + 1)))
    (hQuot : IsQuotientRepresentation ρ
      (relativeRootLayer D coeff J rootVector (i + 1)) ρquot)
    (ι : AlgebraicGroup.Morphism L K)
    (ρLevi : RationalRepresentation L
      (V ⧸ relativeRootLayer D coeff J rootVector (i + 1)))
    (hPullback : IsPullbackRepresentation ι ρquot ρLevi)
    (ρfiber : RationalRepresentation L
      (relativeRootFiberSubmodule D coeff J rootVector i β))
    (hRestriction : IsRestrictionRepresentation ρLevi
      (relativeRootFiberSubmodule D coeff J rootVector i β) ρfiber)
    (hRootVector : ∀ g γ t,
      (ρ.action g).1 (rootVector γ t) =
        rootVector (rootAction g γ) (rootScalar g γ t))
    (l : Variety.Point L)
    (z₁ z₂ :
      {γ : D.Root // γ ∈ relativeRootFiberAtHeight D coeff J i β} × k)
    (hlabel : rootAction (ι.onPoints l) z₁.1.1 = z₂.1.1)
    (hscalar : rootScalar (ι.onPoints l) z₁.1.1 z₁.2 = z₂.2) :
    (ρfiber.action l).1
        (relativeRootFiberGenerator D J coeff rootVector i β z₁) =
      relativeRootFiberGenerator D J coeff rootVector i β z₂ := by
  apply Subtype.ext
  calc
    (((ρfiber.action l).1
        (relativeRootFiberGenerator D J coeff rootVector i β z₁) :
        relativeRootFiberSubmodule D coeff J rootVector i β) :
        V ⧸ relativeRootLayer D coeff J rootVector (i + 1)) =
        (ρLevi.action l).1
          (relativeRootFiberGenerator D J coeff rootVector i β z₁) :=
      hRestriction l _
    _ = (ρquot.action (ι.onPoints l)).1
          (relativeRootFiberGenerator D J coeff rootVector i β z₁) := by
      rw [hPullback l]
    _ = Submodule.Quotient.mk
          ((ρ.action (ι.onPoints l)).1 (rootVector z₁.1.1 z₁.2)) :=
      hQuot (ι.onPoints l) (rootVector z₁.1.1 z₁.2)
    _ = Submodule.Quotient.mk (rootVector z₂.1.1 z₂.2) := by
      rw [hRootVector, hlabel, hscalar]
    _ = (relativeRootFiberGenerator D J coeff rootVector i β z₂ :
        V ⧸ relativeRootLayer D coeff J rootVector (i + 1)) := rfl

/-- A relative-root fiber representation is irreducible once every nonzero
invariant submodule contains all canonical root-vector generators. -/
public lemma relativeRootFiberRepresentation_irreducible_of_generator_mem
    {K L : Variety k} [AlgebraicGroup K] [AlgebraicGroup L]
    {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Fintype D.Root]
    (J : Set D.Root) (coeff : D.Root → D.Root → ℤ)
    (i : ℤ) (β : D.Root)
    {V : Type v} [AddCommGroup V] [Module k V]
    (rootVector : D.Root → k → V)
    (ρfiber : RationalRepresentation L
      (relativeRootFiberSubmodule D coeff J rootVector i β))
    (hgen : ∀ W : Submodule k
        (relativeRootFiberSubmodule D coeff J rootVector i β),
      IsInvariantSubmodule ρfiber W → W ≠ ⊥ →
      ∀ z, relativeRootFiberGenerator D J coeff rootVector i β z ∈ W) :
    IsAlgebraicallyIrreducibleRepresentation ρfiber := by
  intro W hW
  by_cases hWbot : W = ⊥
  · exact Or.inl hWbot
  · right
    apply top_unique
    rw [← relativeRootFiberGenerator_span_eq_top D J coeff rootVector i β]
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    exact hgen W hW hWbot z

/-- A relative-root fiber representation is irreducible when nonzero invariant
submodules detect a nonzero canonical root-vector generator and the Levi action
is transitive on all nonzero generator parameters through `rootAction` and
`rootScalar`. The zero-parameter law handles the remaining generators. -/
public theorem relativeRootFiberRepresentation_irreducible_of_generator_detection_of_rootAction_transitive
    {K L : Variety k} [AlgebraicGroup K] [AlgebraicGroup L]
    {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Fintype D.Root]
    (J : Set D.Root) (coeff : D.Root → D.Root → ℤ)
    (i : ℤ) (β : D.Root)
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V)
    (rootVector : D.Root → k → V)
    (rootAction : Variety.Point K → D.Root → D.Root)
    (rootScalar : Variety.Point K → D.Root → k → k)
    (ρquot : RationalRepresentation K
      (V ⧸ relativeRootLayer D coeff J rootVector (i + 1)))
    (hQuot : IsQuotientRepresentation ρ
      (relativeRootLayer D coeff J rootVector (i + 1)) ρquot)
    (ι : AlgebraicGroup.Morphism L K)
    (ρLevi : RationalRepresentation L
      (V ⧸ relativeRootLayer D coeff J rootVector (i + 1)))
    (hPullback : IsPullbackRepresentation ι ρquot ρLevi)
    (ρfiber : RationalRepresentation L
      (relativeRootFiberSubmodule D coeff J rootVector i β))
    (hRestriction : IsRestrictionRepresentation ρLevi
      (relativeRootFiberSubmodule D coeff J rootVector i β) ρfiber)
    (hRootVector : ∀ g γ t,
      (ρ.action g).1 (rootVector γ t) =
        rootVector (rootAction g γ) (rootScalar g γ t))
    (hzero : ∀ γ, rootVector γ 0 = 0)
    (hdetect : ∀ W : Submodule k
        (relativeRootFiberSubmodule D coeff J rootVector i β),
      IsInvariantSubmodule ρfiber W → W ≠ ⊥ →
      ∃ z, z.2 ≠ 0 ∧
        relativeRootFiberGenerator D J coeff rootVector i β z ∈ W)
    (htransitive : ∀ z₁ z₂ :
      {γ : D.Root // γ ∈ relativeRootFiberAtHeight D coeff J i β} × k,
      z₁.2 ≠ 0 → z₂.2 ≠ 0 →
      ∃ l : Variety.Point L,
        rootAction (ι.onPoints l) z₁.1.1 = z₂.1.1 ∧
        rootScalar (ι.onPoints l) z₁.1.1 z₁.2 = z₂.2) :
    IsAlgebraicallyIrreducibleRepresentation ρfiber := by
  apply relativeRootFiberRepresentation_irreducible_of_generator_mem
    D J coeff i β rootVector ρfiber
  intro W hW hWne z₂
  by_cases hz₂zero : z₂.2 = 0
  · have hgeneratorZero :
        relativeRootFiberGenerator D J coeff rootVector i β z₂ = 0 := by
      apply Subtype.ext
      change Submodule.Quotient.mk (rootVector z₂.1.1 z₂.2) = 0
      rw [hz₂zero, hzero]
      rfl
    rw [hgeneratorZero]
    exact W.zero_mem
  obtain ⟨z₁, hz₁nonzero, hz₁W⟩ := hdetect W hW hWne
  obtain ⟨l, hlabel, hscalar⟩ :=
    htransitive z₁ z₂ hz₁nonzero hz₂zero
  have haction : (ρfiber.action l).1
      (relativeRootFiberGenerator D J coeff rootVector i β z₁) =
      relativeRootFiberGenerator D J coeff rootVector i β z₂ := by
    exact relativeRootFiberGenerator_action D J coeff i β ρ rootVector
      rootAction rootScalar ρquot hQuot ι ρLevi hPullback ρfiber hRestriction
      hRootVector l z₁ z₂ hlabel hscalar
  rw [← haction]
  exact hW l _ hz₁W

/-- A canonical fiber generator is a high-weight vector when the Borel fixes
its root label, the torus acts on its parameter by the prescribed character,
and the root-vector parameterization is homogeneous along that generator. -/
public theorem relativeRootFiberGenerator_hasHighWeight_of_rootAction
    {K L : Variety k} [AlgebraicGroup K] [AlgebraicGroup L]
    {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Fintype D.Root]
    (J : Set D.Root) (coeff : D.Root → D.Root → ℤ)
    (i : ℤ) (β : D.Root)
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V)
    (rootVector : D.Root → k → V)
    (rootAction : Variety.Point K → D.Root → D.Root)
    (rootScalar : Variety.Point K → D.Root → k → k)
    (ρquot : RationalRepresentation K
      (V ⧸ relativeRootLayer D coeff J rootVector (i + 1)))
    (hQuot : IsQuotientRepresentation ρ
      (relativeRootLayer D coeff J rootVector (i + 1)) ρquot)
    (ι : AlgebraicGroup.Morphism L K)
    (ρLevi : RationalRepresentation L
      (V ⧸ relativeRootLayer D coeff J rootVector (i + 1)))
    (hPullback : IsPullbackRepresentation ι ρquot ρLevi)
    (ρfiber : RationalRepresentation L
      (relativeRootFiberSubmodule D coeff J rootVector i β))
    (hRestriction : IsRestrictionRepresentation ρLevi
      (relativeRootFiberSubmodule D coeff J rootVector i β) ρfiber)
    (hRootVector : ∀ g γ t,
      (ρ.action g).1 (rootVector γ t) =
        rootVector (rootAction g γ) (rootScalar g γ t))
    (B₀ T₀ : ClosedSubgroup L)
    (γ : D.Root) (hγ : γ ∈ relativeRootFiberAtHeight D coeff J i β)
    (z : k) (hz : z ≠ 0) (χ : TorusWeight T₀)
    (hgenerator : relativeRootFiberGenerator D J coeff rootVector i β
      (⟨γ, hγ⟩, z) ≠ 0)
    (hsmul : ∀ c : k, rootVector γ (c * z) = c • rootVector γ z)
    (hBfixed : ∀ l, l ∈ B₀ → rootAction (ι.onPoints l) γ = γ)
    (hTfixed : ∀ t : Variety.Point T₀.carrierVariety,
      rootAction (ι.onPoints (T₀.includePoint t)) γ = γ)
    (hTscalar : ∀ t : Variety.Point T₀.carrierVariety,
      rootScalar (ι.onPoints (T₀.includePoint t)) γ z =
        χ.pointCharacter t * z) :
    HasHighWeight ρfiber B₀ T₀
      (relativeRootFiberGenerator D J coeff rootVector i β (⟨γ, hγ⟩, z)) χ := by
  constructor
  · refine ⟨hgenerator, ?_⟩
    intro l hl
    let c := rootScalar (ι.onPoints l) γ z / z
    refine ⟨c, ?_⟩
    rw [relativeRootFiberGenerator_action D J coeff i β ρ rootVector
      rootAction rootScalar ρquot hQuot ι ρLevi hPullback ρfiber hRestriction
      hRootVector l (⟨γ, hγ⟩, z) (⟨γ, hγ⟩,
        rootScalar (ι.onPoints l) γ z) (hBfixed l hl) rfl]
    apply Subtype.ext
    change Submodule.Quotient.mk
        (rootVector γ (rootScalar (ι.onPoints l) γ z)) =
      c • Submodule.Quotient.mk (rootVector γ z)
    rw [show rootScalar (ι.onPoints l) γ z = c * z by
      simp [c, hz], hsmul]
    exact (relativeRootLayer D coeff J rootVector (i + 1)).mkQ.map_smul c
      (rootVector γ z)
  · refine ⟨hgenerator, ?_⟩
    intro t
    rw [relativeRootFiberGenerator_action D J coeff i β ρ rootVector
      rootAction rootScalar ρquot hQuot ι ρLevi hPullback ρfiber hRestriction
      hRootVector (T₀.includePoint t) (⟨γ, hγ⟩, z)
        (⟨γ, hγ⟩, χ.pointCharacter t * z) (hTfixed t) (hTscalar t)]
    apply Subtype.ext
    change Submodule.Quotient.mk
        (rootVector γ (χ.pointCharacter t * z)) =
      χ.pointCharacter t • Submodule.Quotient.mk (rootVector γ z)
    rw [hsmul]
    exact (relativeRootLayer D coeff J rootVector (i + 1)).mkQ.map_smul
      (χ.pointCharacter t) (rootVector γ z)

private noncomputable def torusWeightEvaluationAt
    {L : Variety k} [AlgebraicGroup L] (T₀ : ClosedSubgroup L)
    (t : Variety.Point T₀.carrierVariety) : TorusWeight T₀ →* kˣ where
  toFun χ := dPointEquiv 1 (χ.onPoints t) 0
  map_one' := by
    change dPointEquiv 1 (1 : Variety.Point (KMult k)) 0 = 1
    rw [dPointEquiv_one]
    rfl
  map_mul' χ ψ := by
    change dPointEquiv 1 (χ.onPoints t * ψ.onPoints t) 0 =
      dPointEquiv 1 (χ.onPoints t) 0 * dPointEquiv 1 (ψ.onPoints t) 0
    rw [dPointEquiv_mul]
    rfl

/-- A torus-weight product formula follows from the corresponding equality of
scalar-valued point characters. -/
public lemma torusWeight_eq_fintype_prod_zpow_of_pointCharacter
    {L : Variety k} [AlgebraicGroup L] (T₀ : ClosedSubgroup L)
    {ι : Type v} [Fintype ι]
    (χ : TorusWeight T₀) (weights : ι → TorusWeight T₀) (coeff : ι → ℤ)
    (hpoint : ∀ t,
      χ.pointCharacter t = ∏ j, (weights j).pointCharacter t ^ coeff j) :
    χ = ∏ j, weights j ^ coeff j := by
  apply TorusCharacter.pointCharacter_injective
  ext t
  have heval : (∏ j, weights j ^ coeff j).pointCharacter t =
      ∏ j, (weights j).pointCharacter t ^ coeff j := by
    calc
      (∏ j, weights j ^ coeff j).pointCharacter t =
          ((torusWeightEvaluationAt T₀ t) (∏ j, weights j ^ coeff j) : k) := rfl
      _ = ∏ j, ((torusWeightEvaluationAt T₀ t)
          (weights j ^ coeff j) : k) := by
        exact_mod_cast map_prod (torusWeightEvaluationAt T₀ t)
          (fun j => weights j ^ coeff j) Finset.univ
      _ = ∏ j, ((torusWeightEvaluationAt T₀ t) (weights j) : k) ^ coeff j := by
        apply Finset.prod_congr rfl
        intro j _
        exact_mod_cast map_zpow (torusWeightEvaluationAt T₀ t)
          (weights j) (coeff j)
      _ = ∏ j, (weights j).pointCharacter t ^ coeff j := by
        apply Finset.prod_congr rfl
        intro j _
        rfl
  exact (hpoint t).trans heval.symm

end

section

/-- Reflection in the difference of two equal-length roots exchanges them. -/
public lemma reflectionPerm_eq_of_root_eq_sub_of_length_eq
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    (form : P.InvariantForm) (α β δ : ι)
    (hδ : P.root δ = P.root α - P.root β)
    (hlen : form.form (P.root α) (P.root α) =
      form.form (P.root β) (P.root β)) :
    P.reflectionPerm δ α = β := by
  have hpair : P.pairing α δ = 1 := by
    have hformula := form.two_mul_apply_root_root α δ
    rw [hδ] at hformula
    simp only [LinearMap.sub_apply, map_sub] at hformula
    have hne : form.form (P.root δ) (P.root δ) ≠ 0 := form.ne_zero δ
    rw [hδ] at hne
    simp only [LinearMap.sub_apply, map_sub] at hne
    have hsymm : form.form (P.root β) (P.root α) =
        form.form (P.root α) (P.root β) := form.symm.eq _ _
    rw [hsymm, ← hlen] at hformula hne
    have hsecond : 2 * (form.form (P.root α) (P.root α) -
        form.form (P.root α) (P.root β)) ≠ 0 := by
      intro hz
      apply hne
      linarith
    have hfac : (P.pairing α δ - 1) *
        (2 * (form.form (P.root α) (P.root α) -
          form.form (P.root α) (P.root β))) = 0 := by
      nlinarith [hformula]
    exact sub_eq_zero.mp (mul_eq_zero.mp hfac |>.resolve_right hsecond)
  apply P.root.injective
  rw [P.root_reflectionPerm, P.reflection_apply_root, hpair, one_smul, hδ]
  abel

end

section

/-- Lemma 1.14.8: equal-length roots in a nontrivial parabolic root fiber
lie in one `W_J` orbit. -/
public theorem rootFiber_sameLength_exists_parabolicWeylSubgroup
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (form : P.InvariantForm)
    (J : Set ι) (hJ : J ⊆ base.support) (γ : M)
    (hγ : γ ∉ Submodule.span ℝ (P.root '' J))
    (α β : ι) (hα : α ∈ rootFiber P J γ) (hβ : β ∈ rootFiber P J γ)
    (hlen : form.form (P.root α) (P.root α) =
      form.form (P.root β) (P.root β)) :
    ∃ w : parabolicWeylSubgroup P J, P.weylGroupToPerm w.1 α = β := by
  obtain ⟨wa, hwa⟩ := exists_parabolicWeylSubgroup_baseHeight_minimal P base J α
  obtain ⟨wb, hwb⟩ := exists_parabolicWeylSubgroup_baseHeight_minimal P base J β
  let α' := P.weylGroupToPerm wa.1 α
  let β' := P.weylGroupToPerm wb.1 β
  have hα' : α' ∈ rootFiber P J γ :=
    parabolicWeylSubgroup_rootFiber_invariant P J γ wa α hα
  have hβ' : β' ∈ rootFiber P J γ :=
    parabolicWeylSubgroup_rootFiber_invariant P J γ wb β hβ
  have hαmin : ∀ w : parabolicWeylSubgroup P J,
      base.height α' ≤ base.height (P.weylGroupToPerm w.1 α') := by
    intro w
    have := hwa (w * wa)
    simpa [α', map_mul] using this
  have hβmin : ∀ w : parabolicWeylSubgroup P J,
      base.height β' ≤ base.height (P.weylGroupToPerm w.1 β') := by
    intro w
    have := hwb (w * wb)
    simpa [β', map_mul] using this
  have hlenα : form.form (P.root α') (P.root α') =
      form.form (P.root α) (P.root α) := by
    have hroot : wa.1 • P.root α = P.root α' := by
      exact P.weylGroup_apply_root wa.1 α
    rw [← hroot]
    exact RootPairing.InvariantForm.apply_weylGroup_smul P (B := form) wa.1
      (P.root α) (P.root α)
  have hlenβ : form.form (P.root β') (P.root β') =
      form.form (P.root β) (P.root β) := by
    have hroot : wb.1 • P.root β = P.root β' := by
      exact P.weylGroup_apply_root wb.1 β
    rw [← hroot]
    exact RootPairing.InvariantForm.apply_weylGroup_smul P (B := form) wb.1
      (P.root β) (P.root β)
  have hlen' : form.form (P.root α') (P.root α') =
      form.form (P.root β') (P.root β') := by
    rw [hlenα, hlen, ← hlenβ]
  by_cases heq : α' = β'
  · refine ⟨wb⁻¹ * wa, ?_⟩
    have hperm := congrArg (fun x => (P.weylGroupToPerm wb.1⁻¹) x) heq
    simpa [α', β', map_mul] using hperm
  · obtain ⟨δ, hδ, hδspan⟩ :=
      rootFiber_minimal_sub_isRoot P base J hJ γ hγ α' β'
        hα' hβ' heq hαmin hβmin
    have hrmem := root_mem_span_reflection_mem_parabolicWeylSubgroup
      P base J hJ δ hδspan
    let r : parabolicWeylSubgroup P J :=
      ⟨RootPairing.weylGroup.ofIdx P δ, hrmem⟩
    have href : P.weylGroupToPerm r.1 α' = β' := by
      exact reflectionPerm_eq_of_root_eq_sub_of_length_eq P form α' β' δ hδ hlen'
    refine ⟨wb⁻¹ * r * wa, ?_⟩
    have hperm := congrArg (fun x => (P.weylGroupToPerm wb.1⁻¹) x) href
    simpa [α', β', r, RootPairing.weylGroup.ofIdx, map_mul] using hperm

end

section

@[expose]
public def IsLongestWeylElement
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (w₀ : P.weylGroup) : Prop :=
  ∀ w : P.weylGroup, base.wordLength w ≤ base.wordLength w₀

end

end Theory.AlgebraicGroup
