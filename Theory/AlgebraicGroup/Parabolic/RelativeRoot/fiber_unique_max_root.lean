module

public import Theory.AlgebraicGroup.Representations.Algebraic.RelativeRoot
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.RelativeRootNeg
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.SourceSetup

/-!
The absolute-height maximum in a fixed relative-root fiber is unique.  The
proof is the root-system argument behind GLS3, Lemma 1.14.8: after negating
two putative maxima, choose minimal parabolic-Weyl representatives; distinct
minimal representatives force their difference to be a root in the parabolic
span, while the equal maximal heights force that root to have height zero.
-/

universe u v

namespace Theory.AlgebraicGroup

section

open Set
local notation "Submodule" => _root_.Submodule

private lemma lsum_repr_root_eq_height
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    (base : P.Base) (i : ι) :
    (Finsupp.lsum ℚ (fun _ : base.support => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)))
      (base.toWeightBasis.repr (P.root i)) = (base.height i : ℚ) := by
  obtain ⟨f, -, hroot⟩ := base.exists_root_eq_sum_int i
  have hrepr := congrArg base.toWeightBasis.repr hroot.2
  simp only [map_sum] at hrepr
  have hrepr_one {x : ι} (hx : x ∈ base.support) :
      (base.toWeightBasis.repr (P.root x)).sum (fun _ c => c) = 1 := by
    let j : base.support := ⟨x, hx⟩
    have hj := congrArg (fun z : base.support →₀ ℚ => z.sum (fun _ c => c))
      (base.toWeightBasis_repr_root j)
    simpa [j] using hj
  have hlsum_one {x : ι} (hx : x ∈ base.support) :
      (Finsupp.lsum ℚ (fun _ : base.support => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)))
        (base.toWeightBasis.repr (P.root x)) = 1 := by
    rw [Finsupp.lsum_apply]
    exact hrepr_one hx
  have hlsum_zsmul (x : ι) (n : ℤ) :
      (Finsupp.lsum ℚ (fun _ : base.support => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)))
        (base.toWeightBasis.repr (n • P.root x)) =
      (n : ℚ) * (Finsupp.lsum ℚ
        (fun _ : base.support => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)))
        (base.toWeightBasis.repr (P.root x)) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, map_smul, Finsupp.lsum_apply]
    change (((n : ℚ) • base.toWeightBasis.repr (P.root x)).sum
        (fun _ : base.support => fun c : ℚ => c)) =
      (n : ℚ) * (base.toWeightBasis.repr (P.root x)).sum
        (fun _ : base.support => fun c : ℚ => c)
    rw [Finsupp.sum_smul_index (h0 := by simp)]
    simp only [Finsupp.sum]
    rw [← Finset.mul_sum]
  calc
    (Finsupp.lsum ℚ (fun _ : base.support => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)))
        (base.toWeightBasis.repr (P.root i)) =
        ∑ x ∈ base.support,
          (Finsupp.lsum ℚ (fun _ : base.support => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)))
            (base.toWeightBasis.repr (f x • P.root x)) := by
      rw [hrepr]
      simp only [map_sum]
    _ = ∑ x ∈ base.support, (f x : ℚ) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hlsum_zsmul x (f x), hlsum_one hx, mul_one]
    _ = (base.height i : ℚ) := by
      rw [base.height_eq_sum hroot.2]
      norm_num

private lemma base_coeff_coord
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    (base : P.Base) (coeff : ι → ι → ℤ)
    (hCoeff : HasSimpleRootExpansion P base coeff)
    (a x : ι) (hx : x ∈ base.support) :
    (base.toWeightBasis.repr (P.root a)) ⟨x, hx⟩ = (coeff a x : ℚ) := by
  classical
  have hrepr := congrArg base.toWeightBasis.repr (hCoeff a).1
  simp only [map_sum, map_smul] at hrepr
  have h := congrArg
    (Finsupp.lapply (⟨x, hx⟩ : base.support) :
      (base.support →₀ ℚ) →ₗ[ℚ] ℚ) hrepr
  simp only [map_sum, map_smul, Finsupp.lapply_apply] at h
  have hrootcoord {j : ι} (hj : j ∈ base.support) :
      (base.toWeightBasis.repr (P.root j)) ⟨x, hx⟩ = if j = x then 1 else 0 := by
    let k : base.support := ⟨j, hj⟩
    have hk := base.toWeightBasis_repr_root k
    simpa [k, Finsupp.single_apply] using
      congrArg (fun z : base.support →₀ ℚ => z ⟨x, hx⟩) hk
  rw [show (∑ j ∈ base.support, (coeff a j : ℚ) •
      (base.toWeightBasis.repr (P.root j)) ⟨x, hx⟩) =
      ∑ j ∈ base.support, (coeff a j : ℚ) • (if j = x then 1 else 0) by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hrootcoord hj]] at h
  rw [Finset.sum_eq_single_of_mem x hx] at h
  · simpa using h
  · intro b hb hbx
    simp [hbx]

private lemma root_span_coord_zero
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    (base : P.Base) (J : Set ι) (hJ : J ⊆ base.support)
    {z : M} (hz : z ∈ Submodule.span ℚ (P.root '' J))
    (x : ι) (hx : x ∈ base.support) (hxJ : x ∉ J) :
    (base.toWeightBasis.repr z) ⟨x, hx⟩ = 0 := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
      rcases hz with ⟨j, hj, rfl⟩
      let k : base.support := ⟨j, hJ hj⟩
      have hneq : j ≠ x := by
        intro h
        exact hxJ (h ▸ hj)
      rw [base.toWeightBasis_repr_root k]
      simp [k, hneq]
  | zero => simp
  | add z₁ z₂ _ _ hz₁ hz₂ => simp [map_add, hz₁, hz₂]
  | smul c z _ hz => simp [map_smul, hz]

public lemma root_mem_span_projection_zero
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    (base : P.Base) (J : Set ι) (hJ : J ⊆ base.support)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    {a : ι} (hspan : P.root a ∈ Submodule.span ℚ (P.root '' J)) :
    RelativeRootProjection coeff (base.support : Set ι) J a = 0 := by
  classical
  apply Finsupp.ext
  intro x
  by_cases hx : x ∈ base.support
  · by_cases hxJ : x ∈ J
    · simp [RelativeRootProjection, hx, hxJ]
    · have hcoord := root_span_coord_zero P base J hJ hspan x hx hxJ
      have hcoeff := base_coeff_coord P base coeff hCoeff a x hx
      have hzero : coeff a x = 0 := by
        have : (coeff a x : ℚ) = 0 := by simpa [hcoeff] using hcoord
        exact_mod_cast this
      simp [RelativeRootProjection, hx, hxJ, hzero]
  · simp [RelativeRootProjection, hx]

public lemma root_sub_mem_span_of_projection_eq
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    (base : P.Base) (J : Set ι)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    {a b : ι}
    (hproj : RelativeRootProjection coeff (base.support : Set ι) J a =
      RelativeRootProjection coeff (base.support : Set ι) J b) :
    P.root a - P.root b ∈ Submodule.span ℚ (P.root '' J) := by
  classical
  let Q : Submodule ℚ M := Submodule.span ℚ (P.root '' J)
  have hcoeffeq (x : ι) (hx : x ∈ base.support) (hxJ : x ∉ J) :
      coeff a x = coeff b x := by
    have h := congrArg (fun f : ι →₀ ℤ => f x) hproj
    simpa [RelativeRootProjection, hx, hxJ] using h
  have hrootdiff : P.root a - P.root b =
      ∑ j ∈ base.support, ((coeff a j - coeff b j : ℤ) : ℚ) • P.root j := by
    rw [(hCoeff a).1, (hCoeff b).1]
    simp only [Int.cast_sub, sub_smul, Finset.sum_sub_distrib]
  have hsum : (∑ j ∈ base.support,
      ((coeff a j - coeff b j : ℤ) : ℚ) • P.root j) ∈ Q := by
    apply Q.sum_mem
    intro j hj
    by_cases hjJ : j ∈ J
    · exact Q.smul_mem _ (Submodule.subset_span ⟨j, hjJ, rfl⟩)
    · have hz := hcoeffeq j hj hjJ
      simp [hz]
  rw [hrootdiff]
  exact hsum

public lemma projection_eq_of_root_sub_mem_span
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    (base : P.Base) (J : Set ι) (hJ : J ⊆ base.support)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    {a b : ι}
    (hspan : P.root a - P.root b ∈ Submodule.span ℚ (P.root '' J)) :
    RelativeRootProjection coeff (base.support : Set ι) J a =
      RelativeRootProjection coeff (base.support : Set ι) J b := by
  classical
  apply Finsupp.ext
  intro x
  by_cases hx : x ∈ base.support
  · by_cases hxJ : x ∈ J
    · simp [RelativeRootProjection, hx, hxJ]
    · have hcoord := root_span_coord_zero P base J hJ hspan x hx hxJ
      have ha := base_coeff_coord P base coeff hCoeff a x hx
      have hb := base_coeff_coord P base coeff hCoeff b x hx
      have hzero : coeff a x = coeff b x := by
        have hz : (coeff a x : ℚ) - (coeff b x : ℚ) = 0 := by
          simpa [map_sub, ha, hb] using hcoord
        exact_mod_cast sub_eq_zero.mp hz
      simp [RelativeRootProjection, hx, hxJ, hzero]
  · simp [RelativeRootProjection, hx]

public lemma parabolicWeylSubgroup_relativeRootHeight_eq
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (J : Set ι) (hJ : J ⊆ base.support)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (w : parabolicWeylSubgroup P J) (a : ι) :
    RelativeRootHeight coeff base.support J (P.weylGroupToPerm w.1 a) =
      RelativeRootHeight coeff base.support J a := by
  let height := RelativeRootHeight coeff base.support J
  change height (P.weylGroupToPerm w.1 a) = height a
  have hclosure : ∀ x : P.weylGroup,
      x ∈ parabolicWeylSubgroup P J →
        ∀ b, height (P.weylGroupToPerm x b) = height b := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        rcases hx with ⟨δ, rfl⟩
        intro b
        exact relativeRootHeight_reflectionPerm_eq P base J hJ coeff hCoeff δ.2 b
    | one => simp
    | mul x y hx hy hx' hy' =>
        intro b
        rw [map_mul, Equiv.Perm.mul_apply, hx', hy']
    | inv x hx hx' =>
        intro b
        have h := hx' (P.weylGroupToPerm x⁻¹ b)
        simp at h
        exact h.symm
  exact hclosure w.1 w.2 a


set_option maxHeartbeats 800000 in
public lemma rootFiber_minimal_pairingIn_le_zero_ordered
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
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

set_option maxHeartbeats 800000 in
public lemma rootFiber_minimal_sub_isRoot_ordered
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (J : Set ι) (hJ : J ⊆ base.support) (γ : M)
    (hγ : γ ∉ Submodule.span ℚ (P.root '' J))
    (α β : ι) (hα : α ∈ rootFiber P J γ) (hβ : β ∈ rootFiber P J γ)
    (hαβ : α ≠ β)
    (hαmin : ∀ w : parabolicWeylSubgroup P J,
      base.height α ≤ base.height (P.weylGroupToPerm w.1 α))
    (hβmin : ∀ w : parabolicWeylSubgroup P J,
      base.height β ≤ base.height (P.weylGroupToPerm w.1 β)) :
    ∃ δ, P.root δ = P.root α - P.root β ∧
      P.root δ ∈ Submodule.span ℚ (P.root '' J) := by
  let Q : Submodule ℚ M := Submodule.span ℚ (P.root '' J)
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
      Submodule.span ℚ (P.root '' (insert α J)) := by
    have hQle : Q ≤ Submodule.span ℚ (P.root '' (insert α J)) := by
      apply Submodule.span_mono
      exact image_mono (subset_insert α J)
    have hrα : P.root α ∈ Submodule.span ℚ (P.root '' (insert α J)) := by
      apply Submodule.subset_span
      exact ⟨α, mem_insert α J, rfl⟩
    have : P.root β = P.root α - (P.root α - P.root β) := by abel
    rw [this]
    exact Submodule.sub_mem _ hrα (hQle hsubQ)
  have hnotLI : ¬ LinearIndepOn ℚ P.root (insert β (insert α J)) := by
    intro hli
    have hβnot : β ∉ insert α J := by simp [hαβ.symm, hβnotJ]
    have hi := (linearIndepOn_insert hβnot).mp hli
    exact hi.2 hβmemspanInsert
  have hpairpos : 0 < P.pairingIn ℤ α β := by
    by_contra hnotpos
    have hpairle : P.pairingIn ℤ α β ≤ 0 := le_of_not_gt hnotpos
    let zeroQ : Q →ₗ[ℚ] ℚ := 0
    obtain ⟨q, hqQ, hqγ⟩ := LinearMap.exists_extend_of_notMem zeroQ hγ 1
    have hq_mem {x : M} (hx : x ∈ Q) : q x = 0 := by
      have heq := congrArg (fun L : Q →ₗ[ℚ] ℚ => L ⟨x, hx⟩) hqQ
      simpa [zeroQ] using heq
    have hqα : q (P.root α) = 1 := by
      have hz := hq_mem hαQ
      simp only [map_sub] at hz
      linarith
    have hqβ : q (P.root β) = 1 := by
      have hz := hq_mem hβQ
      simp only [map_sub] at hz
      linarith
    let c : ℚ := max (-(base.height α : ℚ))
      (-(base.height β : ℚ)) + 1
    let f : Module.Dual ℚ M :=
      (Finsupp.lsum ℚ fun _ : base.support => LinearMap.id).comp
        base.toWeightBasis.repr.toLinearMap + c • q
    let S : Set ι := insert β (insert α J)
    let v : S → P.rootSpan ℚ := fun i => P.rootSpanMem ℚ i.1
    let f' : Module.Dual ℚ (P.rootSpan ℚ) :=
      f.comp (P.rootSpan ℚ).subtype
    have hp : ∀ i : S, 0 < f' (v i) := by
      rintro ⟨i, hiS⟩
      change 0 <
        (Finsupp.lsum ℚ fun _ : base.support => LinearMap.id)
            (base.toWeightBasis.repr (P.root i)) + c * q (P.root i)
      rw [lsum_repr_root_eq_height P base i]
      rcases hiS with hi | hi
      · subst i
        rw [hqβ]
        dsimp [c]
        linarith [le_max_right (-(base.height α : ℚ))
          (-(base.height β : ℚ))]
      · rcases hi with hi | hi
        · subst i
          rw [hqα]
          dsimp [c]
          linarith [le_max_left (-(base.height α : ℚ))
            (-(base.height β : ℚ))]
        · let j : base.support := ⟨i, hJ hi⟩
          have hqj : q (P.root i) = 0 := by
            apply hq_mem
            exact Submodule.subset_span ⟨i, hi, rfl⟩
          rw [hqj, base.height_one_of_mem_support j.property]
          norm_num
    have cast_nonpos {i j : ι} (h : P.pairingIn ℤ i j ≤ 0) :
        P.pairingIn ℚ i j ≤ 0 := by
      rw [← P.algebraMap_pairingIn' ℚ ℤ]
      change ((P.pairingIn ℤ i j : ℤ) : ℚ) ≤ 0
      exact_mod_cast h
    have hn : Pairwise fun i j : S =>
        (P.posRootForm ℚ).posForm (v i) (v j) ≤ 0 := by
      rintro ⟨i, hiS⟩ ⟨j, hjS⟩ hij
      have hijv : i ≠ j := fun h => hij (Subtype.ext h)
      rw [(P.posRootForm ℚ).posForm_apply_root_root_le_zero_iff]
      change P.pairingIn ℚ i j ≤ 0
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
            (rootFiber_minimal_pairingIn_le_zero_ordered P base J hJ β j hj hβmin)
      · rcases hi with hi | hi
        · subst i; subst j
          exact cast_nonpos hpairle
        · subst j
          have hβi := rootFiber_minimal_pairingIn_le_zero_ordered
            P base J hJ β i hi hβmin
          have hswap : P.pairingIn ℤ i β ≤ 0 := by
            rw [P.pairingIn_le_zero_iff ℤ]
            exact hβi
          exact cast_nonpos hswap
      · rcases hi with hi | hi <;> rcases hj with hj | hj
        · subst i; subst j; exact (hijv rfl).elim
        · subst i
          exact cast_nonpos
            (rootFiber_minimal_pairingIn_le_zero_ordered P base J hJ α j hj hαmin)
        · subst j
          have hαi := rootFiber_minimal_pairingIn_le_zero_ordered
            P base J hJ α i hi hαmin
          have hswap : P.pairingIn ℤ i α ≤ 0 := by
            rw [P.pairingIn_le_zero_iff ℤ]
            exact hαi
          exact cast_nonpos hswap
        · exact cast_nonpos (base.pairingIn_le_zero_of_ne hijv (hJ hi) (hJ hj))
    have hliSpan : LinearIndependent ℚ v :=
      LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero
        (P.posRootForm ℚ).posForm
        (by simpa using P.posRootForm_rootFormIn_posDef ℚ) f' v hp hn
    have hliM : LinearIndependent ℚ (fun i : S => P.root i.1) := by
      simpa [v, Function.comp_def] using
        hliSpan.map' (P.rootSpan ℚ).subtype (Submodule.ker_subtype _)
    exact hnotLI hliM
  obtain ⟨δ, hδ⟩ := P.root_sub_root_mem_of_pairingIn_pos hpairpos hαβ
  exact ⟨δ, hδ, hδ ▸ hsubQ⟩

set_option maxHeartbeats 800000 in
public theorem relativeRootFiber_unique_max_height
    {k : Type u} [Field k] [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    ∃! γ : { γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root },
      ∀ δ, δ ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root →
        S.D.height δ ≤ S.D.height γ := by
  classical
  let _ := Fintype.ofFinite S.D.Root
  let P := S.pairing
  let base := S.base
  have hsimple : ∀ a, a ∈ S.D.simple ↔ a ∈ base.support :=
    S.rootSystemRealization.2.2.2.1
  have hsimpleSet : (S.D.simple : Set S.D.Root) = (base.support : Set S.D.Root) := by
    ext a
    exact hsimple a
  have hsimpleFinset : S.D.simple.toFinite.toFinset = base.support := by
    ext a
    simp [hsimple a]
  have hJ : S.J ⊆ base.support := fun a ha =>
    (hsimple a).1 (S.J_simple ha)
  have hrootHeight (a : S.D.Root) :
      RelativeRootHeight S.coeff base.support S.J a =
        RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J a := by
    rw [hsimpleFinset]
  have hsource_iff (a : S.D.Root) :
      a ∈ relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root ↔
      (P.root a - P.root S.root ∈ Submodule.span ℚ (P.root '' S.J) ∧
        RelativeRootHeight S.coeff base.support S.J a = S.height) := by
    constructor
    · intro ha
      refine ⟨root_sub_mem_span_of_projection_eq P base S.J S.coeff
          S.simpleRootExpansion (by simpa [RelativeRootFiber, hsimpleSet] using ha.1.2),
        (hrootHeight a).trans ha.2⟩
    · rintro ⟨hspan, hheight⟩
      refine ⟨⟨Set.mem_univ a, ?_⟩, (hrootHeight a).symm.trans hheight⟩
      simpa [hsimpleSet] using projection_eq_of_root_sub_mem_span P base S.J hJ
        S.coeff S.simpleRootExpansion hspan
  have hroot_notspan : P.root S.root ∉ Submodule.span ℚ (P.root '' S.J) := by
    intro hspan
    have hp := root_mem_span_projection_zero P base S.J hJ S.coeff
      S.simpleRootExpansion hspan
    have hz := relativeRootHeight_eq_zero_of_projection_eq_zero
      S.coeff base.support S.J hp
    have hr := (hrootHeight S.root).trans S.root_height
    have hpos : (0 : ℤ) < S.height := by exact_mod_cast S.height_pos
    omega
  have hneg_mem {a : S.D.Root} {g : S.X}
      (ha : a ∈ rootFiber P S.J g) :
      P.reflectionPerm a a ∈ rootFiber P S.J (-g) := by
    change P.root (P.reflectionPerm a a) - (-g) ∈
      Submodule.span ℚ (P.root '' S.J)
    rw [sub_neg_eq_add, P.root_reflectionPerm, P.reflection_apply_self]
    have ha' : P.root a - g ∈ Submodule.span ℚ (P.root '' S.J) := by
      change P.root a - g ∈ Submodule.span ℚ (P.root '' S.J) at ha
      simpa only [P] using ha
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      Submodule.neg_mem _ ha'
  have hneg_source {a : S.D.Root}
      (ha : a ∈ rootFiber P S.J (-P.root S.root))
      (hh : RelativeRootHeight S.coeff base.support S.J a = -S.height) :
      P.reflectionPerm a a ∈
        relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root := by
    apply (hsource_iff _).2
    have hneg := hneg_mem ha
    change P.root (P.reflectionPerm a a) - (-(-P.root S.root)) ∈
      Submodule.span ℚ (P.root '' S.J) at hneg
    refine ⟨by simpa using hneg, ?_⟩
    rw [relativeRootHeight_reflectionPerm_self P base S.J S.coeff
      S.simpleRootExpansion, hh, neg_neg]
  obtain ⟨γ, hγ, hγmax⟩ := relativeRootFiber_exists_max_height
    S.D S.J S.coeff S.height S.root S.root_height
  refine ⟨⟨γ, hγ⟩, hγmax, ?_⟩
  intro η hηmax
  apply Subtype.ext
  by_contra hneq
  have hηdata := (hsource_iff η.1).mp η.2
  have hγdata := (hsource_iff γ).mp hγ
  have hηneg := hneg_mem (g := P.root S.root) hηdata.1
  have hγneg := hneg_mem (g := P.root S.root) hγdata.1
  have hηnegheight : RelativeRootHeight S.coeff base.support S.J
      (P.reflectionPerm η.1 η.1) = -S.height := by
    rw [relativeRootHeight_reflectionPerm_self P base S.J S.coeff
      S.simpleRootExpansion, hηdata.2]
  have hγnegheight : RelativeRootHeight S.coeff base.support S.J
      (P.reflectionPerm γ γ) = -S.height := by
    rw [relativeRootHeight_reflectionPerm_self P base S.J S.coeff
      S.simpleRootExpansion, hγdata.2]
  have hηmin : ∀ w : parabolicWeylSubgroup P S.J,
      base.height (P.reflectionPerm η.1 η.1) ≤
        base.height (P.weylGroupToPerm w.1 (P.reflectionPerm η.1 η.1)) := by
    intro w
    have hwr := parabolicWeylSubgroup_rootFiber_invariant P S.J
      (-P.root S.root) w _ hηneg
    have hwh := parabolicWeylSubgroup_relativeRootHeight_eq P base S.J hJ
      S.coeff S.simpleRootExpansion w (P.reflectionPerm η.1 η.1)
    have hs := hneg_source hwr (hwh.trans hηnegheight)
    have hm := hγmax _ hs
    have hdw := S.rootSystemRealization.2.2.2.2
      (P.reflectionPerm (P.weylGroupToPerm w.1 (P.reflectionPerm η.1 η.1))
        (P.weylGroupToPerm w.1 (P.reflectionPerm η.1 η.1)))
    have hdη := S.rootSystemRealization.2.2.2.2 η.1
    have hdγ := S.rootSystemRealization.2.2.2.2 γ
    rw [hdw, hdγ] at hm
    simp only [Equiv.refl_apply] at hm
    have hnegw := base.height_reflectionPerm_self
      (P.weylGroupToPerm w.1 (P.reflectionPerm η.1 η.1))
    change base.height (P.reflectionPerm
      (P.weylGroupToPerm w.1 (P.reflectionPerm η.1 η.1))
      (P.weylGroupToPerm w.1 (P.reflectionPerm η.1 η.1))) =
      -base.height (P.weylGroupToPerm w.1 (P.reflectionPerm η.1 η.1)) at hnegw
    have hm' : -base.height (P.weylGroupToPerm w.1
        (P.reflectionPerm η.1 η.1)) ≤ base.height γ := by
      calc
        -base.height (P.weylGroupToPerm w.1 (P.reflectionPerm η.1 η.1)) =
            base.height (P.reflectionPerm
              (P.weylGroupToPerm w.1 (P.reflectionPerm η.1 η.1))
              (P.weylGroupToPerm w.1 (P.reflectionPerm η.1 η.1))) := hnegw.symm
        _ ≤ base.height γ := hm
    have heqD : S.D.height η.1 = S.D.height γ := by
      exact le_antisymm (hγmax η.1 η.2) (hηmax γ hγ)
    have heq : base.height η.1 = base.height γ := by
      have hdη' : S.D.height η.1 = base.height η.1 := by
        simpa only [Equiv.refl_apply] using hdη
      have hdγ' : S.D.height γ = base.height γ := by
        simpa only [Equiv.refl_apply] using hdγ
      calc
        base.height η.1 = S.D.height η.1 := hdη'.symm
        _ = S.D.height γ := heqD
        _ = base.height γ := hdγ'
    have hleft := base.height_reflectionPerm_self η.1
    change base.height (P.reflectionPerm η.1 η.1) = -base.height η.1 at hleft
    omega
  have hγmin : ∀ w : parabolicWeylSubgroup P S.J,
      base.height (P.reflectionPerm γ γ) ≤
        base.height (P.weylGroupToPerm w.1 (P.reflectionPerm γ γ)) := by
    intro w
    have hwr := parabolicWeylSubgroup_rootFiber_invariant P S.J
      (-P.root S.root) w _ hγneg
    have hwh := parabolicWeylSubgroup_relativeRootHeight_eq P base S.J hJ
      S.coeff S.simpleRootExpansion w (P.reflectionPerm γ γ)
    have hs := hneg_source hwr (hwh.trans hγnegheight)
    have hm := hγmax _ hs
    have hdw := S.rootSystemRealization.2.2.2.2
      (P.reflectionPerm (P.weylGroupToPerm w.1 (P.reflectionPerm γ γ))
        (P.weylGroupToPerm w.1 (P.reflectionPerm γ γ)))
    rw [hdw, S.rootSystemRealization.2.2.2.2 γ] at hm
    simp only [Equiv.refl_apply] at hm
    have hnegw := base.height_reflectionPerm_self
      (P.weylGroupToPerm w.1 (P.reflectionPerm γ γ))
    change base.height (P.reflectionPerm
      (P.weylGroupToPerm w.1 (P.reflectionPerm γ γ))
      (P.weylGroupToPerm w.1 (P.reflectionPerm γ γ))) =
      -base.height (P.weylGroupToPerm w.1 (P.reflectionPerm γ γ)) at hnegw
    have hm' : -base.height (P.weylGroupToPerm w.1
        (P.reflectionPerm γ γ)) ≤ base.height γ := by
      calc
        -base.height (P.weylGroupToPerm w.1 (P.reflectionPerm γ γ)) =
            base.height (P.reflectionPerm
              (P.weylGroupToPerm w.1 (P.reflectionPerm γ γ))
              (P.weylGroupToPerm w.1 (P.reflectionPerm γ γ))) := hnegw.symm
        _ ≤ base.height γ := hm
    have hleft := base.height_reflectionPerm_self γ
    change base.height (P.reflectionPerm γ γ) = -base.height γ at hleft
    omega
  have hneqneg : P.reflectionPerm η.1 η.1 ≠ P.reflectionPerm γ γ := by
    intro heq
    apply hneq
    apply P.root.injective
    simpa [P.root_reflectionPerm, P.reflection_apply_self] using congrArg P.root heq
  have hnegspan : (-P.root S.root) ∉ Submodule.span ℚ (P.root '' S.J) := by
    intro hz
    apply hroot_notspan
    have hz' : (-P.root S.root) ∈ Submodule.span ℚ (P.root '' S.J) := by
      change (-P.root S.root) ∈ Submodule.span ℚ (P.root '' S.J) at hz
      simpa only [P] using hz
    simpa using Submodule.neg_mem _ hz'
  obtain ⟨δ, hδ, _⟩ := rootFiber_minimal_sub_isRoot_ordered P base S.J hJ
    (-P.root S.root) hnegspan (P.reflectionPerm η.1 η.1)
    (P.reflectionPerm γ γ) hηneg hγneg hneqneg hηmin hγmin
  have hzero : base.height δ = 0 := by
    rw [base.height_sub hδ]
    have hnegη := base.height_reflectionPerm_self η.1
    change base.height (P.reflectionPerm η.1 η.1) = -base.height η.1 at hnegη
    have hnegγ := base.height_reflectionPerm_self γ
    change base.height (P.reflectionPerm γ γ) = -base.height γ at hnegγ
    rw [hnegη, hnegγ]
    have hdη := S.rootSystemRealization.2.2.2.2 η.1
    have hdγ := S.rootSystemRealization.2.2.2.2 γ
    have heq : S.D.height η.1 = S.D.height γ := by
      exact le_antisymm (hγmax η.1 η.2) (hηmax γ hγ)
    have hdη' : S.D.height η.1 = base.height η.1 := by
      simpa only [Equiv.refl_apply] using hdη
    have hdγ' : S.D.height γ = base.height γ := by
      simpa only [Equiv.refl_apply] using hdγ
    calc
      -base.height η.1 - -base.height γ =
          -S.D.height η.1 - -S.D.height γ := by rw [hdη', hdγ']
      _ = 0 := by rw [heq]; simp
  exact (base.height_ne_zero δ) hzero

end

end Theory.AlgebraicGroup
