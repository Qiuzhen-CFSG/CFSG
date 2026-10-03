module
public import ABG.ChapterII.Section1.GeneratorNoncommutative
public import ABG.ChapterII.Section1.PresentationCalculus
public import Theory.GroupTheory.DihedralPresentation
public import Theory.GroupTheory.QuaternionPresentation
/-!
# The three explicit index-two subgroups of a quasi-dihedral group

For the actual semidihedral presentation with `|G| = 2^n`, `n ≥ 4`,
`C = ⟨a⟩`, `D = ⟨a²,b⟩`, and `Q = ⟨a²,ab⟩` all have index two.
The first is cyclic; the latter two are isomorphic to the standard dihedral
and generalized quaternion groups of order `2^(n-1)`.

The shared two-form closure induction applies when the outer generator has its square
in the cyclic subgroup. The rotation `a` is outside both `D` and `Q`:
its order excludes an even-power normal form, and an outer normal form would
put `b` in `⟨a⟩`, contradicting noncommutation. Splitting ambient normal forms
by parity then gives index two. Inside each subgroup, `a²` has order
`2^(n-2)` and its second generator inverts it. The square of `ab` is the
half-order power of `a²`. The generic dihedral and quaternion presentation
recognizers finish using the cardinalities obtained from the indices.

This is the model-identification part of Chapter II, §1, Lemma 1(iii),
article page 9 of `refs/latex/alperin-brauer-gorenstein.tex`, from the
presentation on article page 2. Maximality and exhaustion are assembled in
the maximal-subgroups module. Stellmacher's parameter `n` is one larger
than the article's parameter.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]
private theorem square_order {n : ℕ} (hn : 4 ≤ n) {a : G}
    (ha : orderOf a = 2 ^ (n-1)) : orderOf (a^2) = 2^(n-2) := by
  have he : n-1 = (n-2)+1 := by omega
  have hd : 2 ∣ orderOf a := by rw [ha, he, pow_succ]; exact dvd_mul_left _ _
  rw [orderOf_pow_of_dvd (by decide) hd, ha, he, pow_succ, Nat.mul_div_cancel]
  decide

private theorem generator_not_square {n : ℕ} (hn : 4 ≤ n) {a : G}
    (ha : orderOf a = 2 ^ (n-1)) : a ∉ Subgroup.zpowers (a^2) := by
  intro h
  have hd := orderOf_dvd_of_mem_zpowers h
  rw [ha, square_order hn ha] at hd
  have hle := Nat.le_of_dvd (by positivity) hd
  have hlt : 2^(n-2) < 2^(n-1) := Nat.pow_lt_pow_right (by omega) (by omega)
  omega

private theorem outer_not_cyclic {n : ℕ} (hn : 4 ≤ n) {a b : G}
    (ha : orderOf a = 2 ^ (n-1))
    (hconj : b*a*b⁻¹=a^(2^(n-2)-1)) : b ∉ Subgroup.zpowers a := by
  rintro ⟨i, rfl⟩
  exact generators_not_commute hn ha hconj (Commute.self_zpow a i)

private theorem conjugate_square (a b : G) (k : ℕ)
    (hconj : b*a*b⁻¹=a^k) : b*a^2*b⁻¹=(a^2)^k := by
  have h := congrArg (fun x : G => x^2) hconj
  rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply] at h
  simpa only [← pow_mul, Nat.mul_comm] using h

private theorem outer_conjugate_square (a b : G) (k : ℕ)
    (hconj : b*a*b⁻¹=a^k) : (a*b)*a^2*(a*b)⁻¹=(a^2)^k := by
  calc
    (a*b)*a^2*(a*b)⁻¹ = a*(b*a^2*b⁻¹)*a⁻¹ := by group
    _ = a*(a^2)^k*a⁻¹ := by rw [conjugate_square a b k hconj]
    _ = (a^2)^k := by rw [← pow_mul, (Commute.self_pow a _).eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem generator_not_two_generator (a d : G) (k : ℕ) (r : ℤ)
    (ha : a ∉ Subgroup.zpowers (a^2)) (hd : d ∉ Subgroup.zpowers a)
    (hsq : d^2=(a^2)^r) (hconj : d*a^2*d⁻¹=(a^2)^k) :
    a ∉ Subgroup.closure ({a^2,d} : Set G) := by
  intro hx
  obtain ⟨i, he | he⟩ := square_normal_form_int (a^2) d k r hsq hconj a hx
  · exact ha ((congrArg (fun x => x ∈ Subgroup.zpowers (a^2)) he).mpr
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _))
  · apply hd
    have hc : (a^2)^i ∈ Subgroup.zpowers a :=
      Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _) _
    have hh := (Subgroup.zpowers a).mul_mem ((Subgroup.zpowers a).inv_mem hc) (Subgroup.mem_zpowers a)
    have heq : ((a^2)^i)⁻¹*a=d := by
      calc
        _ = ((a^2)^i)⁻¹*((a^2)^i*d) := congrArg (fun x => ((a^2)^i)⁻¹*x) he
        _ = d := by group
    simpa only [heq] using hh

private theorem index_two_of_normal_forms (a b : G) (H : Subgroup G)
    (ha : a ∉ H) (hsq : a^2 ∈ H) (hout : b ∈ H ∨ a*b ∈ H)
    (hnf : ∀ x : G, ∃ i : ℕ, x=a^i ∨ x=a^i*b) : H.index=2 := by
  apply Subgroup.index_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨a, ha, ?_⟩
  intro x
  have hp (i : ℕ) : a^i=(a^2)^(i/2)*a^(i%2) := by rw [← pow_mul, ← pow_add]; congr 1; omega
  obtain ⟨i, rfl | rfl⟩ := hnf x
  · by_cases hi : i%2=0
    · right; rw [hp, hi, pow_zero, mul_one]; exact H.pow_mem hsq _
    · left
      have hi' : i%2=1 := by omega
      have he : a*a^i=(a^2)^((i+1)/2) := by rw [← pow_mul, ← pow_succ']; congr 1; omega
      rw [he]; exact H.pow_mem hsq _
  · rcases hout with hb | hab
    · by_cases hi : i%2=0
      · right; rw [hp, hi, pow_zero, mul_one]; exact H.mul_mem (H.pow_mem hsq _) hb
      · left
        have hi' : i%2=1 := by omega
        have he : a*(a^i*b)=(a^2)^((i+1)/2)*b := by rw [← mul_assoc, ← pow_succ', ← pow_mul]; congr 2; omega
        rw [he]; exact H.mul_mem (H.pow_mem hsq _) hb
    · by_cases hi : i%2=0
      · left
        have he : a*(a^i*b)=(a^2)^(i/2)*(a*b) := by rw [hp, hi, pow_zero, mul_one, ← pow_mul]; group
        rw [he]; exact H.mul_mem (H.pow_mem hsq _) hab
      · right
        have hi' : i%2=1 := by omega
        rw [hp, hi', pow_one, mul_assoc]; exact H.mul_mem (H.pow_mem hsq _) hab
private theorem square_conjugate_inverse {n : ℕ} (hn : 4≤n) (a b : G)
    (ha : orderOf a=2^(n-1)) (hconj : b*a*b⁻¹=a^(2^(n-2)-1)) :
    b*a^2*b⁻¹=(a^2)⁻¹ := by
  rw [conjugate_square a b _ hconj]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  have hh : 1≤2^(n-2) := Nat.one_le_pow _ _ (by decide)
  rw [Nat.sub_add_cancel hh, ← square_order hn ha, pow_orderOf_eq_one]

/-- The explicit cyclic, dihedral, and quaternion subgroups have index two,
with their standard abstract models (ABG II.1.1(iii)). -/
public theorem explicit_subgroup_models {n : ℕ} (hn : 4≤n) (a b : G)
    (hcard : Nat.card G=2^n) (ha : orderOf a=2^(n-1)) (hb : orderOf b=2)
    (hconj : b*a*b⁻¹=a^(2^(n-2)-1))
    (hgen : Subgroup.closure ({a,b}:Set G)=⊤) :
    (Subgroup.zpowers a).index=2 ∧
    (Subgroup.closure ({a^2,b}:Set G)).index=2 ∧
    (Subgroup.closure ({a^2,a*b}:Set G)).index=2 ∧
    IsCyclic (Subgroup.zpowers a) ∧
    Nonempty ((Subgroup.closure ({a^2,b}:Set G)) ≃* DihedralGroup (2^(n-2))) ∧
    Nonempty ((Subgroup.closure ({a^2,a*b}:Set G)) ≃* QuaternionGroup (2^(n-3))) := by
  have hbn := outer_not_cyclic hn ha hconj
  have han := generator_not_square hn ha
  have hb2 : b^2=1 := by rw [← hb]; exact pow_orderOf_eq_one _
  have habn : a*b ∉ Subgroup.zpowers a := by
    intro h
    have hh := (Subgroup.zpowers a).mul_mem ((Subgroup.zpowers a).inv_mem (Subgroup.mem_zpowers a)) h
    exact hbn (by simpa only [← mul_assoc, inv_mul_cancel, one_mul] using hh)
  have habsq : (a*b)^2=(a^2)^(2^(n-3):ℕ) := by
    have hh := outer_square hn a b hb hconj 1
    rw [pow_one, mul_one] at hh
    rw [hh, ← pow_mul]
    congr 1
    rw [show n-2=(n-3)+1 by omega, pow_succ]; omega
  have hDn : a ∉ Subgroup.closure ({a^2,b}:Set G) :=
    generator_not_two_generator a b _ 0 han hbn (by simpa) (conjugate_square a b _ hconj)
  have hQn : a ∉ Subgroup.closure ({a^2,a*b}:Set G) :=
    generator_not_two_generator a (a*b) _ (2^(n-3):ℕ) han habn (by simpa only [zpow_natCast] using habsq)
      (outer_conjugate_square a b _ hconj)
  have hnf (x : G) : ∃ i : ℕ, x=a^i ∨ x=a^i*b := by
    obtain ⟨i, _, hi⟩ := normal_form a b _ _ (by positivity) ha hb2 hconj hgen x
    exact ⟨i,hi⟩
  have hC : (Subgroup.zpowers a).index=2 := by
    apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
    refine ⟨b,hbn,?_⟩
    intro x
    obtain ⟨i,rfl|rfl⟩ := hnf x
    · right; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · left
      have hbb : b*b=1 := by simpa [pow_two] using hb2
      rw [mul_assoc, hbb, mul_one]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hD : (Subgroup.closure ({a^2,b}:Set G)).index=2 :=
    index_two_of_normal_forms a b _ hDn (Subgroup.subset_closure (by simp))
      (Or.inl (Subgroup.subset_closure (by simp))) hnf
  have hQ : (Subgroup.closure ({a^2,a*b}:Set G)).index=2 :=
    index_two_of_normal_forms a b _ hQn (Subgroup.subset_closure (by simp))
      (Or.inr (Subgroup.subset_closure (by simp))) hnf
  refine ⟨hC,hD,hQ,inferInstance,?_,?_⟩
  · let D := Subgroup.closure ({a^2,b}:Set G)
    let c : D := ⟨a^2,Subgroup.subset_closure (by simp)⟩
    let d : D := ⟨b,Subgroup.subset_closure (by simp)⟩
    have hc : orderOf c=2^(n-2) := by
      rw [← orderOf_injective D.subtype D.subtype_injective]
      exact square_order hn ha
    have hd : d^2=1 := by apply Subtype.ext; exact hb2
    have hinv : d*c*d⁻¹=c⁻¹ := by apply Subtype.ext; exact square_conjugate_inverse hn a b ha hconj
    have hcd : Subgroup.closure ({c,d}:Set D)=⊤ := generated_subtype (a^2) b
    have hcardD : Nat.card D=2*2^(n-2) := by
      have hh := D.card_mul_index
      change Nat.card D * (Subgroup.closure ({a^2,b}:Set G)).index=Nat.card G at hh
      rw [hD,hcard,show n=(n-2)+2 by omega,pow_add] at hh
      norm_num at hh
      omega
    exact dihedralGroup_equiv_of_presentation (by positivity) c d hc hd hinv hcd hcardD
  · let Q := Subgroup.closure ({a^2,a*b}:Set G)
    let c : Q := ⟨a^2,Subgroup.subset_closure (by simp)⟩
    let d : Q := ⟨a*b,Subgroup.subset_closure (by simp)⟩
    have hc : orderOf c=2*2^(n-3) := by
      rw [← orderOf_injective Q.subtype Q.subtype_injective]
      change orderOf (a^2)=2*2^(n-3)
      rw [square_order hn ha,show n-2=(n-3)+1 by omega,pow_succ,Nat.mul_comm]
    have hd : d^2=c^(2^(n-3)) := by apply Subtype.ext; exact habsq
    have hinv : d*c*d⁻¹=c⁻¹ := by
      apply Subtype.ext
      change (a*b)*a^2*(a*b)⁻¹=(a^2)⁻¹
      rw [outer_conjugate_square a b _ hconj]
      rw [← conjugate_square a b _ hconj]
      exact square_conjugate_inverse hn a b ha hconj
    have hcd : Subgroup.closure ({c,d}:Set Q)=⊤ := generated_subtype (a^2) (a*b)
    have hcardQ : Nat.card Q=4*2^(n-3) := by
      have hh := Q.card_mul_index
      change Nat.card Q * (Subgroup.closure ({a^2,a*b}:Set G)).index=Nat.card G at hh
      rw [hQ,hcard,show n=(n-3)+3 by omega,pow_add] at hh
      norm_num at hh
      omega
    exact QuaternionGroup.quaternionGroup_equiv_of_presentation (by positivity) c d hc hd hinv hcd hcardQ
end ABG.QuasiDihedral
