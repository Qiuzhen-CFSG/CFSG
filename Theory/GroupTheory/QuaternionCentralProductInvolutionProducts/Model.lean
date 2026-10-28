module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fintype.Sum

/-!
# Norms in the diagonal quotient of two quaternion groups

For an outer involution of Q₈, a central norm is one. Among the six
noncentral elements, two have norm square one and four have norm square
equal to the central involution. These small kernel-checked tables use the
quaternion generator-pair parametrization of
`QuaternionCentralProductOuterInvolution`.

The two possible orders of these factor types give 2·4 + 4·2 = 16 pairs.
A surjective homomorphism with diagonal central kernel identifies each pair
with precisely one other pair, giving eight qualifying elements in its target.
The central-norm assertion follows by testing commutation with each factor.

Source: Aschbacher, *A 2-local characterization of M12*, Lemma 2.3 and the
product calculation in the proof of Lemma 4.3, printed pp.33–34 and 39–40.
-/

namespace QuaternionInvolutionProducts
public abbrev Q8 := QuaternionGroup 2
private def pairMap (p : Q8 × Q8) : Q8 → Q8
  | .a i => p.1 ^ i.val
  | .xa i => p.2 * p.1 ^ i.val
private def goodPair (p : Q8 × Q8) : Prop :=
  p.1 ^ 2 = QuaternionGroup.a 2 ∧ p.2 ^ 2 = QuaternionGroup.a 2 ∧
    p.1 * p.2 ≠ p.2 * p.1
private instance : DecidablePred goodPair := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private abbrev Pairs := {p : Q8 × Q8 // goodPair p}
private theorem aut_pair (e : MulAut Q8) : ∃ p : Pairs, ∀ x, pairMap p.val x = e x := by
  have hs : ∀ x : Q8, x^2 ≠ 1 → x^2 = QuaternionGroup.a 2 := by decide
  have hsq (x : Q8) (hx : x^2 ≠ 1) : (e x)^2 = QuaternionGroup.a 2 := by
    apply hs
    intro he
    apply hx
    apply e.injective
    simpa only [map_pow, map_one] using he
  refine ⟨⟨(e (.a 1), e (.xa 0)), hsq _ (by decide), hsq _ (by decide), ?_⟩, ?_⟩
  · intro he
    have hn : (QuaternionGroup.a 1 : Q8) * .xa 0 ≠ .xa 0 * .a 1 := by decide
    apply hn
    apply e.injective
    simpa only [map_mul] using he
  · intro x
    cases x with
    | a i =>
      change (e (QuaternionGroup.a 1))^i.val = e (QuaternionGroup.a i)
      rw [← map_pow, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    | xa i =>
      change e (QuaternionGroup.xa 0) * (e (QuaternionGroup.a 1))^i.val = e (QuaternionGroup.xa i)
      rw [← map_pow, ← map_mul, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val,
        QuaternionGroup.xa_mul_a, zero_add]

public abbrev Pair := Q8 × Q8
public abbrev centralInvolution : Q8 := QuaternionGroup.a 2
public abbrev diagonalKernel (x : Pair) : Prop := x = 1 ∨ x = (centralInvolution,centralInvolution)
private def outer (p : Pairs) : Prop :=
  (∀ x : Q8, pairMap p.val (pairMap p.val x) = x) ∧
  (¬ ∃ b : Q8, ∀ x : Q8, pairMap p.val x = b*x*b⁻¹)
private instance : DecidablePred outer := fun _ => inferInstanceAs (Decidable (_ ∧ _))
private abbrev Outer := {p : Pairs // outer p}
private theorem norm_central : ∀ p : Outer, ∀ x : Q8,
    (pairMap p.val.val x * x)^2 = 1 → pairMap p.val.val x * x = 1 := by decide
private abbrev short (p : Outer) (x : Q8) : Prop :=
  x^2=centralInvolution ∧ (pairMap p.val.val x*x)^2=1
private abbrev long (p : Outer) (x : Q8) : Prop :=
  x^2=centralInvolution ∧ (pairMap p.val.val x*x)^2=centralInvolution
private theorem factor_counts : ∀ p : Outer,
    Fintype.card {x : Q8 // short p x}=2 ∧
    Fintype.card {x : Q8 // long p x}=4 := by decide
private theorem central_input : ∀ p : Outer, ∀ x : Q8,
    x^2=1 → (pairMap p.val.val x*x)^2=1 := by decide
private theorem squares : ∀ x : Q8, x^2=1 ∨ x^2=centralInvolution := by decide
private theorem pair_criterion (x y u v : Q8)
    (hu : x^2=1 → u^2=1) (hv : y^2=1 → v^2=1) :
    diagonalKernel ((x,y)^2) ∧ ¬diagonalKernel ((u,v)^2) ↔
      (x^2=centralInvolution ∧ u^2=1) ∧ (y^2=centralInvolution ∧ v^2=centralInvolution) ∨
      (x^2=centralInvolution ∧ u^2=centralInvolution) ∧ (y^2=centralInvolution ∧ v^2=1) := by
  have hne : centralInvolution≠(1:Q8) := by decide
  have hne' : (1:Q8)≠centralInvolution := hne.symm
  rcases squares x with hx | hx <;> rcases squares y with hy | hy <;>
    rcases squares u with hu' | hu' <;> rcases squares v with hv' | hv' <;>
    simp_all [diagonalKernel, Prod.ext_iff]
private theorem pair_count (p q : Outer) :
    Fintype.card {x : Pair // diagonalKernel (x^2) ∧
      ¬diagonalKernel ((pairMap p.val.val x.1 * x.1, pairMap q.val.val x.2 * x.2)^2)} = 16 := by
  have hi (x : Pair) :
      diagonalKernel (x^2) ∧ ¬diagonalKernel ((pairMap p.val.val x.1*x.1, pairMap q.val.val x.2*x.2)^2) ↔
        short p x.1 ∧ long q x.2 ∨ long p x.1 ∧ short q x.2 :=
    pair_criterion x.1 x.2 _ _ (central_input p x.1) (central_input q x.2)
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hi),
    Fintype.card_subtype_or_disjoint _ _ (fun _ ha hb x hc =>
      (by decide : centralInvolution≠(1:Q8)) ((hb x hc).1.2.symm.trans (ha x hc).1.2)),
    Fintype.card_congr (@Equiv.subtypeProdEquivProd Q8 Q8 (short p) (long q)),
    Fintype.card_congr (@Equiv.subtypeProdEquivProd Q8 Q8 (long p) (short q)),
    Fintype.card_prod, Fintype.card_prod,
    (factor_counts p).1, (factor_counts p).2, (factor_counts q).1, (factor_counts q).2]

private theorem outer_pair (e : MulAut Q8) (he : e^2 = 1)
    (ho : ¬ ∃ b : Q8, ∀ x : Q8, e x = b*x*b⁻¹) :
    ∃ p : Outer, ∀ x, pairMap p.val.val x = e x := by
  obtain ⟨p, hp⟩ := aut_pair e
  refine ⟨⟨p, ?_, ?_⟩, hp⟩
  · intro x
    rw [hp, hp]
    simpa [pow_two] using DFunLike.congr_fun he x
  · simpa only [hp] using ho

private theorem center_sq : ∀ x : Q8, (∀ y : Q8, y*x=x*y) → x^2=1 := by decide

private theorem card_preimage {G K : Type*} [Group G] [Group K]
    (f : G →* K) (hf : Function.Surjective f) (s : Set K) :
    Nat.card {x : G // f x ∈ s} = Nat.card f.ker * Nat.card s := by
  classical
  let lift : K → G := fun x => (hf x).choose
  have hl (x : K) : f (lift x) = x := (hf x).choose_spec
  let e : {x : G // f x ∈ s} ≃ f.ker × s :=
    { toFun := fun x => (⟨x.val * (lift (f x.val))⁻¹, by simp [hl]⟩, ⟨f x.val, x.property⟩)
      invFun := fun x => ⟨x.1.val * lift x.2.val, by simp [hl, MonoidHom.mem_ker.mp x.1.property]⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by
        rintro ⟨x,y⟩
        apply Prod.ext
        · apply Subtype.ext
          simp [hl, MonoidHom.mem_ker.mp x.property]
        · apply Subtype.ext
          simp [hl, MonoidHom.mem_ker.mp x.property] }
  rw [Nat.card_congr e, Nat.card_prod]

/-- Transport the norm calculation through a surjection with the actual diagonal kernel. -/
public theorem norms_of_diagonal_kernel {G : Type*} [Group G]
    (f : Pair →* G) (hf : Function.Surjective f)
    (hk : ∀ x : Pair, f x = 1 ↔ diagonalKernel x)
    (a b : MulAut Q8) (ha : a^2=1) (hb : b^2=1)
    (hao : ¬ ∃ c : Q8, ∀ x : Q8, a x = c*x*c⁻¹)
    (hbo : ¬ ∃ c : Q8, ∀ x : Q8, b x = c*x*c⁻¹)
    (α : MulAut G) (he : ∀ x : Pair, f (a x.1, b x.2) = α (f x)) :
    (∀ x : G, α x*x ∈ Subgroup.center G → α x*x=1) ∧
    Nat.card {x : G // x^2=1 ∧ (α x*x)^2≠1} = 8 := by
  classical
  obtain ⟨p,hp⟩ := outer_pair a ha hao
  obtain ⟨q,hq⟩ := outer_pair b hb hbo
  let n (x : Pair) : Pair := (a x.1*x.1, b x.2*x.2)
  have hn (x : Pair) : f (n x) = α (f x)*f x := by
    change f ((a x.1,b x.2)*x) = _
    rw [map_mul, he]
  constructor
  · intro x hx
    obtain ⟨y,rfl⟩ := hf x
    have hc (v : Pair) : diagonalKernel (v*n y*(n y*v)⁻¹) := by
      apply (hk _).mp
      rw [map_mul, map_mul, map_inv, map_mul, hn,
        Subgroup.mem_center_iff.mp hx (f v), mul_inv_cancel]
    have hleft : (a y.1*y.1)^2=1 := by
      apply center_sq
      intro v
      rcases hc (v,1) with hh | hh
      · have hh' := congrArg Prod.fst hh
        change (v*(a y.1*y.1))*((a y.1*y.1)*v)⁻¹=1 at hh'
        exact mul_inv_eq_one.mp hh'
      · have hh' := congrArg Prod.snd hh
        change (1*(b y.2*y.2))*((b y.2*y.2)*1)⁻¹=centralInvolution at hh'
        simp only [one_mul, mul_one, mul_inv_cancel] at hh'
        exact (by decide : (1:Q8)≠centralInvolution) hh' |>.elim
    have hright : (b y.2*y.2)^2=1 := by
      apply center_sq
      intro v
      rcases hc (1,v) with hh | hh
      · have hh' := congrArg Prod.snd hh
        change (v*(b y.2*y.2))*((b y.2*y.2)*v)⁻¹=1 at hh'
        exact mul_inv_eq_one.mp hh'
      · have hh' := congrArg Prod.fst hh
        change (1*(a y.1*y.1))*((a y.1*y.1)*1)⁻¹=centralInvolution at hh'
        simp only [one_mul, mul_one, mul_inv_cancel] at hh'
        exact (by decide : (1:Q8)≠centralInvolution) hh' |>.elim
    have hl : a y.1*y.1=1 := by simpa only [hp] using norm_central p y.1 (by simpa only [hp] using hleft)
    have hr : b y.2*y.2=1 := by simpa only [hq] using norm_central q y.2 (by simpa only [hq] using hright)
    rw [← hn]
    have hy : n y=1 := Prod.ext hl hr
    rw [hy, map_one]
  · let s : Set G := {x | x^2=1 ∧ (α x*x)^2≠1}
    have hs (x : Pair) : f x ∈ s ↔ diagonalKernel (x^2) ∧ ¬diagonalKernel ((n x)^2) := by
      change (f x)^2=1 ∧ (α (f x)*f x)^2≠1 ↔ _
      rw [← hn, ← map_pow, ← map_pow, ne_eq, hk, hk]
    have hc : Nat.card {x : Pair // f x ∈ s}=16 := by
      rw [Nat.card_congr (Equiv.subtypeEquivRight hs), Nat.card_eq_fintype_card]
      simpa only [hp,hq] using pair_count p q
    have hkcard : Nat.card f.ker=2 := by
      have e : f.ker ≃ {x : Pair // diagonalKernel x} := Equiv.subtypeEquivRight hk
      rw [Nat.card_congr e, Nat.card_eq_fintype_card]
      decide
    have hh := card_preimage f hf s
    rw [hc,hkcard] at hh
    change Nat.card s=8
    omega
end QuaternionInvolutionProducts
