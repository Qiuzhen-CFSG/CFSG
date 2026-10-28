module

public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Theory.GroupTheory.WordSubgroup

/-!
# Automorphism certificates from profiles on the Frattini quotient

An automorphism-invariant label on a finite p-group induces a profile on
its Frattini quotient: each coset is labelled by the number of elements
of each label. Every induced automorphism preserves these profiles. Thus
if the profile-preserving automorphisms of an explicit model of the
quotient have p-power order, the full automorphism group is a p-group,
by the Burnside basis-kernel theorem.

The labels may be element orders, centralizer orders, or any other
intrinsic invariant. The counting lemma is independent of the quotient
construction and includes a finite-filter formula for checked computation.
This is an elementary consequence of the Frattini automorphism kernel
proved in `FrattiniAutomorphismKernel`.
-/

namespace Subgroup

variable {G Q A : Type*}

/-- Counts of intrinsic labels in the fibers of a map. -/
public noncomputable def fiberProfile (q : G → Q) (label : G → A) (y : Q) (a : A) : ℕ :=
  Nat.card {x : G // q x = y ∧ label x = a}

/-- Profiles can be evaluated by a finite filter. -/
public theorem fiberProfile_eq_card_filter [Fintype G] [DecidableEq Q] [DecidableEq A]
    (q : G → Q) (label : G → A) (y : Q) (a : A) :
    fiberProfile q label y a =
      (Finset.univ.filter (fun x => q x = y ∧ label x = a)).card := by
  unfold fiberProfile
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Equivariant bijections preserving labels preserve their fiber counts. -/
public theorem fiberProfile_map (q : G → Q) (label : G → A)
    (f : G ≃ G) (b : Q ≃ Q)
    (hq : ∀ x, q (f x) = b (q x)) (hl : ∀ x, label (f x) = label x)
    (y : Q) : fiberProfile q label (b y) = fiberProfile q label y := by
  funext a
  apply (Nat.card_congr (f.subtypeEquiv (fun x => ?_))).symm
  rw [hq, hl, b.injective.eq_iff]

variable [Group G] [Group Q]

/-- A profile certificate on any explicit Frattini quotient model implies
that the full automorphism group is a p-group. -/
public theorem isPGroup_mulAut_of_frattini_profile [Finite G] {p : ℕ}
    (hG : IsPGroup p G) (e : (G ⧸ frattini G) ≃* Q) (label : G → A)
    (hl : ∀ (f : MulAut G) x, label (f x) = label x)
    (cert : ∀ b : MulAut Q,
      (∀ y, fiberProfile (fun x => e (QuotientGroup.mk' (frattini G) x)) label (b y) =
        fiberProfile (fun x => e (QuotientGroup.mk' (frattini G) x)) label y) →
      ∃ k : ℕ, b ^ (p ^ k) = 1) :
    IsPGroup p (MulAut G) := by
  intro f
  let a := quotientAut (frattini G) f
  let b := MulAut.congr e a
  have hp : ∀ y,
      fiberProfile (fun x => e (QuotientGroup.mk' (frattini G) x)) label (b y) =
      fiberProfile (fun x => e (QuotientGroup.mk' (frattini G) x)) label y := by
    apply fiberProfile_map _ _ f.toEquiv b.toEquiv
    · intro x
      change e (QuotientGroup.mk' (frattini G) (f x)) =
        e (a (e.symm (e (QuotientGroup.mk' (frattini G) x))))
      rw [e.symm_apply_apply]
      simp only [a, quotientAut_apply_mk]
    · exact hl f
  obtain ⟨k, hk⟩ := cert b hp
  have ha : a ^ (p ^ k) = 1 := by
    apply (MulAut.congr e).injective
    simpa only [map_pow, map_one] using hk
  have hmem : f ^ (p ^ k) ∈ (quotientAut (frattini G)).ker := by
    change quotientAut (frattini G) (f ^ (p ^ k)) = 1
    rw [map_pow]
    exact ha
  obtain ⟨m, hm⟩ := isPGroup_quotientAut_frattini_kernel hG
    (⟨f ^ (p ^ k), hmem⟩ : (quotientAut (frattini G)).ker)
  refine ⟨k + m, ?_⟩
  have hm' := congrArg Subtype.val hm
  change (f ^ (p ^ k)) ^ (p ^ m) = 1 at hm'
  simpa only [pow_add, pow_mul] using hm'

/-- Element order is an intrinsic label for fiber-profile certificates. -/
public theorem orderOf_mulAut (f : MulAut G) (x : G) : orderOf (f x) = orderOf x :=
  orderOf_injective f.toMonoidHom f.injective x

/-- Centralizer order is an intrinsic label for fiber-profile certificates. -/
public theorem card_centralizer_mulAut (f : MulAut G) (x : G) :
    Nat.card (centralizer ({f x} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
  apply (Nat.card_congr (f.toEquiv.subtypeEquiv (fun y => ?_))).symm
  change y ∈ centralizer ({x} : Set G) ↔ f y ∈ centralizer ({f x} : Set G)
  simp only [mem_centralizer_singleton_iff, ← map_mul, f.injective.eq_iff]

/-- The joint order and centralizer-order label is automorphism invariant. -/
public theorem order_centralizer_label_mulAut (f : MulAut G) (x : G) :
    (orderOf (f x), Nat.card (centralizer ({f x} : Set G))) =
      (orderOf x, Nat.card (centralizer ({x} : Set G))) := by
  rw [orderOf_mulAut, card_centralizer_mulAut]

end Subgroup

namespace Theory.GroupTheory

variable {Q A : Type*} [Group Q] {n : ℕ}

/-- A finite certificate over generator images, with color and identity-fiber
checks to prune tuples that cannot come from automorphisms. Only the small
quotient group, rather than the original p-group, needs to be enumerated. -/
@[expose] public def ProfileWordCertificate (gen : Fin n → Q)
    (word : Q → List (Fin n)) (color : Q → A) (m : ℕ) : Prop :=
  ∀ v : Fin n → Q,
    (∀ x, color (evalWord v (word x)) = color x) →
    (∀ x, evalWord v (word x) = 1 ↔ x = 1) →
    ∀ j, (fun x => evalWord v (word x))^[m] (gen j) = gen j

public instance [Fintype Q] [DecidableEq Q] [DecidableEq A]
    (gen : Fin n → Q) (word : Q → List (Fin n)) (color : Q → A) (m : ℕ) :
    Decidable (ProfileWordCertificate gen word color m) := by
  unfold ProfileWordCertificate
  infer_instance

/-- A successful generator-image certificate bounds every color-preserving
quotient automorphism's order. The normal forms and certificate are separate
finite mathematical obligations. -/
public theorem ProfileWordCertificate.pow_eq_one
    {gen : Fin n → Q} {word : Q → List (Fin n)} {color : Q → A} {m : ℕ}
    (cert : ProfileWordCertificate gen word color m)
    (hw : ∀ x, evalWord gen (word x) = x)
    (b : MulAut Q) (hb : ∀ x, color (b x) = color x) : b ^ m = 1 := by
  have hmap (f : Q →* Q) (w : List (Fin n)) :
      evalWord (fun j => f (gen j)) w = f (evalWord gen w) := by
    induction w with
    | nil => exact f.map_one.symm
    | cons j w ih => simp only [evalWord, map_mul, ih]
  have hrec (x : Q) : evalWord (fun j => b (gen j)) (word x) = b x :=
    (hmap b.toMonoidHom _).trans (congrArg b (hw x))
  have hfix := cert (fun j => b (gen j))
    (fun x => (congrArg color (hrec x)).trans (hb x))
    (fun x => by rw [hrec]; exact b.map_eq_one_iff)
  have hrecfun : (fun x => evalWord (fun j => b (gen j)) (word x)) = b := funext hrec
  rw [hrecfun] at hfix
  have hiter (r : ℕ) (x : Q) : b^[r] x = (b ^ r) x := by
    induction r with
    | zero => rfl
    | succ r ih => rw [Function.iterate_succ_apply', ih, pow_succ', MulAut.mul_apply]
  have hgen : ∀ j, (b ^ m) (gen j) = gen j := by
    intro j
    rw [← hiter]
    exact hfix j
  apply MulEquiv.ext
  intro x
  change (b ^ m) x = x
  calc
    (b ^ m) x = evalWord (fun j => (b ^ m) (gen j)) (word x) := by
      exact ((hmap (b ^ m).toMonoidHom _).trans (congrArg (b ^ m) (hw x))).symm
    _ = evalWord gen (word x) := by simp only [hgen]
    _ = x := hw x

end Theory.GroupTheory

namespace Subgroup

/-- A finite word certificate for a coloring distinguished by intrinsic fiber
profiles proves the full automorphism group is a p-group. The color may retain
only selected counts, so no enumeration of an infinite label type is required. -/
public theorem isPGroup_mulAut_of_frattini_word_profile
    {G Q A B : Type*} [Group G] [Finite G] [Group Q] {p n k : ℕ}
    (hG : IsPGroup p G) (e : (G ⧸ frattini G) ≃* Q) (label : G → A)
    (hl : ∀ (f : MulAut G) x, label (f x) = label x)
    (gen : Fin n → Q) (word : Q → List (Fin n)) (color : Q → B)
    (hw : ∀ x, Theory.GroupTheory.evalWord gen (word x) = x)
    (hcolor : ∀ x y,
      fiberProfile (fun g => e (QuotientGroup.mk' (frattini G) g)) label x =
        fiberProfile (fun g => e (QuotientGroup.mk' (frattini G) g)) label y →
      color x = color y)
    (cert : Theory.GroupTheory.ProfileWordCertificate gen word color (p ^ k)) :
    IsPGroup p (MulAut G) := by
  apply isPGroup_mulAut_of_frattini_profile hG e label hl
  intro b hb
  exact ⟨k, cert.pow_eq_one hw b (fun x => hcolor (b x) x (hb x))⟩

end Subgroup
