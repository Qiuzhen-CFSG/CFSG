module
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Marked
public import Theory.SpecificGroups.SymmetricFiveSubgroups
public import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic
/-!
# The normalizer action in the A₆ fusion argument

Conjugation restricts to the actual set β = zᴳ ∩ A. Because the four marked
generators belong to β and generate A, its action kernel is precisely C_G(A)
inside N_G(A). Thus the permutation image is the faithful induced automizer.
Orbit-stabilizer computes its order from transitivity and the point stabilizer.
When β has five points and that stabilizer has order six, relabeling the
constructed action embeds its image into S₅, contradicting the order-thirty
obstruction.

The local stabilizer calculation and both fusion arguments remain obligations
of the branch proofs. These conditional helpers neither assume an action of
order thirty nor assert a proof of 16.4.9(2).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.Six
open Equiv Equiv.Perm Subgroup
variable {G : Type*} [Group G] {L : Subgroup G} {z r : G}

theorem conjugate_mem_beta_iff (M : AlternatingProductModel L z r 6)
    (n : normalizer (elementary M : Set G)) (a : G) :
    MulAut.conj (n : G) a ∈ beta M ↔ a ∈ beta M := by
  have hc : IsConj a (MulAut.conj (n : G) a) := isConj_iff.mpr ⟨n, rfl⟩
  constructor
  · rintro ⟨ha, hz⟩
    exact ⟨(n.property a).mpr ha, hz.trans hc.symm⟩
  · rintro ⟨ha, hz⟩
    exact ⟨(n.property a).mp ha, hz.trans hc⟩

/-- The actual conjugation action on the corrected marked class. -/
def normalizerAction (M : AlternatingProductModel L z r 6) :
    normalizer (elementary M : Set G) →* Perm (beta M) where
  toFun n := Equiv.Perm.subtypePerm (MulAut.conj (n : G)).toEquiv (conjugate_mem_beta_iff M n)
  map_one' := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    simp
  map_mul' n m := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    change ((n : G) * (m : G)) * (a : G) * ((n : G) * (m : G))⁻¹ =
      (n : G) * ((m : G) * (a : G) * (m : G)⁻¹) * (n : G)⁻¹
    simp only [mul_inv_rev, mul_assoc]

@[simp] theorem normalizerAction_apply (M : AlternatingProductModel L z r 6)
    (n : normalizer (elementary M : Set G)) (a : beta M) :
    (normalizerAction M n a : G) = MulAut.conj (n : G) a := rfl

/-- The kernel on β is the actual centralizer of A, since α generates A. -/
theorem normalizerAction_kernel (M : AlternatingProductModel L z r 6) (hr : IsConj z r) :
    (normalizerAction M).ker =
      (centralizer (elementary M : Set G)).subgroupOf (normalizer (elementary M : Set G)) := by
  ext n
  constructor
  · intro hn
    change (n : G) ∈ centralizer (elementary M : Set G)
    have hcentral : centralizer (elementary M : Set G) = centralizer (alpha M : Set G) := by
      rw [elementary_eq_closure, centralizer_closure]
    rw [hcentral]
    apply mem_centralizer_iff.mpr
    intro a ha
    have he := congrArg (fun p : Perm (beta M) => (p ⟨a, alpha_subset_beta M hr ha⟩ : G)) hn
    change (n : G) * a * (n : G)⁻¹ = a at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hn
    change (n : G) ∈ centralizer (elementary M : Set G) at hn
    change normalizerAction M n = 1
    apply Equiv.ext
    intro a
    apply Subtype.ext
    change (n : G) * (a : G) * (n : G)⁻¹ = (a : G)
    rw [← mem_centralizer_iff.mp hn a a.property.1, mul_inv_cancel_right]

/-- The faithful permutation image, with no assumed order. -/
def normalizerImage (M : AlternatingProductModel L z r 6) : Subgroup (Perm (beta M)) :=
  (normalizerAction M).range

/-- The point z of the corrected marked class. -/
def markedPoint (M : AlternatingProductModel L z r 6) : beta M :=
  ⟨z, ⟨by simpa only [generator_three] using generator_mem M 3, IsConj.refl z⟩⟩

/-- The point stabilizer in the faithful action image. -/
def normalizerStabilizer (M : AlternatingProductModel L z r 6) : Subgroup (normalizerImage M) :=
  MulAction.stabilizer (normalizerImage M) (markedPoint M)

/-- The precise transitivity obligation for each source branch. -/
def NormalizerTransitive (M : AlternatingProductModel L z r 6) : Prop :=
  ∀ a ∈ beta M, ∃ n ∈ normalizer (elementary M : Set G), MulAut.conj n z = a

/-- Orbit-stabilizer computes the order of the constructed image. -/
theorem normalizerImage_card (M : AlternatingProductModel L z r 6)
    (htrans : NormalizerTransitive M) :
    Nat.card (normalizerImage M) = Nat.card (beta M) * Nat.card (normalizerStabilizer M) := by
  have ho : MulAction.orbit (normalizerImage M) (markedPoint M) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    obtain ⟨n, hn, he⟩ := htrans a a.property
    refine ⟨⟨normalizerAction M ⟨n, hn⟩, ⟨⟨n, hn⟩, rfl⟩⟩, ?_⟩
    exact Subtype.ext he
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    (normalizerImage M) (markedPoint M))
  rw [Nat.card_prod, ho] at hc
  simpa only [Nat.card_congr (Equiv.Set.univ (beta M)), normalizerStabilizer] using hc.symm

/-- Relabel the genuine five-point image and apply the S₅ obstruction. -/
theorem normalizerImage_card_ne_thirty [Finite G]
    (M : AlternatingProductModel L z r 6) (hb : Nat.card (beta M) = 5) :
    Nat.card (normalizerImage M) ≠ 30 := by
  classical
  let := Fintype.ofFinite (beta M)
  let e : beta M ≃ Fin 5 := Fintype.equivFinOfCardEq (by rwa [← Nat.card_eq_fintype_card])
  let f : normalizerImage M →* Perm (Fin 5) :=
    e.permCongrHom.toMonoidHom.comp (normalizerImage M).subtype
  exact card_ne_thirty_of_injective_hom f (e.permCongrHom.injective.comp Subtype.val_injective)

/-- The common terminal contradiction. The branch proofs must supply transitivity
and the computed order-six stabilizer; neither is asserted by this helper. -/
theorem contradiction_of_five_points [Finite G]
    (M : AlternatingProductModel L z r 6) (hb : Nat.card (beta M) = 5)
    (htrans : NormalizerTransitive M) (hs : Nat.card (normalizerStabilizer M) = 6) : False := by
  apply normalizerImage_card_ne_thirty M hb
  rw [normalizerImage_card M htrans, hb, hs]

end CFSG.Quasithin.Chapter16.Intersections.Six
