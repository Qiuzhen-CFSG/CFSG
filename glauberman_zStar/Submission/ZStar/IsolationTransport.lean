import Submission.ZStar.OddCommutators

/-!
# Transport and limitations of involution isolation

This file records the elementary group-theoretic facts needed when comparing
the isolated distinguished involution in the Z-star argument with the
auxiliary involutions in the commuting-replacement construction.
-/

namespace Submission.ZStar

namespace IsolationTransport

universe u

/-- The raw isolation predicate used throughout the Z-star development. -/
def IsolatedConjugates {G : Type u} [Group G] (z : G) : Prop :=
  ∀ g : G,
    (g * z * g⁻¹) * z = z * (g * z * g⁻¹) →
      g * z * g⁻¹ = z

/-- Isolation can equivalently be stated using membership of a conjugate in
the centralizer.  This is the orientation that naturally occurs when one
works with right cosets of `C_G(z)`. -/
theorem isolatedConjugates_iff_conjugate_mem_centralizer
    {G : Type u} [Group G] (z : G) :
    IsolatedConjugates z ↔
      ∀ g : G,
        g⁻¹ * z * g ∈ Subgroup.centralizer ({z} : Set G) →
          g ∈ Subgroup.centralizer ({z} : Set G) := by
  constructor
  · intro hisolated g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    have heq := hisolated g⁻¹ (by simpa [mul_assoc] using hg)
    have h := congrArg (fun x : G ↦ g * x) heq
    simpa [mul_assoc] using h.symm
  · intro hcentralizer g hcomm
    have hgInv : g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
      apply hcentralizer g⁻¹
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa [mul_assoc] using hcomm
    have hg : g ∈ Subgroup.centralizer ({z} : Set G) := by
      have := (Subgroup.centralizer ({z} : Set G)).inv_mem hgInv
      simpa using this
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    calc
      g * z * g⁻¹ = (g * z) * g⁻¹ := by rw [mul_assoc]
      _ = (z * g) * g⁻¹ := by rw [hg]
      _ = z := by simp

/-- Isolation is preserved by conjugating the distinguished element. -/
theorem isolatedConjugates_conjugate
    {G : Type u} [Group G] {t : G}
    (ht : IsolatedConjugates t) (a : G) :
    IsolatedConjugates (a * t * a⁻¹) := by
  intro g hcomm
  let x : G := a⁻¹ * g * a
  have hxcomm :
      (x * t * x⁻¹) * t = t * (x * t * x⁻¹) := by
    have h := congrArg (fun y : G ↦ a⁻¹ * y * a) hcomm
    dsimp [x]
    convert h using 1 <;> group
  have hx := ht x hxcomm
  calc
    g * (a * t * a⁻¹) * g⁻¹ =
        a * (x * t * x⁻¹) * a⁻¹ := by
      dsimp [x]
      group
    _ = a * t * a⁻¹ := by rw [hx]

/-- Every element conjugate to an isolated element is isolated. -/
theorem isolatedConjugates_of_isConj
    {G : Type u} [Group G] {t z : G}
    (ht : IsolatedConjugates t) (hzt : IsConj z t) :
    IsolatedConjugates z := by
  rcases isConj_iff.mp hzt with ⟨a, ha⟩
  have hz : z = a⁻¹ * t * a := by
    calc
      z = a⁻¹ * (a * z * a⁻¹) * a := by group
      _ = a⁻¹ * t * a := by rw [ha]
  rw [hz]
  simpa using isolatedConjugates_conjugate ht a⁻¹

/-- Under the local Z-star hypotheses, isolation is therefore available for
every conjugate of the distinguished involution (and only such conjugates are
obtained formally from weak closure). -/
theorem isolatedConjugates_of_isConj_of_central_weaklyClosed
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (t z : G)
    (htI : IsInvolution t)
    (htCentral : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s)
    (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G))
    (hzt : IsConj z t) :
    IsolatedConjugates z := by
  apply isolatedConjugates_of_isConj
    (t := t) (z := z) _ hzt
  exact isolated_of_central_weaklyClosed S t htI htCentral htWeak

/-- Centralizer-membership form of the preceding transport theorem. -/
theorem conjugate_mem_centralizer_imp_mem_of_isConj_of_weaklyClosed
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (t z : G)
    (htI : IsInvolution t)
    (htCentral : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s)
    (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G))
    (hzt : IsConj z t) :
    ∀ g : G,
      g⁻¹ * z * g ∈ Subgroup.centralizer ({z} : Set G) →
        g ∈ Subgroup.centralizer ({z} : Set G) := by
  exact (isolatedConjugates_iff_conjugate_mem_centralizer z).mp
    (isolatedConjugates_of_isConj_of_central_weaklyClosed
      S t z htI htCentral htWeak hzt)

/-- A distinct element commuting with an isolated element cannot lie in its
conjugacy class. -/
theorem not_isConj_of_commute_of_ne
    {G : Type u} [Group G] {t z : G}
    (ht : IsolatedConjugates t)
    (hcomm : z * t = t * z) (hne : z ≠ t) :
    ¬ IsConj z t := by
  intro hzt
  rcases isConj_iff.mp hzt with ⟨g, hg⟩
  have hz : g⁻¹ * t * g = z := by
    calc
      g⁻¹ * t * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [hg]
      _ = z := by group
  have hcomm' :
      (g⁻¹ * t * (g⁻¹)⁻¹) * t =
        t * (g⁻¹ * t * (g⁻¹)⁻¹) := by
    simpa only [inv_inv, hz] using hcomm
  have heq := ht g⁻¹ hcomm'
  apply hne
  calc
    z = g⁻¹ * t * g := hz.symm
    _ = g⁻¹ * t * (g⁻¹)⁻¹ := by rw [inv_inv]
    _ = t := heq

/-- Membership in the conjugacy class used by `SectionReplacement` preserves
the explicit assertion that this class is different from the distinguished
class of `t`. -/
theorem not_isConj_of_mem_carrier_of_not_isConj
    {G : Type u} [Group G] {t s s₀ : G}
    (hst : ¬ IsConj s t)
    (hs₀ : s₀ ∈ (ConjClasses.mk s).carrier) :
    ¬ IsConj s₀ t := by
  have hs₀s : IsConj s₀ s :=
    ConjClasses.mk_eq_mk_iff_isConj.mp
      (ConjClasses.mem_carrier_iff_mk_eq.mp hs₀)
  intro hs₀t
  exact hst (hs₀s.symm.trans hs₀t)

/-- In particular, multiplying an isolated element by a nonidentity element
which commutes with it produces an element outside the isolated conjugacy
class.  This is exactly the shape `c = t * s₀` occurring in
`SectionReplacement`. -/
theorem mul_not_isConj_of_commute_of_ne_one
    {G : Type u} [Group G] {t s₀ : G}
    (ht : IsolatedConjugates t)
    (hcomm : t * s₀ = s₀ * t) (hs₀ : s₀ ≠ 1) :
    ¬ IsConj (t * s₀) t := by
  apply not_isConj_of_commute_of_ne ht
  · calc
      (t * s₀) * t = t * (s₀ * t) := by rw [mul_assoc]
      _ = t * (t * s₀) := by rw [← hcomm]
  · intro h
    apply hs₀
    have h' := congrArg (fun x : G ↦ t⁻¹ * x) h
    simpa [mul_assoc] using h'

/-- Involution-specialized form of the preceding obstruction. -/
theorem mul_not_isConj_of_commute_of_isInvolution
    {G : Type u} [Group G] {t s₀ : G}
    (ht : IsolatedConjugates t)
    (hcomm : t * s₀ = s₀ * t) (hs₀I : IsInvolution s₀) :
    ¬ IsConj (t * s₀) t :=
  mul_not_isConj_of_commute_of_ne_one ht hcomm hs₀I.1

end IsolationTransport

end Submission.ZStar
