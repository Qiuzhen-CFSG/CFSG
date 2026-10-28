module

public import Theory.GroupAction.Quotient
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group

/-!
# Central commutator quotients and fixed representatives

If all commutators [r,Q] lie in a subgroup V centralizing Q, the map
x ↦ [r,x] is a homomorphism Q → V with kernel C_Q(r). It is equivariant
under any subgroup centralizing r and normalizing Q. Irreducibility on V
and a nonzero commutator make it onto, giving the explicit quotient
isomorphism. Coprime action on a finite solvable Q then lifts fixed values
to fixed representatives.

These are the algebraic steps in the last paragraph of Aschbacher--Smith,
*The Classification of Quasithin Groups*, combined manuscript of 1 March
2004, Theorem 4.2.13, printed p.612. Here Q is the source's R₁. We use
Lean's commutator convention r*x*r⁻¹*x⁻¹ throughout; the final normalizer
argument is proved with this same convention, so it needs no implicit
change of conjugation convention. No sporadic-group recognition input is
asserted in this module.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace Subgroup

/-- The central commutator map, retaining its ambient values. -/
def centralCommutatorHom {G : Type*} [Group G]
    (Q V : Subgroup G) (hV : V ≤ centralizer (Q : Set G))
    (r : G) (hr : ∀ x ∈ Q, ⁅r, x⁆ ∈ V) : Q →* V where
  toFun x := ⟨⁅r, (x : G)⁆, hr x x.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change ⁅r, (x : G) * (y : G)⁆ = ⁅r, (x : G)⁆ * ⁅r, (y : G)⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    calc
      _ = ⁅r, (x : G)⁆ * ((x : G) * ⁅r, (y : G)⁆) * (x : G)⁻¹ := by group
      _ = ⁅r, (x : G)⁆ * ⁅r, (y : G)⁆ := by
        rw [hV (hr y y.property) x x.property]
        group

/-- Its kernel is the centralizer of r inside Q, not the ambient centralizer. -/
theorem centralCommutatorHom_ker {G : Type*} [Group G]
    (Q V : Subgroup G) (hV : V ≤ centralizer (Q : Set G))
    (r : G) (hr : ∀ x ∈ Q, ⁅r, x⁆ ∈ V) :
    (centralCommutatorHom Q V hV r hr).ker =
      (centralizer ({r} : Set G)).subgroupOf Q := by
  ext x
  change (⟨⁅r, (x : G)⁆, _⟩ : V) = 1 ↔ _
  rw [Subtype.ext_iff]
  exact commutatorElement_eq_one_iff_mul_comm.trans
    (mem_centralizer_singleton_iff.trans eq_comm).symm

/-- Equivariance under an element normalizing Q and centralizing r. -/
theorem centralCommutatorHom_conj {G : Type*} [Group G]
    (Q V : Subgroup G) (hV : V ≤ centralizer (Q : Set G))
    (r : G) (hr : ∀ x ∈ Q, ⁅r, x⁆ ∈ V)
    (a : G) (haQ : a ∈ normalizer (Q : Set G)) (har : Commute a r)
    (x : Q) :
    (centralCommutatorHom Q V hV r hr
      ⟨a * x * a⁻¹, (mem_normalizer_iff.mp haQ x).mp x.property⟩ : G) =
      a * (centralCommutatorHom Q V hV r hr x : G) * a⁻¹ := by
  change ⁅r, a * (x : G) * a⁻¹⁆ = a * ⁅r, (x : G)⁆ * a⁻¹
  rw [conjugate_commutatorElement]
  rw [har.eq, mul_inv_cancel_right]

/-- An irreducible image containing a nonidentity commutator is all of V. -/
theorem centralCommutatorHom_surjective_of_irreducible {G : Type*} [Group G]
    (Q V L : Subgroup G) (hV : V ≤ centralizer (Q : Set G))
    (r : G) (hr : ∀ x ∈ Q, ⁅r, x⁆ ∈ V)
    (hLQ : L ≤ normalizer (Q : Set G)) (hLr : L ≤ centralizer ({r} : Set G))
    (hirr : ∀ W : Subgroup G, W ≤ V → L ≤ normalizer (W : Set G) → W = ⊥ ∨ W = V)
    (hne : ∃ x ∈ Q, ¬ Commute r x) :
    Function.Surjective (centralCommutatorHom Q V hV r hr) := by
  let f := centralCommutatorHom Q V hV r hr
  let W := f.range.map V.subtype
  have hWV : W ≤ V := map_subtype_le _
  have hstable (a : G) (ha : a ∈ L) (w : G) (hw : w ∈ W) :
      a * w * a⁻¹ ∈ W := by
    obtain ⟨v, ⟨x, rfl⟩, rfl⟩ := hw
    refine ⟨f ⟨a * x * a⁻¹, (mem_normalizer_iff.mp (hLQ ha) x).mp x.property⟩,
      ⟨_, rfl⟩, ?_⟩
    exact centralCommutatorHom_conj Q V hV r hr a (hLQ ha)
      (mem_centralizer_singleton_iff.mp (hLr ha)) x
  have hLW : L ≤ normalizer (W : Set G) := by
    intro a ha
    apply mem_normalizer_iff.mpr
    intro w
    refine ⟨hstable a ha w, ?_⟩
    intro hw
    have hh := hstable a⁻¹ (L.inv_mem ha) _ hw
    simpa [mul_assoc] using hh
  have hWne : W ≠ ⊥ := by
    intro heq
    obtain ⟨x, hx, hnx⟩ := hne
    have hxW : ⁅r, x⁆ ∈ W := ⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    rw [heq, mem_bot] at hxW
    exact hnx (commutatorElement_eq_one_iff_mul_comm.mp hxW)
  have hWeq : W = V := (hirr W hWV hLW).resolve_left hWne
  intro v
  have hv : (v : G) ∈ W := hWeq.symm ▸ v.property
  obtain ⟨v', ⟨x, rfl⟩, hx⟩ := hv
  exact ⟨x, Subtype.ext hx⟩

/-- A commutator of a centralizing element with a normalizing element
still centralizes the subgroup. -/
theorem commutator_mem_centralizer_of_normalizes {G : Type*} [Group G]
    (K : Subgroup G) {r s : G} (hr : r ∈ centralizer (K : Set G))
    (hs : s ∈ normalizer (K : Set G)) : ⁅r, s⁆ ∈ centralizer (K : Set G) := by
  have hconj : s * r⁻¹ * s⁻¹ ∈ centralizer (K : Set G) := by
    intro k hk
    have hkinv : s⁻¹ * k * s ∈ K := (mem_normalizer_iff''.mp hs k).mp hk
    have hh := (centralizer (K : Set G)).inv_mem hr _ hkinv
    calc
      k * (s * r⁻¹ * s⁻¹) = s * ((s⁻¹ * k * s) * r⁻¹) * s⁻¹ := by group
      _ = s * (r⁻¹ * (s⁻¹ * k * s)) * s⁻¹ := by rw [hh]
      _ = s * r⁻¹ * s⁻¹ * k := by group
  simpa [commutatorElement_def, mul_assoc] using
    (centralizer (K : Set G)).mul_mem hr hconj

/-- The actual multiplicative equivalence induced by the commutator map. -/
noncomputable def centralCommutatorQuotientEquiv {G : Type*} [Group G]
    (Q V L : Subgroup G) (hV : V ≤ centralizer (Q : Set G))
    (r : G) (hr : ∀ x ∈ Q, ⁅r, x⁆ ∈ V)
    (hLQ : L ≤ normalizer (Q : Set G)) (hLr : L ≤ centralizer ({r} : Set G))
    (hirr : ∀ W : Subgroup G, W ≤ V → L ≤ normalizer (W : Set G) → W = ⊥ ∨ W = V)
    (hne : ∃ x ∈ Q, ¬ Commute r x) :
    Q ⧸ (centralCommutatorHom Q V hV r hr).ker ≃* V :=
  QuotientGroup.quotientKerEquivOfSurjective _
    (centralCommutatorHom_surjective_of_irreducible Q V L hV r hr hLQ hLr hirr hne)

/-- The quotient equivalence takes the coset of x to the literal commutator. -/
theorem centralCommutatorQuotientEquiv_apply {G : Type*} [Group G]
    (Q V L : Subgroup G) (hV : V ≤ centralizer (Q : Set G))
    (r : G) (hr : ∀ x ∈ Q, ⁅r, x⁆ ∈ V)
    (hLQ : L ≤ normalizer (Q : Set G)) (hLr : L ≤ centralizer ({r} : Set G))
    (hirr : ∀ W : Subgroup G, W ≤ V → L ≤ normalizer (W : Set G) → W = ⊥ ∨ W = V)
    (hne : ∃ x ∈ Q, ¬ Commute r x) (x : Q) :
    (centralCommutatorQuotientEquiv Q V L hV r hr hLQ hLr hirr hne
      (QuotientGroup.mk' (centralCommutatorHom Q V hV r hr).ker x) : G) = ⁅r, (x : G)⁆ := rfl

/-- Coprime action on solvable Q lifts X-fixed commutator values to
representatives in C_Q(X). -/
theorem centralCommutatorHom_exists_fixed_preimage {G : Type*} [Group G] [Finite G]
    (Q V X : Subgroup G) (hV : V ≤ centralizer (Q : Set G))
    (r : G) (hr : ∀ x ∈ Q, ⁅r, x⁆ ∈ V)
    (hXQ : X ≤ normalizer (Q : Set G)) (hXr : X ≤ centralizer ({r} : Set G))
    (hsolv : Group.IsSolvable Q) (hcop : Nat.Coprime (Nat.card X) (Nat.card Q))
    (hsurj : Function.Surjective (centralCommutatorHom Q V hV r hr))
    (v : G) (hv : v ∈ V) (hvX : v ∈ centralizer (X : Set G)) :
    ∃ s ∈ Q, s ∈ centralizer (X : Set G) ∧ ⁅r, s⁆ = v := by
  let f := centralCommutatorHom Q V hV r hr
  let nativeAction := conjMulDistribMulActionOfLeNormalizer X Q hXQ
  let _ : MulDistribMulAction X Q := nativeAction
  let _ : SMul X Q := nativeAction.toSMul
  let _ : MulAction X Q := nativeAction.toMulAction
  have hequiv (a : X) (q : Q) :
      (f (a • q) : G) = (a : G) * (f q : G) * (a : G)⁻¹ :=
    centralCommutatorHom_conj Q V hV r hr a (hXQ a.property)
      (mem_centralizer_singleton_iff.mp (hXr a.property)) q
  have hInv : IsInvariant X Q f.ker := by
    constructor
    intro a q
    change f q = 1 ↔ f (a • q) = 1
    simp only [Subtype.ext_iff]
    rw [hequiv]
    change (f q : G) = 1 ↔ MulAut.conj (a : G) (f q : G) = 1
    constructor
    · intro h
      rw [h, map_one]
    · intro h
      apply (MulAut.conj (a : G)).injective
      simpa only [map_one] using h
  let _ : MulDistribMulAction X (Q ⧸ f.ker) := quotientMulDistribMulAction f.ker hInv
  obtain ⟨q, hq⟩ := hsurj ⟨v, hv⟩
  have hqfix : QuotientGroup.mk' f.ker q ∈ FixedPoints.subgroup X (Q ⧸ f.ker) := by
    intro a
    change QuotientGroup.mk' f.ker (a • q) = QuotientGroup.mk' f.ker q
    apply QuotientGroup.eq_iff_div_mem.mpr
    change f ((a • q) / q) = 1
    rw [map_div, div_eq_one]
    apply Subtype.ext
    rw [hequiv]
    have hqval : (f q : G) = v := congrArg Subtype.val hq
    rw [hqval, hvX a a.property, mul_inv_cancel_right]
  rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime hsolv hcop f.ker hInv] at hqfix
  obtain ⟨s, hs, heq⟩ := hqfix
  have hfs : f s = f q := by
    have hh := QuotientGroup.eq_iff_div_mem.mp heq
    change f (s / q) = 1 at hh
    rwa [map_div, div_eq_one] at hh
  refine ⟨s, s.property, ?_, congrArg Subtype.val (hfs.trans hq)⟩
  intro a ha
  have hh := congrArg Subtype.val (hs ⟨a, ha⟩)
  change a * (s : G) * a⁻¹ = (s : G) at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

end Subgroup
