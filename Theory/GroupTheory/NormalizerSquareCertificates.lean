module

public import Theory.GroupTheory.NormalizerInvolutionSquareWitness
public import Theory.GroupTheory.CentricRadicalCertificates
public import Theory.Frattini.PGroup

/-!
# Square certificates for normalizer two-core witnesses

Two variants of the finite word certificate from `NormalizerInvolutionSquareWitness`
use the same enumeration and conjugation data. Products of squares for every
displacement imply trivial Frattini action. Alternatively, central displacements,
square displacements on the center, and fixed squares give trivial action on
G, Z(G), the square-generated subgroup, and 1. The characteristic-series kernel
is a normal two-subgroup of the full automorphism group.

Generator and inverse transitions prove that the listed elements exhaust the
actual generated subgroup. Every remaining certificate clause is a finite group
identity, including nonmembership and normalization of the proposed witness.

Source: Burnside's Frattini kernel theorem and the elementary characteristic-series
argument, as proved in `PGroup.FrattiniAutomorphismKernel` and
`PGroup.CharacteristicSeriesAutomorphisms`. These tests are used for the second
Held local model in Huppert--Blackburn III, XII.1.18(b), printed p.314.
-/

namespace Subgroup
variable {G : Type*} [Group G]

/-- Central displacements, square displacements on the center, and fixed squares
place an automorphism in the two-core of the full automorphism group. -/
public theorem mem_pCore_of_center_square_actions [Finite G]
    (hG : IsPGroup 2 G) (f : MulAut G)
    (hdis : ∀ x, x⁻¹ * f x ∈ center G)
    (hcen : ∀ x ∈ center G, ∃ w : List G,
      (w.map (fun y => y ^ 2)).prod = x⁻¹ * f x)
    (hsq : ∀ x, f (x ^ 2) = x ^ 2) : f ∈ pCore 2 (MulAut G) := by
  let C := center G
  let D := closure (Set.range (fun x : G => x ^ 2))
  let : D.Characteristic := closure_range_pow_characteristic 2
  have hCD : ∀ x ∈ C, x⁻¹ * f x ∈ D := by
    intro x hx
    obtain ⟨w, hw⟩ := hcen x hx
    rw [← hw]
    apply list_prod_mem
    intro y hy
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
    exact subset_closure ⟨z, rfl⟩
  have hD : ∀ x ∈ D, f x = x := by
    apply MonoidHom.eqOn_closure (f := f.toMonoidHom) (g := MonoidHom.id G)
    rintro _ ⟨x, rfl⟩
    exact hsq x
  have hle : characteristicStepKernel ⊤ C ⊓ characteristicStepKernel C D ⊓
      characteristicStepKernel D ⊥ ≤ pCore 2 (MulAut G) :=
    le_sSup ⟨inferInstance, isPGroup_threeStepKernel hG C D⟩
  apply hle
  refine ⟨⟨fun x _ => hdis x, hCD⟩, ?_⟩
  intro x hx
  change x⁻¹ * f x = 1
  rw [hD x hx, inv_mul_cancel]

/-- Finite identities for the center/square characteristic-series test. -/
@[expose] public def InvolutionSquareCertificate.CenterSquareValid {m r : ℕ}
    (c : InvolutionSquareCertificate G m r) (gen : Fin m → G) : Prop :=
  (∀ a, c.rep a = (List.map gen (c.words a)).prod) ∧
  c.rep c.base = 1 ∧
  (∀ i a, gen i * c.rep a = c.rep (c.next i a)) ∧
  (∀ i a, (gen i)⁻¹ * c.rep a = c.rep (c.prev i a)) ∧
  (∀ a, c.rep a ≠ c.outside) ∧
  (∀ a, c.outside * c.rep a * c.outside⁻¹ = c.rep (c.conj a)) ∧
  (∀ a, c.outside⁻¹ * c.rep a * c.outside = c.rep (c.unconj a)) ∧
  (∀ a b, c.rep b * ((c.rep a)⁻¹ * (c.outside * c.rep a * c.outside⁻¹)) =
    ((c.rep a)⁻¹ * (c.outside * c.rep a * c.outside⁻¹)) * c.rep b) ∧
  (∀ a, (∀ b, c.rep b * c.rep a = c.rep a * c.rep b) →
    ((c.squareRoots a).map (fun j => (c.rep j) ^ 2)).prod =
      (c.rep a)⁻¹ * (c.outside * c.rep a * c.outside⁻¹)) ∧
  ∀ a, c.outside * ((c.rep a) ^ 2) * c.outside⁻¹ = (c.rep a) ^ 2

public instance {m r : ℕ} [DecidableEq G] (c : InvolutionSquareCertificate G m r)
    (gen : Fin m → G) : Decidable (c.CenterSquareValid gen) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop) ∧
    (_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop)))

/-- A valid center/square certificate constructs an outside normalizer two-core witness. -/
public theorem InvolutionSquareCertificate.centerSquare_sound [Finite G] {m r : ℕ}
    (hG : IsPGroup 2 G) (c : InvolutionSquareCertificate G m r) (gen : Fin m → G)
    (hc : c.CenterSquareValid gen) : (closure (Set.range gen)).HasPCoreNormalizerWitness 2 := by
  obtain ⟨hw, hb, hn, hp, hout, hconj, hunconj, hd, hi, hs⟩ := hc
  let U := closure (Set.range gen)
  have he : ∀ x, x ∈ U ↔ ∃ a, c.rep a = x := by
    intro x
    change x ∈ (U : Set G) ↔ _
    rw [show (U : Set G) = Set.range c.rep from
      closure_eq_range_of_word_transitions gen c.rep c.words c.base c.next c.prev hw hb hn hp]
    rfl
  have hnorm : c.outside ∈ normalizer (U : Set G) := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := (he x).mp hx
      exact (he _).mpr ⟨c.conj a, (hconj a).symm⟩
    · intro hx
      obtain ⟨a, ha⟩ := (he _).mp hx
      apply (he _).mpr
      refine ⟨c.unconj a, ?_⟩
      rw [← hunconj a, ha]
      simp [mul_assoc]
  let f := U.normalizerMonoidHom ⟨c.outside, hnorm⟩
  refine ⟨⟨c.outside, hnorm⟩, ?_, mem_pCore_of_center_square_actions (hG.to_subgroup U) f ?_ ?_ ?_⟩
  · intro hh
    obtain ⟨a, ha⟩ := (he _).mp hh
    exact hout a ha
  · intro x
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a, ha⟩ := (he _).mp x.property
    obtain ⟨b, hb⟩ := (he _).mp y.property
    apply Subtype.ext
    change (y : G) * ((x : G)⁻¹ * (c.outside * (x : G) * c.outside⁻¹)) =
      ((x : G)⁻¹ * (c.outside * (x : G) * c.outside⁻¹)) * (y : G)
    rw [← ha, ← hb]
    exact hd a b
  · intro x hx
    obtain ⟨a, ha⟩ := (he _).mp x.property
    have hh : ∀ b, c.rep b * c.rep a = c.rep a * c.rep b := by
      intro b
      have hh := congrArg Subtype.val ((mem_center_iff.mp hx)
        (⟨c.rep b, (he _).mpr ⟨b, rfl⟩⟩ : U))
      change c.rep b * (x : G) = (x : G) * c.rep b at hh
      rwa [← ha] at hh
    let w : List U := (c.squareRoots a).map (fun j => ⟨c.rep j, (he _).mpr ⟨j, rfl⟩⟩)
    refine ⟨w, Subtype.ext ?_⟩
    change (((w.map (fun y => y ^ 2)).prod : U) : G) =
      (x : G)⁻¹ * (c.outside * (x : G) * c.outside⁻¹)
    simpa only [w, Subgroup.val_list_prod, List.map_map, Function.comp_def,
      Subgroup.coe_pow, ← ha] using hi a hh
  · intro x
    obtain ⟨a, ha⟩ := (he _).mp x.property
    apply Subtype.ext
    change c.outside * ((x : G) ^ 2) * c.outside⁻¹ = (x : G) ^ 2
    rw [← ha]
    exact hs a

/-- Finite identities certifying trivial action on the Frattini quotient. -/
@[expose] public def InvolutionSquareCertificate.FrattiniValid {m r : ℕ}
    (c : InvolutionSquareCertificate G m r) (gen : Fin m → G) : Prop :=
  (∀ a, c.rep a = (List.map gen (c.words a)).prod) ∧
  c.rep c.base = 1 ∧
  (∀ i a, gen i * c.rep a = c.rep (c.next i a)) ∧
  (∀ i a, (gen i)⁻¹ * c.rep a = c.rep (c.prev i a)) ∧
  (∀ a, c.rep a ≠ c.outside) ∧
  (∀ a, c.outside * c.rep a * c.outside⁻¹ = c.rep (c.conj a)) ∧
  (∀ a, c.outside⁻¹ * c.rep a * c.outside = c.rep (c.unconj a)) ∧
  ∀ a, ((c.squareRoots a).map (fun j => (c.rep j) ^ 2)).prod =
      (c.rep a)⁻¹ * (c.outside * c.rep a * c.outside⁻¹)

public instance {m r : ℕ} [DecidableEq G] (c : InvolutionSquareCertificate G m r)
    (gen : Fin m → G) : Decidable (c.FrattiniValid gen) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop) ∧
    (_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop)))

/-- A valid Frattini certificate constructs an outside normalizer two-core witness. -/
public theorem InvolutionSquareCertificate.frattini_sound [Finite G] {m r : ℕ}
    (hG : IsPGroup 2 G) (c : InvolutionSquareCertificate G m r) (gen : Fin m → G)
    (hc : c.FrattiniValid gen) : (closure (Set.range gen)).HasPCoreNormalizerWitness 2 := by
  obtain ⟨hw, hb, hn, hp, hout, hconj, hunconj, hd⟩ := hc
  let U := closure (Set.range gen)
  have he : ∀ x, x ∈ U ↔ ∃ a, c.rep a = x := by
    intro x
    change x ∈ (U : Set G) ↔ _
    rw [show (U : Set G) = Set.range c.rep from
      closure_eq_range_of_word_transitions gen c.rep c.words c.base c.next c.prev hw hb hn hp]
    rfl
  have hnorm : c.outside ∈ normalizer (U : Set G) := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := (he x).mp hx
      exact (he _).mpr ⟨c.conj a, (hconj a).symm⟩
    · intro hx
      obtain ⟨a, ha⟩ := (he _).mp hx
      apply (he _).mpr
      refine ⟨c.unconj a, ?_⟩
      rw [← hunconj a, ha]
      simp [mul_assoc]
  let : Fact (IsPGroup 2 U) := ⟨hG.to_subgroup U⟩
  have hle : (quotientAut (frattini U)).ker ≤ pCore 2 (MulAut U) :=
    le_sSup ⟨inferInstance, isPGroup_quotientAut_frattini_kernel (hG.to_subgroup U)⟩
  refine ⟨⟨c.outside, hnorm⟩, ?_, hle ?_⟩
  · intro hh
    obtain ⟨a, ha⟩ := (he _).mp hh
    exact hout a ha
  · apply quotientAut_eq_one_of_displacements
    intro x
    obtain ⟨a, ha⟩ := (he _).mp x.property
    let w : List U := (c.squareRoots a).map (fun j => ⟨c.rep j, (he _).mpr ⟨j, rfl⟩⟩)
    have hh : (w.map (fun y => y ^ 2)).prod = x⁻¹ * U.normalizerMonoidHom ⟨c.outside, hnorm⟩ x := by
      apply Subtype.ext
      change (((w.map (fun y => y ^ 2)).prod : U) : G) =
        (x : G)⁻¹ * (c.outside * (x : G) * c.outside⁻¹)
      simpa only [w, Subgroup.val_list_prod, List.map_map, Function.comp_def,
        Subgroup.coe_pow, ← ha] using hd a
    rw [← hh]
    apply list_prod_mem
    intro y hy
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
    exact pth_power_mem_frattini_of_isPGroup (p := 2) z
end Subgroup
