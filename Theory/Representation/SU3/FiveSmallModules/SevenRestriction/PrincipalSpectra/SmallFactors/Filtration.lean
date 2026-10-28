module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.FlagTools
public import Theory.Representation.RepEquiv
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Characteristic polynomials retained by simple-factor filtrations

A finite filtration records each simple quotient's dimension and the
characteristic polynomial of a fixed actor. Pullback along an exact sequence
retains these data, since every surviving factor is equivariantly isomorphic
to an original factor. Consequently all irreducible subquotients inherit the
certificate, including subquotients that are not quotients of the whole module.
Equivariant transport and finite-flag assembly connect this argument to the
literal SU₃(5) principal series.

Source application: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open Polynomial
namespace Representation
universe u
variable {k G : Type*} [Field k] [Group G]

/-- A filtration by actual simple quotients, retaining a predicate on their
dimensions and characteristic polynomials at the specified actor. -/
inductive FactorPolynomialFiltration (P : ℕ → k[X] → Prop) (x : G) :
    {V : Type u} → [AddCommGroup V] → [Module k V] → [FiniteDimensional k V] →
      Representation k G V → Prop
  | zero {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (ρ : Representation k G V) [Subsingleton V] : FactorPolynomialFiltration P x ρ
  | step {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      {ρ : Representation k G V} (S : Subrepresentation ρ)
      (previous : FactorPolynomialFiltration P x S.toRepresentation)
      (simple : IsIrreducible S.quotientRepresentation)
      (spectrum : P (Module.finrank k (V ⧸ S.toSubmodule))
        (S.quotientRepresentation x).charpoly) : FactorPolynomialFiltration P x ρ

namespace FactorPolynomialFiltration
variable {P : ℕ → k[X] → Prop} {x : G}
variable {V W : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  {ρ : Representation k G V} {σ : Representation k G W}

/-- An equivariant linear equivalence preserves the actor polynomial. -/
theorem charpoly_equiv (e : ρ.Equiv σ) (x : G) :
    (ρ x).charpoly = (σ x).charpoly := by
  rw [← e.conj_apply_self x, e.toLinearEquiv.charpoly_conj]

/-- A nonzero map to a simple representation identifies an actual simple factor. -/
theorem quotient_spectrum (h : FactorPolynomialFiltration P x ρ) [IsIrreducible σ]
    (f : ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    P (Module.finrank k W) (σ x).charpoly := by
  induction h with
  | zero τ =>
    exfalso
    apply hf
    ext x
    exact (congrArg f (Subsingleton.elim x 0)).trans (map_zero f)
  | @step X _ _ _ τ S previous simple spectrum ih =>
    let r : S.toRepresentation.IntertwiningMap σ := {
      toLinearMap := f.toLinearMap.comp S.toSubmodule.subtype
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        exact IntertwiningMap.isIntertwining τ σ f g x }
    by_cases hr : r = 0
    · have hk : S.toSubmodule ≤ LinearMap.ker f.toLinearMap := by
        intro x hx
        exact congrArg (fun q : S.toRepresentation.IntertwiningMap σ => q ⟨x, hx⟩) hr
      let q : S.quotientRepresentation.IntertwiningMap σ := {
        toLinearMap := S.toSubmodule.liftQ f.toLinearMap hk
        isIntertwining' := by
          intro g
          apply LinearMap.ext
          intro x
          induction x using Submodule.Quotient.induction_on with
          | H x => exact IntertwiningMap.isIntertwining τ σ f g x }
      have hq : q ≠ 0 := by
        intro hq
        apply hf
        ext x
        exact congrArg (fun z : S.quotientRepresentation.IntertwiningMap σ =>
          z (S.toSubmodule.mkQ x)) hq
      let := simple
      let e := q.ofBijective ((IsIrreducible.bijective_or_eq_zero q).resolve_right hq)
      simpa only [e.toLinearEquiv.finrank_eq, charpoly_equiv e x] using spectrum
    · exact ih r hr

section Transport
variable {H : Type*} [Group H] {x : H}
omit [FiniteDimensional k V] [FiniteDimensional k W] in
private theorem irreducible_transport
    {ρ : Representation k H V} {σ : Representation k G W}
    (f : H →* G) (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (ρ g v) = σ (f g) (e v))
    [IsIrreducible ρ] : IsIrreducible σ := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  let : Nontrivial W := e.toEquiv.injective.nontrivial
  rw [IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation ρ := {
    toSubmodule := S.toSubmodule.comap e.toLinearMap
    apply_mem_toSubmodule g v hv := by
      change e (ρ g v) ∈ S.toSubmodule
      rw [he]
      exact S.apply_mem_toSubmodule (f g) hv }
  rcases eq_bot_or_eq_top T with h | h
  · left
    apply le_antisymm _ bot_le
    intro w hw
    obtain ⟨v, rfl⟩ := e.surjective w
    have hv : v ∈ T := hw
    rw [h] at hv
    change v = 0 at hv
    change e v = 0
    rw [hv, map_zero]
  · right
    apply le_antisymm le_top
    intro w _
    obtain ⟨v, rfl⟩ := e.surjective w
    have hv : v ∈ T := by rw [h]; trivial
    exact hv

/-- Transport every invariant subspace, quotient and actor polynomial through
an equivariant equivalence and a surjective homomorphism of acting groups. -/
theorem transport {ρ : Representation k H V}
    (h : Representation.FactorPolynomialFiltration P x ρ)
    (f : H →* G) (hf : Function.Surjective f)
    (σ : Representation k G W) (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (ρ g v) = σ (f g) (e v)) :
    Representation.FactorPolynomialFiltration P (f x) σ := by
  induction h generalizing W with
  | zero τ =>
    let : Subsingleton W := e.symm.injective.subsingleton
    exact .zero σ
  | @step X _ _ _ τ S previous simple spectrum ih =>
    let T : Subrepresentation σ := {
      toSubmodule := S.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule g w hw := by
        obtain ⟨a, rfl⟩ := hf g
        obtain ⟨v, hv, rfl⟩ := hw
        exact ⟨τ a v, S.apply_mem_toSubmodule a hv, he a v⟩ }
    let es : S.toSubmodule ≃ₗ[k] T.toSubmodule := e.submoduleMap S.toSubmodule
    have hes : ∀ g v, es (S.toRepresentation g v) = T.toRepresentation (f g) (es v) := by
      intro g v
      apply Subtype.ext
      exact he g v.val
    let eq : (X ⧸ S.toSubmodule) ≃ₗ[k] (W ⧸ T.toSubmodule) :=
      Submodule.Quotient.equiv S.toSubmodule T.toSubmodule e rfl
    have heq : ∀ g v, eq (S.quotientRepresentation g v) =
        T.quotientRepresentation (f g) (eq v) := by
      intro g v
      induction v using Submodule.Quotient.induction_on with
      | H v => exact congrArg T.toSubmodule.mkQ (he g v)
    refine .step T (ih T.toRepresentation es hes) ?_ ?_
    · let := simple
      exact irreducible_transport f eq heq
    · have hc : (S.quotientRepresentation x).charpoly =
          (T.quotientRepresentation (f x)).charpoly := by
        let E : S.quotientRepresentation.Equiv (T.quotientRepresentation.comp f) :=
          .mk eq (by intro g; apply LinearMap.ext; intro v; exact heq g v)
        exact charpoly_equiv E x
      simpa only [eq.finrank_eq, hc] using spectrum

end Transport

section Exact
variable {U : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
  {τ : Representation k G U}
/-- An injective kernel parametrization and a map to a filtered representation
assemble a filtration of the middle representation. The latter map need not
be surjective. -/
theorem of_exact (hτ : FactorPolynomialFiltration P x τ) (hσ : FactorPolynomialFiltration P x σ)
    (i : τ.IntertwiningMap ρ) (f : ρ.IntertwiningMap σ)
    (hi : Function.Injective i) (hex : ∀ v, f v = 0 ↔ ∃ u, i u = v) :
    FactorPolynomialFiltration P x ρ := by
  induction hσ generalizing V with
  | zero υ =>
    have his : Function.Surjective i := fun v => (hex v).mp (Subsingleton.elim _ _)
    apply hτ.transport (MonoidHom.id G) (fun g => ⟨g, rfl⟩) ρ
      (i.ofBijective ⟨hi, his⟩).toLinearEquiv
    intro g v
    exact LinearMap.congr_fun (i.isIntertwining' g) v
  | @step X _ _ _ υ S previous simple spectrum ih =>
    let q : υ.IntertwiningMap S.quotientRepresentation := {
      toLinearMap := S.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
    let p := q.comp f
    let T := p.ker
    have hT (v : V) : v ∈ T ↔ f v ∈ S := by
      change S.toSubmodule.mkQ (f v) = 0 ↔ f v ∈ S.toSubmodule
      exact Submodule.Quotient.mk_eq_zero _
    let it : τ.IntertwiningMap T.toRepresentation := {
      toLinearMap := i.toLinearMap.codRestrict T.toSubmodule (by
        intro u
        apply (hT _).mpr
        have hf : f (i u) = 0 := (hex _).mpr ⟨u, rfl⟩
        change f (i u) ∈ S
        rw [hf]
        exact S.toSubmodule.zero_mem)
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro u
        apply Subtype.ext
        exact LinearMap.congr_fun (i.isIntertwining' g) u }
    let ft : T.toRepresentation.IntertwiningMap S.toRepresentation := {
      toLinearMap := (f.toLinearMap.comp T.toSubmodule.subtype).codRestrict
        S.toSubmodule (fun v => (hT v.val).mp v.property)
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact LinearMap.congr_fun (f.isIntertwining' g) v.val }
    have hit : Function.Injective it := by
      intro u v h
      exact hi (congrArg Subtype.val h)
    have hext (v : T.toSubmodule) : ft v = 0 ↔ ∃ u, it u = v := by
      constructor
      · intro h
        obtain ⟨u, hu⟩ := (hex v.val).mp (congrArg Subtype.val h)
        exact ⟨u, Subtype.ext hu⟩
      · rintro ⟨u, hu⟩
        apply Subtype.ext
        exact (hex v.val).mpr ⟨u, congrArg Subtype.val hu⟩
    have ht : FactorPolynomialFiltration P x T.toRepresentation := ih it ft hit hext
    by_cases hp : p = 0
    · let e : T.toSubmodule ≃ₗ[k] V := {
        toFun := Subtype.val
        invFun := fun v => ⟨v, by
          change p v = 0
          rw [hp]
          rfl⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      apply ht.transport (MonoidHom.id G) (fun g => ⟨g, rfl⟩) ρ e
      intro g v
      rfl
    · let := simple
      have hps : Function.Surjective p :=
        (IsIrreducible.surjective_or_eq_zero p).resolve_right hp
      let e : T.quotientRepresentation.Equiv S.quotientRepresentation :=
        .mk (p.toLinearMap.quotKerEquivOfSurjective hps) (by
          intro g
          apply LinearMap.ext
          intro v
          induction v using Submodule.Quotient.induction_on with
          | H v => exact LinearMap.congr_fun (p.isIntertwining' g) v)
      refine .step T ht ((RepEquiv.ofRepresentationEquiv e).irreducible_of_euqiv simple) ?_
      simpa only [e.toLinearEquiv.finrank_eq, charpoly_equiv e x] using spectrum

/-- A filtered kernel and filtered codomain give a filtration of the domain. -/
theorem of_ker (f : ρ.IntertwiningMap σ)
    (hker : FactorPolynomialFiltration P x f.ker.toRepresentation)
    (hσ : FactorPolynomialFiltration P x σ) : FactorPolynomialFiltration P x ρ := by
  let i : f.ker.toRepresentation.IntertwiningMap ρ := {
    toLinearMap := f.ker.toSubmodule.subtype
    isIntertwining' := fun _ => rfl }
  apply of_exact hker hσ i f Subtype.val_injective
  intro v
  exact ⟨fun h => ⟨⟨v, h⟩, rfl⟩, fun ⟨u, hu⟩ => hu ▸ u.property⟩


/-- Every invariant subspace inherits a filtration with the same simple spectra. -/
theorem subrepresentation (h : FactorPolynomialFiltration P x ρ)
    (S : Subrepresentation ρ) : FactorPolynomialFiltration P x S.toRepresentation := by
  let i : S.toRepresentation.IntertwiningMap ρ := {
    toLinearMap := S.toSubmodule.subtype
    isIntertwining' _ := rfl }
  have hz : i.ker = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    exact LinearMap.ker_eq_bot.mpr Subtype.val_injective
  have : Subsingleton i.ker.toSubmodule := by
    rw [hz]
    exact inferInstanceAs (Subsingleton (⊥ : Submodule k S.toSubmodule))
  exact of_ker i (.zero _) h

/-- The certificate on a filtration holds on every literal irreducible subquotient. -/
theorem subquotient_spectrum (h : FactorPolynomialFiltration P x ρ)
    (S : Subrepresentation ρ) (T : Subrepresentation S.toRepresentation)
    (hi : IsIrreducible T.quotientRepresentation) :
    P (Module.finrank k (S.toSubmodule ⧸ T.toSubmodule))
      (T.quotientRepresentation x).charpoly := by
  let q : S.toRepresentation.IntertwiningMap T.quotientRepresentation := {
    toLinearMap := T.toSubmodule.mkQ
    isIntertwining' _ := rfl }
  let := hi
  let : Nontrivial (S.toSubmodule ⧸ T.toSubmodule) :=
    Subrepresentation.irreducible_module_nontrivial T.quotientRepresentation
  apply (h.subrepresentation S).quotient_spectrum q
  intro hz
  obtain ⟨v, hv⟩ := exists_ne (0 : S.toSubmodule ⧸ T.toSubmodule)
  obtain ⟨u, hu⟩ := T.toSubmodule.mkQ_surjective v
  exact hv (hu.symm.trans (congrArg (fun f => f u) hz))
end Exact

open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
/-- A finite invariant flag supplies the spectral filtration using its literal quotients. -/
theorem of_flag (n : ℕ) (S : ℕ → Subrepresentation ρ)
    (hzero : S 0 = ⊥) (hlast : S n = ⊤)
    (hmono : ∀ m, m < n → S m ≤ S (m + 1))
    (hsimple : ∀ m, m < n → IsIrreducible (within (S m) (S (m + 1))).quotientRepresentation)
    (hspectrum : ∀ m, m < n →
      P (Module.finrank k ((S (m + 1)).toSubmodule ⧸
        (within (S m) (S (m + 1))).toSubmodule))
        ((within (S m) (S (m + 1))).quotientRepresentation x).charpoly) :
    FactorPolynomialFiltration P x ρ := by
  have aux : ∀ m, m ≤ n → FactorPolynomialFiltration P x (S m).toRepresentation := by
    intro m
    induction m with
    | zero =>
      intro _
      have : Subsingleton (S 0).toSubmodule := by
        rw [hzero]
        exact inferInstanceAs (Subsingleton (⊥ : Submodule k V))
      exact .zero _
    | succ m ih =>
      intro hm
      have hmn : m < n := by omega
      let U := within (S m) (S (m + 1))
      have hp : FactorPolynomialFiltration P x U.toRepresentation := by
        apply (ih (by omega)).transport (MonoidHom.id G) (fun x => ⟨x, rfl⟩)
          U.toRepresentation (withinEquiv (S m) (S (m + 1)) (hmono m hmn))
        intro g v
        rfl
      exact .step U hp (hsimple m hmn) (hspectrum m hmn)
  let e : (S n).toSubmodule ≃ₗ[k] V := {
    toFun := Subtype.val
    invFun := fun x => ⟨x, by rw [hlast]; trivial⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  apply (aux n le_rfl).transport (MonoidHom.id G) (fun x => ⟨x, rfl⟩) ρ e
  intro g v
  rfl

end FactorPolynomialFiltration
end Representation
