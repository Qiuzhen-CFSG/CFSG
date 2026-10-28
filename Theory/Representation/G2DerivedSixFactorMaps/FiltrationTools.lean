module

public import Theory.Representation.FactorMapFiltration
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.FlagTools
public import Theory.Representation.RepEquiv
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Transport and exact extensions of filtrations with factor maps

Transport a filtration, including its actual quotient intertwiners, through
an equivariant linear equivalence and a surjective change of acting group.
Pullback along an exact sequence and finite products preserve these maps:
each surviving quotient is equivalent to the corresponding simple factor.
Finite invariant flags can therefore be assembled with specified factor maps.

These are the map-retaining versions of the degree-filtration constructions
used for the binary G₂ flag module. The application is Aschbacher--Smith
G.9.3(10), printed pp.354,356--357.
-/

@[expose] public section

namespace Representation.FactorMapFiltration

variable {k H G : Type*} [Field k] [Group H] [Group G]
  {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

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

/-- Transport invariant subspaces, literal quotients and their specified nonzero
maps through an equivalence and a surjective change of acting group. -/
theorem transport {Z : Type*} [AddCommGroup Z] [Module k Z]
    (η : Representation k G Z) (f : H →* G) (hf : Function.Surjective f)
    {ρ : Representation k H V} (h : Representation.FactorMapFiltration (η.comp f) ρ)
    (σ : Representation k G W) (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (ρ g v) = σ (f g) (e v)) :
    Representation.FactorMapFiltration η σ := by
  induction h generalizing W with
  | zero τ =>
    let : Subsingleton W := e.symm.injective.subsingleton
    exact .zero σ
  | @step X _ _ τ S previous simple degree ih =>
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
    · intro hd
      obtain ⟨p, hp⟩ := degree (eq.finrank_eq.trans hd)
      let q : T.quotientRepresentation.IntertwiningMap η := {
        toLinearMap := p.toLinearMap.comp eq.symm.toLinearMap
        isIntertwining' := by
          intro g
          obtain ⟨a, rfl⟩ := hf g
          apply LinearMap.ext
          intro v
          obtain ⟨x, rfl⟩ := eq.surjective v
          change p (eq.symm (T.quotientRepresentation (f a) (eq x))) = η (f a) (p (eq.symm (eq x)))
          rw [← heq]
          simp only [eq.symm_apply_apply]
          exact LinearMap.congr_fun (p.isIntertwining' a) x }
      refine ⟨q, fun hq => hp ?_⟩
      ext x
      have hx := congrArg (fun z : T.quotientRepresentation.IntertwiningMap η => z (eq x)) hq
      simpa [q] using hx

end Representation.FactorMapFiltration

namespace Representation.FactorMapFiltration

variable {k G U V W : Type*} [Field k] [Group G]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
  {τ : Representation k G U} {ρ : Representation k G V} {σ : Representation k G W}
  {Z : Type*} [AddCommGroup Z] [Module k Z] {η : Representation k G Z}

/-- An injective kernel parametrization and a map to a filtered representation
assemble a filtration of the middle representation. The latter map need not
be surjective. -/
theorem of_exact (hτ : FactorMapFiltration η τ) (hσ : FactorMapFiltration η σ)
    (i : τ.IntertwiningMap ρ) (f : ρ.IntertwiningMap σ)
    (hi : Function.Injective i) (hex : ∀ v, f v = 0 ↔ ∃ u, i u = v) :
    FactorMapFiltration η ρ := by
  induction hσ generalizing V with
  | zero υ =>
    have his : Function.Surjective i := fun v => (hex v).mp (Subsingleton.elim _ _)
    apply transport η (MonoidHom.id G) (fun g => ⟨g, rfl⟩) hτ ρ
      (i.ofBijective ⟨hi, his⟩).toLinearEquiv
    intro g v
    exact LinearMap.congr_fun (i.isIntertwining' g) v
  | @step X _ _ υ S previous simple degree ih =>
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
    have ht : FactorMapFiltration η T.toRepresentation := ih it ft hit hext
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
      apply transport η (MonoidHom.id G) (fun g => ⟨g, rfl⟩) ht ρ e
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
      intro hd
      obtain ⟨p, hp⟩ := degree (e.toLinearEquiv.finrank_eq.symm.trans hd)
      refine ⟨p.comp e.toIntertwiningMap, fun hz => hp ?_⟩
      ext x
      obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective x
      exact congrArg (fun q : T.quotientRepresentation.IntertwiningMap η => q v) hz

/-- A filtered kernel and filtered codomain give a filtration of the domain. -/
theorem of_ker (f : ρ.IntertwiningMap σ)
    (hker : FactorMapFiltration η f.ker.toRepresentation)
    (hσ : FactorMapFiltration η σ) : FactorMapFiltration η ρ := by
  let i : f.ker.toRepresentation.IntertwiningMap ρ := {
    toLinearMap := f.ker.toSubmodule.subtype
    isIntertwining' := fun _ => rfl }
  apply of_exact hker hσ i f Subtype.val_injective
  intro v
  exact ⟨fun h => ⟨⟨v, h⟩, rfl⟩, fun ⟨u, hu⟩ => hu ▸ u.property⟩

/-- Products retain nonzero maps on all simple factors of the target dimension. -/
theorem prod (hρ : FactorMapFiltration η ρ) (hσ : FactorMapFiltration η σ) :
    FactorMapFiltration η (ρ.prod σ) := by
  apply of_exact hσ hρ (IntertwiningMap.inr k ρ σ) (IntertwiningMap.fst k ρ σ)
  · intro v w h
    exact congrArg Prod.snd h
  · intro v
    change v.1 = 0 ↔ ∃ w, (0, w) = v
    exact ⟨fun h => ⟨v.2, Prod.ext h.symm rfl⟩,
      fun ⟨w, h⟩ => (congrArg Prod.fst h).symm⟩

end Representation.FactorMapFiltration

namespace Representation.FactorMapFiltration
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
/-- Assemble a finite flag using its actual successive quotient actions. -/
theorem of_flag {k G V Z : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup Z] [Module k Z]
    {ρ : Representation k G V} (η : Representation k G Z) (n : ℕ) (S : ℕ → Subrepresentation ρ)
    (hzero : S 0 = ⊥) (hlast : S n = ⊤)
    (hmono : ∀ m, m < n → S m ≤ S (m + 1))
    (hsimple : ∀ m, m < n → IsIrreducible (within (S m) (S (m + 1))).quotientRepresentation)
    (hmaps : ∀ m, m < n →
      Module.finrank k ((S (m + 1)).toSubmodule ⧸ (within (S m) (S (m + 1))).toSubmodule) = Module.finrank k Z →
      ∃ f : (within (S m) (S (m + 1))).quotientRepresentation.IntertwiningMap η, f ≠ 0) :
    FactorMapFiltration η ρ := by
  have aux : ∀ m, m ≤ n → FactorMapFiltration η (S m).toRepresentation := by
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
      have hp : FactorMapFiltration η U.toRepresentation := by
        apply transport η (MonoidHom.id G) (fun x => ⟨x, rfl⟩) (ih (by omega))
          U.toRepresentation (withinEquiv (S m) (S (m + 1)) (hmono m hmn))
        intro g v
        rfl
      exact .step U hp (hsimple m hmn) (hmaps m hmn)
  let e : (S n).toSubmodule ≃ₗ[k] V := {
    toFun := Subtype.val
    invFun := fun x => ⟨x, by rw [hlast]; trivial⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  apply transport η (MonoidHom.id G) (fun x => ⟨x, rfl⟩) (aux n le_rfl) ρ e
  intro g v
  rfl


end Representation.FactorMapFiltration

namespace Representation.FactorMapFiltration

/-- A filtration with no factor of the target dimension needs no factor maps. -/
theorem of_degree {k G V W : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} (σ : Representation k G W) {D : Set ℕ}
    (h : FactorDegreeFiltration D ρ) (hd : Module.finrank k W ∉ D) :
    FactorMapFiltration σ ρ := by
  induction h with
  | zero τ => exact .zero τ
  | step S _ simple degree ih =>
    exact .step S ih simple (fun he => False.elim (hd (he ▸ degree)))

end Representation.FactorMapFiltration
