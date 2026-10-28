module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.Reduction
public import Theory.Representation.RepEquiv
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Carrying odd displacement through the actual binary G₂ filtration

The marking into the derived group records which elements are regular threes
or sevens, even when coordinates use a free group. A filtration retains the
odd displacement bounds on every simple factor above degree eight. Exact
pullback, products and equivariant transport preserve that information.
A nonzero map to an irreducible module then identifies that module with one
of the actual simple quotients; no assumed module catalogue is used.

This is the quotient-transport step for Guralnick–Malle, Classification of
2F-modules I, Proposition 4.3, pp.10–11, extended to include degree 32.
-/

@[expose] public noncomputable section

universe u
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements
open Representation Representation.BinaryOffender Subgroup

/-- Odd-element bounds relative to the literal marking of the acting group. -/
structure MarkedBounds {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (π : G →* Derived) (ρ : Representation (ZMod 2) G V) : Prop where
  regular_three : ∀ x, RegularThree (π x) → 10 ≤ fixedCodim ρ (zpowers x)
  seven : ∀ x, orderOf (π x) = 7 → 12 ≤ fixedCodim ρ (zpowers x)

/-- The marking and an equivariant equivalence retain the actual fixed spaces. -/
theorem MarkedBounds.transport {H G V W : Type*} [Group H] [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H V} {σ : Representation (ZMod 2) G W}
    (π : G →* Derived) (f : H →* G) (hf : Function.Surjective f)
    (e : V ≃ₗ[ZMod 2] W) (he : ∀ g v, e (ρ g v) = σ (f g) (e v))
    (h : MarkedBounds (π.comp f) ρ) : MarkedBounds π σ := by
  have hc (x : H) : fixedCodim ρ (zpowers x) = fixedCodim σ (zpowers (f x)) := by
    simpa only [MonoidHom.map_zpowers] using
      fixedCodim_map_equivariant ρ σ f e he (zpowers x)
  constructor
  · intro x hx
    obtain ⟨w, rfl⟩ := hf x
    rw [← hc]
    exact h.regular_three w hx
  · intro x hx
    obtain ⟨w, rfl⟩ := hf x
    rw [← hc]
    exact h.seven w hx

/-- Actual simple quotients, retaining their large-degree displacement bounds. -/
inductive BoundedFactors {G : Type*} [Group G] (π : G →* Derived) :
    {V : Type u} → [AddCommGroup V] → [Module (ZMod 2) V] →
      Representation (ZMod 2) G V → Prop
  | zero {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
      (ρ : Representation (ZMod 2) G V) [Subsingleton V] : BoundedFactors π ρ
  | step {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
      {ρ : Representation (ZMod 2) G V} (S : Subrepresentation ρ)
      (previous : BoundedFactors π S.toRepresentation)
      (simple : IsIrreducible S.quotientRepresentation)
      (bounds : 8 < Module.finrank (ZMod 2) (V ⧸ S.toSubmodule) →
        MarkedBounds π S.quotientRepresentation) : BoundedFactors π ρ

namespace BoundedFactors
variable {H G : Type*} [Group H] [Group G]
  {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

private theorem irreducible_transport
    {ρ : Representation (ZMod 2) H V} {σ : Representation (ZMod 2) G W}
    (f : H →* G) (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (ρ g v) = σ (f g) (e v))
    [IsIrreducible ρ] : IsIrreducible σ := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  let : Nontrivial W := e.toEquiv.injective.nontrivial
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
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

/-- Transport the full filtration along a surjective change of actors. -/
theorem transport (π : G →* Derived) (f : H →* G) (hf : Function.Surjective f)
    {ρ : Representation (ZMod 2) H V} (h : BoundedFactors (π.comp f) ρ)
    (σ : Representation (ZMod 2) G W) (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (ρ g v) = σ (f g) (e v)) : BoundedFactors π σ := by
  induction h generalizing W with
  | zero τ =>
    let : Subsingleton W := e.symm.injective.subsingleton
    exact .zero σ
  | @step X _ _ τ S previous simple bounds ih =>
    let T : Subrepresentation σ := {
      toSubmodule := S.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule g w hw := by
        obtain ⟨a, rfl⟩ := hf g
        obtain ⟨v, hv, rfl⟩ := hw
        exact ⟨τ a v, S.apply_mem_toSubmodule a hv, he a v⟩ }
    let es : S.toSubmodule ≃ₗ[ZMod 2] T.toSubmodule := e.submoduleMap S.toSubmodule
    have hes : ∀ g v, es (S.toRepresentation g v) = T.toRepresentation (f g) (es v) := by
      intro g v
      apply Subtype.ext
      exact he g v.val
    let eq : (X ⧸ S.toSubmodule) ≃ₗ[ZMod 2] (W ⧸ T.toSubmodule) :=
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
      exact (bounds (by rwa [eq.finrank_eq])).transport π f hf eq heq


end BoundedFactors

namespace BoundedFactors

variable {G U V W : Type*} [Group G]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  {τ : Representation (ZMod 2) G U} {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) G W}
  {π : G →* Derived}

/-- An injective kernel parametrization and a map to a filtered representation
assemble a filtration of the middle representation. The latter map need not
be surjective. -/
theorem of_exact (hτ : BoundedFactors π τ) (hσ : BoundedFactors π σ)
    (i : τ.IntertwiningMap ρ) (f : ρ.IntertwiningMap σ)
    (hi : Function.Injective i) (hex : ∀ v, f v = 0 ↔ ∃ u, i u = v) :
    BoundedFactors π ρ := by
  induction hσ generalizing V with
  | zero υ =>
    have his : Function.Surjective i := fun v => (hex v).mp (Subsingleton.elim _ _)
    apply transport π (MonoidHom.id G) (fun g => ⟨g, rfl⟩) hτ ρ
      (i.ofBijective ⟨hi, his⟩).toLinearEquiv
    intro g v
    exact LinearMap.congr_fun (i.isIntertwining' g) v
  | @step X _ _ υ S previous simple bounds ih =>
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
    have ht : BoundedFactors π T.toRepresentation := ih it ft hit hext
    by_cases hp : p = 0
    · let e : T.toSubmodule ≃ₗ[ZMod 2] V := {
        toFun := Subtype.val
        invFun := fun v => ⟨v, by
          change p v = 0
          rw [hp]
          rfl⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      apply transport π (MonoidHom.id G) (fun g => ⟨g, rfl⟩) ht ρ e
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
      apply (bounds (by rwa [← e.toLinearEquiv.finrank_eq])).transport
        π (MonoidHom.id G) (fun g => ⟨g, rfl⟩) e.symm.toLinearEquiv
      intro g v
      exact LinearMap.congr_fun (e.symm.toIntertwiningMap.isIntertwining' g) v

/-- A filtered kernel and filtered codomain give a filtration of the domain. -/
theorem of_ker (f : ρ.IntertwiningMap σ)
    (hker : BoundedFactors π f.ker.toRepresentation)
    (hσ : BoundedFactors π σ) : BoundedFactors π ρ := by
  let i : f.ker.toRepresentation.IntertwiningMap ρ := {
    toLinearMap := f.ker.toSubmodule.subtype
    isIntertwining' := fun _ => rfl }
  apply of_exact hker hσ i f Subtype.val_injective
  intro v
  exact ⟨fun h => ⟨⟨v, h⟩, rfl⟩, fun ⟨u, hu⟩ => hu ▸ u.property⟩

/-- Products retain the displacement bounds on their large simple factors. -/
theorem prod (hρ : BoundedFactors π ρ) (hσ : BoundedFactors π σ) :
    BoundedFactors π (ρ.prod σ) := by
  apply of_exact hσ hρ (IntertwiningMap.inr (ZMod 2) ρ σ) (IntertwiningMap.fst (ZMod 2) ρ σ)
  · intro v w h
    exact congrArg Prod.snd h
  · intro v
    change v.1 = 0 ↔ ∃ w, (0, w) = v
    exact ⟨fun h => ⟨v.2, Prod.ext h.symm rfl⟩,
      fun ⟨w, h⟩ => (congrArg Prod.fst h).symm⟩

end BoundedFactors

namespace BoundedFactors
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- Assemble a finite flag using its actual successive quotient actions. -/
theorem of_flag (π : G →* Derived) (n : ℕ) (S : ℕ → Subrepresentation ρ)
    (hzero : S 0 = ⊥) (hlast : S n = ⊤)
    (hmono : ∀ m, m < n → S m ≤ S (m + 1))
    (hsimple : ∀ m, m < n → IsIrreducible (within (S m) (S (m + 1))).quotientRepresentation)
    (hbounds : ∀ m, m < n →
      Module.finrank (ZMod 2) ((S (m + 1)).toSubmodule ⧸ (within (S m) (S (m + 1))).toSubmodule) > 8 →
      MarkedBounds π (within (S m) (S (m + 1))).quotientRepresentation) :
    BoundedFactors π ρ := by
  have aux : ∀ m, m ≤ n → BoundedFactors π (S m).toRepresentation := by
    intro m
    induction m with
    | zero =>
      intro _
      have : Subsingleton (S 0).toSubmodule := by
        rw [hzero]
        exact inferInstanceAs (Subsingleton (⊥ : Submodule (ZMod 2) V))
      exact .zero _
    | succ m ih =>
      intro hm
      have hmn : m < n := by omega
      let U := within (S m) (S (m + 1))
      have hp : BoundedFactors π U.toRepresentation := by
        apply transport π (MonoidHom.id G) (fun x => ⟨x, rfl⟩) (ih (by omega))
          U.toRepresentation (withinEquiv (S m) (S (m + 1)) (hmono m hmn))
        intro g v
        rfl
      exact .step U hp (hsimple m hmn) (hbounds m hmn)
  let e : (S n).toSubmodule ≃ₗ[ZMod 2] V := {
    toFun := Subtype.val
    invFun := fun x => ⟨x, by rw [hlast]; trivial⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  apply transport π (MonoidHom.id G) (fun x => ⟨x, rfl⟩) (aux n le_rfl) ρ e
  intro g v
  rfl


end BoundedFactors

variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) G W}

/-- Every irreducible quotient occurs in the finite filtration. -/
theorem BoundedFactors.quotient_bounds {π : G →* Derived}
    (h : BoundedFactors π ρ) [IsIrreducible σ]
    (hd : 8 < Module.finrank (ZMod 2) W)
    (f : ρ.IntertwiningMap σ) (hf : f ≠ 0) : MarkedBounds π σ := by
  induction h with
  | zero τ =>
    exfalso
    apply hf
    ext x
    exact (congrArg f (Subsingleton.elim x 0)).trans (map_zero f)
  | @step X _ _ τ S previous simple bounds ih =>
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
      apply (bounds (by rwa [e.toLinearEquiv.finrank_eq])).transport
        π (MonoidHom.id G) (fun g => ⟨g, rfl⟩) e.toLinearEquiv
      intro g v
      exact LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) v
    · exact ih r hr


end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements
