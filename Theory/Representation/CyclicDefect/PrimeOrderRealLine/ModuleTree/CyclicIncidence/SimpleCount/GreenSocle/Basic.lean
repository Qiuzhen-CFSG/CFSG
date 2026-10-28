module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount.Centralizer
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount.Classes
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount.LocalBlock
public import Theory.Representation.KrullSchmidt
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.Algebra.Module.Projective

/-!
# Actual Green summands, stable maps, and simple socles

The socle is the sum of all simple subrepresentations. A nonzero map from a
simple module to a module with simple socle identifies those simple modules;
a uniserial module has a simple socle by atomicity of its submodule lattice.
Stable nonzero maps are represented by intertwiners which do not factor through
finite-dimensional projectives. Factoring the identity is equivalent to actual
module projectivity.

The final two contracts separate the missing Green restriction/transport
argument from local serial-module theory. Their fields retain actual modules,
intertwiners, projective complements, and the literal normalizer block element.
Neither contract is constructed here. Their consumer is `SimpleCount.GreenSocle`.

Source: Feit, *The Representation Theory of Finite Groups*, VII.1.4--5,
VII.3.5 and VII.3.10--12 (printed pp.273, 282, 285--286).
-/

public section
noncomputable section

namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount.GreenSocle
variable {K H : Type*} [Field K] [Group H]

/-- A finite-dimensional matrix representation selected by the literal block element. -/
structure BlockModel (e : MonoidAlgebra K H) where
  degree : ℕ
  rep : Representation K H (Fin degree → K)
  inBlock : rep.asAlgebraHom e = 1

/-- A selected, nonzero indecomposable module which is not projective over the group algebra. -/
structure NonprojectiveModel (e : MonoidAlgebra K H) extends BlockModel e where
  indecomposable : Module.IsIndecomposable (MonoidAlgebra K H) rep.asModule
  nonprojective : ¬ Module.Projective (MonoidAlgebra K H) rep.asModule

variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Factorization through an actual finite-dimensional projective representation. -/
@[expose] def FactorsThroughProjective {ρ : Representation K H V} {σ : Representation K H W}
    (f : ρ.IntertwiningMap σ) : Prop :=
  ∃ (k : ℕ) (π : Representation K H (Fin k → K)),
    Module.Projective (MonoidAlgebra K H) π.asModule ∧
    ∃ (a : ρ.IntertwiningMap π) (b : π.IntertwiningMap σ), b.comp a = f

/-- The zero map factors through the zero projective module. -/
theorem factorsThroughProjective_zero (ρ : Representation K H V)
    (σ : Representation K H W) :
    FactorsThroughProjective (0 : ρ.IntertwiningMap σ) := by
  let π := Representation.trivial K H (Fin 0 → K)
  let : Subsingleton π.asModule := π.asModuleEquiv.injective.subsingleton
  have hp : Module.Projective (MonoidAlgebra K H) π.asModule :=
    ⟨⟨0, fun _ => Subsingleton.elim _ _⟩⟩
  exact ⟨0, π, hp, 0, 0, by ext; rfl⟩

/-- Factoring the identity through a projective is precisely projectivity. -/
theorem factorsThroughProjective_id_iff {k : ℕ}
    (ρ : Representation K H (Fin k → K)) :
    FactorsThroughProjective (Representation.IntertwiningMap.id ρ) ↔
      Module.Projective (MonoidAlgebra K H) ρ.asModule := by
  constructor
  · rintro ⟨j, π, hp, i, s, hs⟩
    let := hp
    apply Module.Projective.of_split
      (Representation.IntertwiningMap.equivLinearMapAsModule ρ π i)
      (Representation.IntertwiningMap.equivLinearMapAsModule π ρ s)
    have he := congrArg (Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ) hs
    exact he
  · intro hp
    exact ⟨k, ρ, hp, Representation.IntertwiningMap.id ρ,
      Representation.IntertwiningMap.id ρ, by ext; rfl⟩

/-- Projective factorizations are preserved by precomposition. -/
theorem FactorsThroughProjective.precomp {U : Type*} [AddCommGroup U] [Module K U]
    {ρ : Representation K H U} {σ : Representation K H V} {τ : Representation K H W}
    {f : σ.IntertwiningMap τ} (hf : FactorsThroughProjective f)
    (g : ρ.IntertwiningMap σ) : FactorsThroughProjective (f.comp g) := by
  obtain ⟨k, π, hp, a, b, rfl⟩ := hf
  exact ⟨k, π, hp, a.comp g, b, by ext; rfl⟩

/-- Projective factorizations are preserved by postcomposition. -/
theorem FactorsThroughProjective.postcomp {U : Type*} [AddCommGroup U] [Module K U]
    {ρ : Representation K H U} {σ : Representation K H V} {τ : Representation K H W}
    {f : ρ.IntertwiningMap σ} (hf : FactorsThroughProjective f)
    (g : σ.IntertwiningMap τ) : FactorsThroughProjective (g.comp f) := by
  obtain ⟨k, π, hp, a, b, rfl⟩ := hf
  exact ⟨k, π, hp, a, g.comp b, by ext; rfl⟩

/-- A nonzero stable Hom class, witnessed by an actual intertwiner that does not
factor through a finite-dimensional projective. -/
@[expose] def HasStableHom (ρ : Representation K H V) (σ : Representation K H W) : Prop :=
  ∃ f : ρ.IntertwiningMap σ, ¬ FactorsThroughProjective f

/-- A nonzero stable class has a nonzero ordinary intertwiner. -/
theorem HasStableHom.exists_nonzero {ρ : Representation K H V}
    {σ : Representation K H W} (h : HasStableHom ρ σ) :
    ∃ f : ρ.IntertwiningMap σ, f ≠ 0 := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun hz => hf (hz ▸ factorsThroughProjective_zero ρ σ)⟩

/-- The actual socle: the sum of the simple subrepresentations. -/
@[expose] def socle (ρ : Representation K H V) : Subrepresentation ρ :=
  sSup {U | IsAtom U}

/-- A nonzero finite-dimensional uniserial representation has simple socle. -/
theorem isAtom_socle_of_total (ρ : Representation K H V)
    [FiniteDimensional K V] [Nontrivial V]
    (htotal : ∀ U T : Subrepresentation ρ, U ≤ T ∨ T ≤ U) : IsAtom (socle ρ) := by
  obtain ⟨U, hU⟩ := IsAtomic.exists_atom (Subrepresentation ρ)
  have heq : socle ρ = U := by
    apply le_antisymm
    · apply sSup_le
      intro T hT
      rcases htotal T U with hle | hle
      · exact hle
      · exact ((hT.le_iff_eq hU.ne_bot).mp hle).ge
    · exact le_sSup hU
  exact heq.symm ▸ hU

/-- A nonzero map out of a simple representation has simple image. -/
theorem isAtom_range_of_nonzero {ρ : Representation K H V}
    {σ : Representation K H W} [Representation.IsIrreducible ρ]
    (f : ρ.IntertwiningMap σ) (hf : f ≠ 0) : IsAtom f.range := by
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  let q : ρ.IntertwiningMap f.range.toRepresentation :=
    { toLinearMap := f.toLinearMap.rangeRestrict
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        change f (ρ g x) = σ g (f x)
        exact Representation.IntertwiningMap.isIntertwining ρ σ f g x }
  have hq : Function.Bijective q :=
    ⟨fun _ _ hh => hi (congrArg Subtype.val hh),
      fun ⟨_, x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩
  apply (Subrepresentation.irreducible_iff_isAtom f.range).mp
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ q) hq).mp inferInstance

/-- A matrix model of the actual socle, with its equivariant inclusion and
equality to the sum of all simple subrepresentations. -/
structure SimpleSocle {e : MonoidAlgebra K H} (M : BlockModel e) where
  simple : SimpleModel e
  inclusion : simple.rep.IntertwiningMap M.rep
  injective : Function.Injective inclusion
  range_eq : inclusion.range = socle M.rep

/-- In a uniserial module every embedded simple is the actual socle. -/
def SimpleSocle.of_total {e : MonoidAlgebra K H} (M : NonprojectiveModel e)
    (T : SimpleModel e) (f : T.rep.IntertwiningMap M.rep) (hf : Function.Injective f)
    (htotal : ∀ U V : Subrepresentation M.rep, U ≤ V ∨ V ≤ U) :
    SimpleSocle M.toBlockModel := by
  let := T.irreducible
  let : Nontrivial (Fin T.degree → K) := Subrepresentation.irreducible_module_nontrivial T.rep
  let : Nontrivial (Fin M.degree → K) := hf.nontrivial
  have hne : f ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := exists_ne (0 : Fin T.degree → K)
    apply hx
    apply hf
    rw [hz]
    rfl
  have ha := isAtom_range_of_nonzero f hne
  exact ⟨T, f, hf, ((isAtom_socle_of_total M.rep htotal).le_iff_eq ha.ne_bot).mp
    (le_sSup ha)⟩

/-- A nonzero map from a simple into a module with simple socle identifies
that source with the actual socle. -/
theorem SimpleSocle.equiv_of_nonzero {e : MonoidAlgebra K H} {M : BlockModel e}
    (s : SimpleSocle M) (T : SimpleModel e) (f : T.rep.IntertwiningMap M.rep)
    (hf : f ≠ 0) : Nonempty (T.rep.Equiv s.simple.rep) := by
  let := T.irreducible
  let := s.simple.irreducible
  have hle : f.range ≤ s.inclusion.range := by
    rw [s.range_eq]
    exact le_sSup (isAtom_range_of_nonzero f hf)
  let eι := LinearEquiv.ofInjective s.inclusion.toLinearMap s.injective
  let g₀ : (Fin T.degree → K) →ₗ[K] (Fin s.simple.degree → K) :=
    eι.symm.toLinearMap.comp (f.toLinearMap.codRestrict _ (fun x => hle ⟨x, rfl⟩))
  have hfac (x : Fin T.degree → K) : s.inclusion (g₀ x) = f x := by
    exact congrArg Subtype.val (eι.apply_symm_apply ⟨f x, hle ⟨x, rfl⟩⟩)
  let g : T.rep.IntertwiningMap s.simple.rep :=
    { toLinearMap := g₀
      isIntertwining' := by
        intro a
        apply LinearMap.ext
        intro x
        apply s.injective
        change s.inclusion (g₀ (T.rep a x)) = s.inclusion (s.simple.rep a (g₀ x))
        rw [hfac, s.inclusion.isIntertwining, hfac, f.isIntertwining] }
  have hg : g ≠ 0 := by
    intro hz
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hx : g₀ x = 0 := congrArg (fun t : T.rep.IntertwiningMap s.simple.rep => t x) hz
    change f x = 0
    simpa only [hx, map_zero] using (hfac x).symm
  exact ⟨g.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero g).resolve_right hg)⟩

/-- The local serial-module consequences needed by the socle correspondence.
This is an explicit prerequisite, not an assertion that these consequences hold.
`overlap` is the stable Hom separation step of Feit VII.3.10--11. -/
structure LocalSocleTheory (e : MonoidAlgebra K H) : Prop where
  exists_socle : ∀ M : NonprojectiveModel e, Nonempty (SimpleSocle M.toBlockModel)
  overlap : ∀ (M T : NonprojectiveModel e)
    (s : SimpleSocle M.toBlockModel) (t : SimpleSocle T.toBlockModel),
    Nonempty (s.simple.rep.Equiv t.simple.rep) →
      HasStableHom M.rep T.rep ∨ HasStableHom T.rep M.rep

variable {G : Type*} [Group G]

/-- A genuine nonprojective indecomposable summand of restriction, with an
actual projective complement. For a Sylow subgroup of prime order the Green
restriction decomposition has this form: the other terms are projective. -/
structure GreenSummand (H : Subgroup G) {k : ℕ}
    (ρ : Representation K G (Fin k → K)) {e : MonoidAlgebra K H}
    (M : NonprojectiveModel e) where
  complementDegree : ℕ
  complement : Representation K H (Fin complementDegree → K)
  projective : Module.Projective (MonoidAlgebra K H) complement.asModule
  splitting : Representation.Equiv (ρ.comp H.subtype) (M.rep.prod complement)

variable [Finite G] {p m n : ℕ}
    {d : ModularBlock.PrimeBlockConstruction.PrimeCongruenceBlockData p G}
    {residue : Localization.AtPrime d.primeIdeal →+* K} {L : CyclicRootLift K m}

/-- The representation-theoretic Green inputs for the supplied ambient family.
The local modules are actual summands of restriction to the literal normalizer.
Orthogonality comes from stable Hom transport (Feit VII.1.4--5); coverage comes
from inverse Green correspondence and a simple quotient (VII.3.12).
No local count, simple-socle conclusion, or class equivalence is a field. -/
structure GreenFamily (a : Decomposition d residue L n) (P : Sylow p G) where
  model : Fin n → NonprojectiveModel (normalizerSelector d residue P)
  summand : ∀ i, GreenSummand (Subgroup.normalizer (P : Set G)) (a.rep i) (model i)
  orthogonal : Pairwise fun i j => ¬ HasStableHom (model i).rep (model j).rep
  coverage : ∀ T : SimpleModel (normalizerSelector d residue P),
    ∃ i, HasStableHom T.rep (model i).rep

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount.GreenSocle
