module
public import Theory.Representation.ProductIsotypic
public import Theory.Representation.ScalarMultiplicity.Faithful
public import Theory.Representation.OrthogonalFourMinusRankOne.AmbientActions.ScalarCentralizer
public import Theory.Representation.SL2.BinaryHermitianIrreducibility
public import Theory.Representation.SL2.PerfectCoreQuotientDegree
public import Theory.Representation.OrthogonalFourMinusFirstCohomology
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Faithful Hermitian multiplicity spaces for an irreducible product

The restriction to one factor is isotypic. A marked Hermitian constituent
therefore gives copy coordinates on the entire original space. Its binary
commutant is precisely the fixed field, so the commuting second factor acts
on a genuine multiplicity space over that field. The equations on pure vectors
retain both original actions and prove faithfulness of the second factor.

For a second SL₂(2^(2s)) factor, a surviving irreducible binary section forces
multiplicity at least four and total binary degree at least 16s. No small-action
or quotient-faithfulness hypothesis replaces the original product action.
The Chapter D two-kernel calculation and original Chapter 10 Hall consumer use
this obstruction. Source: Aschbacher--Smith D.3.7, printed pp.198--199,
using A.1.41--42 and the defining-characteristic SL₂ degree bound.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped MatrixGroups
namespace Representation.SL2.PairHermitian
open OrthogonalFourMinus.FiniteModel
variable {F H V : Type*} [Field F] [Finite F] [CharP F 2] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable (s : ℕ) [NeZero s]
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- Coordinates for both original factors, with a faithful action over the actual
Hermitian fixed field on the multiplicity space. -/
@[expose] def Coordinates (σ : Representation (ZMod 2) (SL(2,F) × H) V) : Prop :=
    ∃ (b : F ≃+* Field s) (m : ℕ) (e : V ≃ₗ[ZMod 2] (Fin m → Space s))
      (μ : Representation (fixedField s) H (Fin m → fixedField s)),
      Function.Injective μ ∧
      (∀ g v, e (σ (g,1) v) = fun i =>
        BinarySmall.hermitian s (Matrix.SpecialLinearGroup.map b.toRingHom g) (e v i)) ∧
      (∀ h c v, e (σ (1,h) (e.symm (fun i => c i • v))) =
        fun i => μ h c i • v) ∧
      Module.finrank (ZMod 2) V = m * (4*s)

omit [Finite F] [CharP F 2] in
/-- A Hermitian constituent constructs whole-space copy coordinates and the
faithful opposite action, preserving both original factor markings. -/
theorem coordinates_of_constituent
    (σ : Representation (ZMod 2) (SL(2,F) × H) V) [σ.IsIrreducible]
    (hf : Function.Injective σ)
    (I : Subrepresentation (ProductIsotypic.left σ)) (hI : I.toRepresentation.IsIrreducible)
    (hherm : BinarySmall.IsHermitian I.toRepresentation s) :
    Coordinates s σ := by
  classical
  let := hI
  let : Nontrivial I.toSubmodule := Subrepresentation.irreducible_module_nontrivial I.toRepresentation
  let f : I.toRepresentation.IntertwiningMap (ProductIsotypic.left σ) :=
    .mk I.toSubmodule.subtype (by intro g; ext v; rfl)
  have hf0 : f ≠ 0 := by
    obtain ⟨v,hv⟩ := exists_ne (0 : I.toSubmodule)
    intro hz
    exact hv (Subtype.ext (congrArg (fun f : I.toRepresentation.IntertwiningMap
      (ProductIsotypic.left σ) => f v) hz))
  obtain ⟨m,a,ha⟩ := ProductIsotypic.exists_copy_coordinates σ I.toRepresentation f hf0
  obtain ⟨b,⟨q⟩⟩ := hherm
  let : Nontrivial (Space s) := q.toLinearEquiv.injective.nontrivial
  let e := a.trans (LinearEquiv.piCongrRight fun _ => q.toLinearEquiv)
  have he (g : SL(2,F)) (v : V) : e (σ (g,1) v) = fun i =>
      BinarySmall.hermitian s (Matrix.SpecialLinearGroup.map b.toRingHom g) (e v i) := by
    change (fun i => q (a (σ (g,1) v) i)) = _
    rw [ha]
    funext i
    exact LinearMap.congr_fun (q.isIntertwining' g) (a v i)
  let τ : Representation (ZMod 2) H (Fin m → Space s) :=
    e.conjRingEquiv.toMonoidHom.comp (σ.comp (MonoidHom.inr _ _))
  have hτ : Function.Injective τ := by
    apply e.conjRingEquiv.injective.comp
    intro x y h
    exact congrArg Prod.snd (hf h)
  let ν := (BinarySmall.hermitian s).comp (Matrix.SpecialLinearGroup.map b.toRingHom)
  change ∀ g v, e (σ (g,1) v) = fun i => ν g (e v i) at he
  have hc (h : H) (g : SL(2,F)) (x : Fin m → Space s) :
      τ h (fun i => ν g (x i)) = fun i => ν g (τ h x i) := by
    obtain ⟨v,rfl⟩ := e.surjective x
    change e (σ (1,h) (e.symm (fun i => ν g (e v i)))) = _
    rw [←he g v,e.symm_apply_apply]
    have hcomm : σ (1,h) (σ (g,1) v) = σ (g,1) (σ (1,h) v) := by
      simp only [←Module.End.mul_apply,←map_mul,Prod.mk_mul_mk,one_mul,mul_one]
    rw [hcomm,he]
    change _ = fun i => ν g (e (σ (1,h) (e.symm (e v))) i)
    rw [e.symm_apply_apply]
  have hs (f : Space s →ₗ[ZMod 2] Space s)
      (hf : ∀ g v, f (ν g v) = ν g (f v)) :
      ∃ c : fixedField s, ∀ v, f v = c • v := by
    apply OrthogonalFourMinus.RankOne.AmbientActions.commuting_binaryEnd_eq_scalar s f
    intro g v
    let bG := Atlas.fieldEquivSL 2 b
    obtain ⟨g,rfl⟩ := bG.surjective g
    exact hf g v
  obtain ⟨μ,hμ⟩ := ScalarMultiplicity.exists_multiplicity ν hs τ hc
  have hμf : Function.Injective μ := by
    intro h k hh
    apply hτ
    apply LinearMap.ext
    intro x
    have hx : x = ∑ i : Fin m, Pi.single i (x i) := by ext i; simp
    rw [hx,map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hsingle (v : Space s) : (fun j => (Pi.single i (1 : fixedField s) : Fin m → fixedField s) j • v) =
        Pi.single i v := by
      funext j
      by_cases h : i = j
      · subst j; simp
      · simp [Ne.symm h]
    rw [←hsingle (x i),hμ,hμ,hh]
  refine ⟨b,m,e,μ,hμf,he,hμ,?_⟩
  rw [e.finrank_eq]
  have hd : Module.finrank (ZMod 2) (Space s) = 4*s := by
    convert finrank_binary_space s using 1
    congr 1
    exact Subsingleton.elim _ _
  simp [Module.finrank_pi_fintype,hd]

/-- A faithful action of SL₂(2^(2s)) over its half-field needs at least four coordinates. -/
theorem multiplicity_ge_four
    [Group.IsPerfect SL(2,F)] [Nontrivial SL(2,F)]
    (hF : Nat.card F = 2^(2*s)) {m : ℕ}
    (μ : Representation (fixedField s) SL(2,F) (Fin m → fixedField s))
    (hf : Function.Injective μ) : 4 ≤ m := by
  let τ : Representation (ZMod 2) SL(2,F) (Fin m → fixedField s) := {
    toFun g := (μ g).toAddMonoidHom.toZModLinearMap 2
    map_one' := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun μ.map_one v
    map_mul' g h := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (μ.map_mul g h) v }
  have hτ : Function.Injective τ := by
    intro x y h
    apply hf
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun h v
  have hnt : ¬ (⊤ : Subgroup SL(2,F)) ≤ τ.ker := by
    obtain ⟨g,hg⟩ := exists_ne (1 : SL(2,F))
    intro hh
    exact hg (hτ ((hh (mem_top g)).trans τ.map_one.symm))
  let : Group.IsPerfect (⊤ : Subgroup SL(2,F)) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := SL(2,F))).symm.toMonoidHom) (topEquiv (G := SL(2,F))).symm.surjective
  obtain ⟨U,N,hi,hN⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (ρ := τ) (⊤ : Subgroup SL(2,F)) hnt
  let := hi
  have hne : ∃ g, N.quotientRepresentation g ≠ 1 := by
    by_contra! hh
    exact hN (fun g _ => hh g)
  have hd := Unsigned.irreducible_finrank_bound 2 N.quotientRepresentation hne
    (2*s) (by have := NeZero.ne s; omega) hF
  have hle := (Submodule.finrank_quotient_le N.toSubmodule).trans
    (Submodule.finrank_le U.toSubmodule)
  have hdim : Module.finrank (ZMod 2) (Fin m → fixedField s) = m*s := by
    simp [Module.finrank_pi_fintype,finrank_binary_fixedField]
  have hh : 4*s ≤ m*s := by omega
  have hs : 0<s := NeZero.pos s
  nlinarith

omit [FiniteDimensional (ZMod 2) V] in
/-- The unchanged binary square has degree at least 16s whenever one factor
has Hermitian multiplicity coordinates. -/
theorem degree_lower_bound
    [Group.IsPerfect SL(2,F)] [Nontrivial SL(2,F)]
    (hF : Nat.card F = 2^(2*s))
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V)
    (hc : Coordinates s σ) : 16*s ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨b,m,e,μ,hμ,hl,hr,hd⟩ := hc
  have hm := multiplicity_ge_four s hF μ hμ
  nlinarith

omit [Finite F] [CharP F 2] [FiniteDimensional (ZMod 2) V] in
/-- At the minimal Hermitian square degree the constructed faithful action
has exactly four coordinates, with its original intertwining equations. -/
theorem four_coordinates_of_degree_eq
    (σ : Representation (ZMod 2) (SL(2,F) × H) V)
    (hc : Coordinates s σ) (hd : Module.finrank (ZMod 2) V = 16*s) :
    ∃ (b : F ≃+* Field s) (e : V ≃ₗ[ZMod 2] (Fin 4 → Space s))
      (μ : Representation (fixedField s) H (Fin 4 → fixedField s)),
      Function.Injective μ ∧
      (∀ g v, e (σ (g,1) v) = fun i =>
        BinarySmall.hermitian s (Matrix.SpecialLinearGroup.map b.toRingHom g) (e v i)) ∧
      (∀ h c v, e (σ (1,h) (e.symm (fun i => c i • v))) =
        fun i => μ h c i • v) := by
  obtain ⟨b,m,e,μ,hμ,hl,hr,hm⟩ := hc
  have he : m=4 := by nlinarith [NeZero.pos s]
  subst m
  exact ⟨b,e,μ,hμ,hl,hr⟩

end Representation.SL2.PairHermitian
