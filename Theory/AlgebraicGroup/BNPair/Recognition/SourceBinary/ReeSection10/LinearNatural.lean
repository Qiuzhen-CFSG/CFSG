module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.LinearIrreducible
public import Theory.Representation.SL2.EvenSquareExchange
public import Theory.Representation.SL2.BinaryNaturalTripleRecognition

/-!
# Natural linear modules in minimum odd field degree

In binary dimension 2n with n odd, the actual Schur field has degree n.
Indeed, the highest-weight period writes n=s t and the dimension as s b^t;
t is odd, and equality in the degree bound forces t=1. Over the Schur
field the representation therefore has dimension two. The proved absolute
SL₂ classification and finite-field identification descend its natural
intertwiner by Noether--Deuring. Restriction to F₂ retains the original
matrix actor. This includes n=1, using LinearIrreducible's separate cubic
argument; no positive-parameter simplicity argument is applied at q=2.

V1Natural applies this result to the literal Section 10 quotient. Source:
Fong--Seitz II, pp.222--223 before (10.6), and the defining-characteristic
SL₂ classification used in I §4. No natural action is an input premise.
-/

public noncomputable section
open scoped MatrixGroups MonoidAlgebra TensorProduct
open Representation Representation.SL2
namespace Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Odd defining degree excludes repeated Frobenius blocks at the minimum degree. -/
theorem linear_minimal_schur_degree
    (ρ : Representation (ZMod 2) SL(2,K) V) [ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) (n : ℕ) (hn : Odd n) (hK : Nat.card K = 2^n)
    (hd : Module.finrank (ZMod 2) V = 2*n) :
    Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule) = n := by
  let s := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)
  obtain ⟨hs,a,ha,hsdiv,hperiod,hdegree⟩ :=
    Representation.SL2.Unsigned.exists_primeField_highestWeight_parameters 2 ρ hnt n hK
  obtain ⟨t,hnt⟩ := hsdiv
  change n = s*t at hnt
  have htodd : Odd t := by
    rw [hnt,Nat.odd_mul] at hn
    exact hn.2
  have ht : 0<t := htodd.pos
  obtain ⟨b,hb,hprod,_⟩ := Nat.exists_digit_product_pow_of_period 2 s t a.val
    (by decide) hs ht ha (by rw [←hnt,←hK]; exact a.isLt)
      (by rw [←hnt,←hK]; exact hperiod)
  have heq : s*b^t = 2*(s*t) := by
    rw [hd,hnt,hprod] at hdegree
    exact hdegree.symm
  have htone := (orbit_dimension_minimal_parameters hs htodd hb heq).1
  simpa only [htone,mul_one] using hnt.symm

private theorem irreducible_of_equiv {F G U W : Type*} [Field F] [Monoid G]
    [AddCommGroup U] [Module F U] [AddCommGroup W] [Module F W]
    {ρ : Representation F G U} {σ : Representation F G W}
    (e : ρ.Equiv σ) (hσ : IsIrreducible σ) : IsIrreducible ρ := by
  let f := IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  let ef := LinearEquiv.ofBijective f (show Function.Bijective f from e.toLinearEquiv.bijective)
  rw [irreducible_iff_isSimpleModule_asModule]
  exact ef.isSimpleModule_iff.mpr ((irreducible_iff_isSimpleModule_asModule σ).mp hσ)

/-- The actual faithful minimum-degree module is natural for every odd
field degree, including degree one. -/
theorem linear_minimal_natural
    (ρ : Representation (ZMod 2) SL(2,K) V) (hf : Function.Injective ρ)
    (n : ℕ) (hn : Odd n) (hK : Nat.card K = 2^n)
    (hd : Module.finrank (ZMod 2) V = 2*n) :
    BinarySmall.IsNatural ρ := by
  let : ρ.IsIrreducible := linear_minimal_irreducible ρ hf n hn.pos hK hd
  have hnt : ∃ g, ρ g ≠ 1 := by
    let g := Theory.PSL2.SemilinearCoverage.uni (1 : K)
    have hg : g ≠ 1 := by
      intro he
      have hh := congrArg (fun a : SL(2,K) => a.val 0 1) he
      simp [g,Theory.PSL2.SemilinearCoverage.uni] at hh
    exact ⟨g,fun he => hg (hf (he.trans ρ.map_one.symm))⟩
  have hs := linear_minimal_schur_degree ρ hnt n hn hK hd
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  let F := AlgebraicClosure E
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap E F).injective 2
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) ρ.asModule)
  let : Module.Finite E ρ.asModule := Module.Finite.of_finite
  let : IsAbsolutelyIrreducible ρ.endFieldRep := endFieldRep_isAbsolutelyIrreducible ρ
  let : IsIrreducible (extendScalars F ρ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep F
  have hdE : Module.finrank E ρ.asModule = 2 := by
    have he := Module.finrank_mul_finrank (ZMod 2) E ρ.asModule
    rw [hs,ρ.asModuleEquiv.finrank_eq,hd] at he
    nlinarith [hn.pos]
  have hdF : Module.finrank F (F ⊗[E] ρ.asModule) = 2 := by
    rw [Module.finrank_baseChange,hdE]
  let b : (F ⊗[E] ρ.asModule) ≃ₗ[F] (Fin 2 → F) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hdF)
  let σ := extendScalars F ρ.endFieldRep
  let τ : Representation F SL(2,K) (Fin 2 → F) := b.conjRingEquiv.toMonoidHom.comp σ
  let B : σ.Equiv τ := Representation.Equiv.mk b (fun g => by
    apply LinearMap.ext
    intro v
    change b (σ g v) = b (σ g (b.symm (b v)))
    rw [b.symm_apply_apply])
  let : τ.IsIrreducible := irreducible_of_equiv B.symm inferInstance
  let e : K →+* F := (IsAlgClosed.lift (R := ZMod 2) (S := K) (M := F)).toRingHom
  obtain ⟨i,_,⟨C⟩⟩ := EvenSquare.absolute_degree_two_natural τ n hK e
  let e' := (iterateFrobenius F 2 i).comp e
  have hc : Nat.card K = Nat.card E := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E),Nat.card_zmod,hs,hK]
  obtain ⟨c,hc⟩ := BinarySmall.exists_fieldEquiv_comp_eq_of_card_eq e' (algebraMap E F) hc
  have q := BinarySmall.embeddedNaturalBaseChange (F := F) c.toRingHom
  rw [hc] at q
  obtain ⟨d⟩ := repEquiv_of_extendScalars ρ.endFieldRep (BinarySmall.embeddedNatural c.toRingHom)
    ⟨RepEquiv.ofRepresentationEquiv ((B.trans C).trans q.symm)⟩
  let ed : (restrictScalars (k := ZMod 2) ρ.endFieldRep).Equiv
      (restrictScalars (k := ZMod 2) (BinarySmall.embeddedNatural c.toRingHom)) :=
    Representation.Equiv.mk (d.toLinearEquiv.restrictScalars (ZMod 2)) (fun g => by
      apply LinearMap.ext
      intro v
      exact d.isIntertwining g v)
  let start : ρ.Equiv (restrictScalars (k := ZMod 2) ρ.endFieldRep) :=
    Representation.Equiv.mk ρ.asModuleEquiv.symm (fun g => by
      apply LinearMap.ext
      intro v
      change ρ.asModuleEquiv.symm (ρ g v) =
        ρ.asModuleEquiv.symm (ρ g (ρ.asModuleEquiv (ρ.asModuleEquiv.symm v)))
      rw [LinearEquiv.apply_symm_apply])
  exact ⟨start.trans (ed.trans (BinarySmall.naturalFieldEquiv c).symm)⟩
end Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
