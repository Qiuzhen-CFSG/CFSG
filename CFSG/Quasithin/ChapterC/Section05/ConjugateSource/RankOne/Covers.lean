module

public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Coordinates
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.BlockCover
public import Theory.Representation.SL2NaturalFixedLifting
public import Theory.Representation.ProjectiveCentralCover
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Intrinsic rank-one fixed-point lifting

For an actual L₂(2ⁿ)-block, construct the covering representation on the full
U = [O₂(L),L] and its equivariant projection to the natural plane. A fixed
nonzero vector for a nonidentity SL₂-element is a displacement for an
involution. Lifting that displacement proves fixed-point lifting while
retaining the possibly nonzero central layer, including when n = 2.

For an A₃-block the actual quotient actor has order three. Maschke's theorem
makes its binary module projective. Its commutator-generated central cover
is therefore injective, proving C_U(L) = 1.

These are exactly the two intrinsic inputs consumed by NaturalIndices/Lifting.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.2.3(1),
printed p.413/PDF p.424, and C.5.6 (*), printed p.156/PDF p.167;
the A₃ argument is the coprime case of C.1.13(c), printed p.125.
-/

public section

open scoped IsMulCommutative
open Subgroup Representation
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
open IntrinsicCover

section Intrinsic

variable {L : Type*} [Group L]
private theorem intrinsic_alternating_three (h : IsAlternatingBlock L 3) : blockFixed L = ⊥ := by
  let := h.2.1.elementary
  obtain ⟨ρ, ⟨m⟩, hρ⟩ := h.2.2
  let π : Representation (ZMod 2) (alternatingGroup (Fin 3))
      (BinaryPermutation.natural (Fin 3)) :=
    (BinaryPermutation.naturalRepresentation (Fin 3)).comp
    (alternatingGroup (Fin 3)).subtype
  let p := projection h.2.1 m π hρ
  have hp := projection_isCover h.2.1 m π hρ
  let : NeZero (Nat.card (alternatingGroup (Fin 3)) : ZMod 2) := by
    constructor
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  let : Module.Projective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 3))) π.asModule :=
    Module.projective_of_isSemisimpleRing _ _
  have hi := p.injective_of_projective_of_fixed_kernel hp.1 (fun w hw => hp.2.1 hw) hp.2.2
  apply bot_unique
  intro w hw
  have hw0 : p (Additive.ofMul w) = 0 := (projection_kernel m _).mpr hw
  have he : Additive.ofMul w = 0 := hi (hw0.trans (map_zero p).symm)
  exact Additive.ofMul.injective he

private theorem intrinsic_linear (n : ℕ) (h : IsL2EvenBlock L n)
    (l : L) (v : blockU L)
    (hv : QuotientGroup.mk' (blockFixed L) (blockConjugate L l v) =
      QuotientGroup.mk' (blockFixed L) v) : blockConjugate L l v = v := by
  obtain ⟨_, hs, F, _, _, hF, _, ρ, ⟨m⟩, hρ⟩ := h
  let := hs.elementary
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let π := Representation.restrictScalars (k := ZMod 2)
    (Representation.specialLinearNatural (k := F) 2)
  let p := projection hs m π hρ
  have hp := projection_isCover hs m π hρ
  have hv' : p (action hs m (actorMap m l) (Additive.ofMul v)) = p (Additive.ofMul v) := by
    rw [action_apply]
    exact congrArg (fun q => Multiplicative.toAdd (m.moduleIso q)) hv
  have hh := Representation.SL2NaturalFixedLifting.fixed_lift_of_fixed_kernel (action hs m) p.toLinearMap.toAddMonoidHom hp.1
    (fun g w => LinearMap.congr_fun (p.isIntertwining' g) w)
    (fun w hw => hp.2.1 hw) (actorMap m l) (Additive.ofMul v) hv'
  rw [action_apply] at hh
  exact Additive.ofMul.injective hh
end Intrinsic

variable {G : Type*} [Group G]

/-- The full block module lifts every fixed vector of its natural quotient. -/
theorem linearCoverInput : LinearCoverInput (G := G) := by
  intro L n h
  exact intrinsic_linear n h

/-- The commutator module of an actual A₃-block has trivial central layer. -/
theorem alternatingThreeCoverInput : AlternatingThreeCoverInput (G := G) := by
  intro L h
  exact intrinsic_alternating_three h

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne

end
