module

public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Completion
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Comparing the faithful graph action with the chosen ambient image

An injective ambient homomorphism carrying the graph seed onto V identifies
the two underlying elementary abelian groups. Conjugation in the first vertex
maps to the literal action image of M on V, with kernel exactly the seed
centralizer. Hence the faithful F.7 quotient embeds equivariantly into that
image, and every FF offender transfers with its rank and fixed codimension.
The chosen non-FF action therefore supplies the hypothesis of F.7.11(7).

The first vertex may be the smaller normalizer N_M(C_T(V)); no equality with M
is required. Its full action image also equals that of M by 15.1.9(6), but the
injection proved here suffices for the non-FF implication.

Source: Aschbacher--Smith, 15.1.9(6), printed pp.1088--1089;
F.7.6 and F.7.11(7), printed pp.312--314.
-/

public section

open scoped IsMulCommutative
open Subgroup
open Representation.BinaryOffender (IsFFModule)
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
open CFSG.Quasithin.ChapterF.Section07.Track
open CFSG.Quasithin.ChapterF.Section07.CriticalPairs
namespace CFSG.Quasithin.Chapter15.Section02.ChosenOppositeTrack
variable {G K : Type*} [Group G] [Group K] {F : Bool → Subgroup K}

/-- Non-FF for the original ambient conjugation image excludes FF for the
literal centralizer quotient used by the F.7 parity theorem. -/
theorem not_ff_of_ambient_image (D : SourceSetup F)
    (f : K →* G) (hf : Function.Injective f)
    (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (hM : (F false).map f ≤ M) (hV : D.seed.map f = V)
    (hnot : ¬ IsFFModule (imageRepresentation M V hn)) :
    ¬ SourceAction.IsFF D := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := D.reduced.elementary
  let := D.reduced.normal
  let j : F false →* M := {
    toFun := fun x => ⟨f x, hM (mem_map_of_mem f x.property)⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' := fun x y => Subtype.ext (map_mul f (x : K) (y : K)) }
  let a : F false →* internalActionImage M V hn :=
    (actionHom M V hn).rangeRestrict.comp j
  let e : D.V ≃* V :=
    (D.V.equivMapOfInjective (f.comp (F false).subtype)
      (hf.comp (F false).subtype_injective)).trans
      (MulEquiv.subgroupCongr (by rw [← map_map]; exact hV))
  let E : Additive D.V ≃ₗ[ZMod 2] Additive V :=
    e.toAdditive.toLinearEquiv (fun c x => ZMod.map_smul e.toAdditive.toAddMonoidHom c x)
  have hE (g : F false) (x : Additive D.V) :
      E (SourceAction.conjugationRepresentation D g x) =
        imageRepresentation M V hn (a g) (E x) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change f ((g : K) * ((x.toMul : F false) : K) * (g : K)⁻¹) =
      f g * f (x.toMul : F false) * (f g)⁻¹
    simp only [map_mul, map_inv]
  have hk : a.ker = centralizer (D.V : Set (F false)) := by
    rw [← SourceAction.conjugationRepresentation_ker D]
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hg
      apply LinearMap.ext
      intro x
      apply E.injective
      rw [hE, hg, map_one]
      rfl
    · intro hg
      apply imageRepresentation_injective M V hn
      rw [map_one]
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := E.surjective x
      rw [← hE, hg]
      rfl
  let q := QuotientGroup.lift (centralizer (D.V : Set (F false))) a hk.ge
  have hq : Function.Injective q :=
    (QuotientGroup.injective_lift_iff _ _ _).mpr hk.symm
  have hEq (g : (F false) ⧸ centralizer (D.V : Set (F false))) (x : Additive D.V) :
      E (SourceAction.faithfulRepresentation D g x) =
        imageRepresentation M V hn (q g) (E x) := by
    induction g using QuotientGroup.induction_on with
    | H g => exact hE g x
  intro hff
  exact hnot (IsFFModule.map_equivariant
    (SourceAction.faithfulRepresentation D)
    (imageRepresentation M V hn) q hq E hEq hff)

end CFSG.Quasithin.Chapter15.Section02.ChosenOppositeTrack
