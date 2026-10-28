module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix.Bounds
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceSix
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.Stability


/-!
# Transporting the marked exterior-square actor calculation

An equivariant identification preserves quadraticity and the offender
inequality. Conjugation preserves rank and best offenders, including on the
literal quotient of two invariant subspaces. Thus an intrinsic calculation
inside the marked radical applies to the original actors without changing
the common GL₄(2) identification or substituting an unrelated six-space.

The model bounds are explicit here to separate transport from the intrinsic
proof in `MarkedSix.Calculations`. The source adapter discharges those bounds
and constructs the marked radical and the quadratic action separately.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.25,
printed p.961 (PDF p.978). The private conjugation calculation follows the
same representation identity as `SmallCovers.TerminalSource`.
-/

public section

open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix
open Alignment

private theorem quadratic_map_equivariant
    {H D U E : Type*} [Group H] [Group D]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) H U) (σ : Representation (ZMod 2) D E)
    (f : H →* D) (e : U ≃ₗ[ZMod 2] E)
    (he : ∀ g u, e (ρ g u) = σ (f g) (e u))
    (A : Subgroup H) (hq : IsQuadratic ρ A) :
    IsQuadratic σ (A.map f) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  obtain ⟨u, rfl⟩ := e.surjective v
  have hh := congrArg e (hq a ha b hb u)
  simpa only [he, map_sub] using hh

private theorem quadratic_map_conj {H U : Type*} [Group H]
    [AddCommGroup U] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) H U} {A : Subgroup H}
    (hq : IsQuadratic ρ A) (g : H) :
    IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom) := by
  have hinv (v : U) : ρ g⁻¹ (ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hginv (v : U) : ρ g (ρ g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  change ρ (g * a * g⁻¹) (ρ (g * b * g⁻¹) v - v) = ρ (g * b * g⁻¹) v - v
  have hh := congrArg (ρ g) (hq a ha b hb (ρ g⁻¹ v))
  simpa only [map_mul, Module.End.mul_apply, map_sub, hinv, hginv] using hh

private theorem rank_mono {H : Type*} [Group H] [Finite H]
    {A B : Subgroup H} (hAB : A ≤ B) : rank A ≤ rank B := by
  exact Nat.log_monotone (Nat.card_le_card_of_injective
    (Subgroup.inclusion hAB) (Subgroup.inclusion_injective hAB))

variable {H U : Type*} [Group H] [Finite H]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

/-- The two universal exterior calculations imply rank two and absence of
best offenders for an arbitrary noncyclic quadratic subgroup of the marked
radical, after an actual equivariant identification of the representation. -/
theorem actor_facts_of_radical_bounds
    (hb : ExteriorRadicalBounds)
    (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (hρ : IsExteriorSquare ρ eH)
    (P : Submodule (ZMod 2) NaturalSpace) (hP : Module.finrank (ZMod 2) P = 2)
    (V : Subgroup H) (hV : V.map eH.toMonoidHom ≤ BinaryLinear.radical P)
    (hq : IsQuadratic ρ V) (hr : 1 < rank V) :
    rank V = 2 ∧ ∀ B ≤ V, ¬ IsBestOffender ρ B := by
  obtain ⟨e, he⟩ := hρ
  have he' : ∀ g u, e (ρ g u) = modelAction (eH g) (e u) := he
  have hq' := quadratic_map_equivariant ρ modelAction eH.toMonoidHom e he' V hq
  have hupper := hb.quadratic_rank P hP _ hV hq'
  rw [rank_map_injective eH.toMonoidHom eH.injective] at hupper
  have hrank : rank V = 2 := by omega
  refine ⟨hrank, ?_⟩
  intro B hBV hB
  have hB' := (hB.isOffender ρ).map_equivariant ρ modelAction
    eH.toMonoidHom eH.injective e he'
  have hBrank : rank (B.map eH.toMonoidHom) ≤ 2 := by
    rw [rank_map_injective eH.toMonoidHom eH.injective]
    exact (rank_mono hBV).trans hupper
  exact (not_le_of_gt (hb.small_fixedCodim P hP _
    ((Subgroup.map_mono hBV).trans hV) hB'.1 hBrank)) hB'.2

/-- Apply the exterior calculation at the actual conjugate of V and
transport both rank and offender absence back to the original actor.
Quadraticity descends from the whole module to the literal section first. -/
theorem sixActorFacts_of_conjugate_radical_bounds
    (hb : ExteriorRadicalBounds)
    (ρ : Representation (ZMod 2) H U) (X Y : Subrepresentation ρ)
    (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (hXY : IsExteriorSquare (sectionRepresentation ρ X Y) eH)
    (P : Submodule (ZMod 2) NaturalSpace) (hP : Module.finrank (ZMod 2) P = 2)
    (A V : Subgroup H) (hAV : A ≤ V) (g : H)
    (hV : (V.map (MulAut.conj g).toMonoidHom).map eH.toMonoidHom ≤ BinaryLinear.radical P)
    (hq : IsQuadratic ρ V) (hr : 1 < rank V) : SixActorFacts ρ X Y A V := by
  have hq' := quadratic_map_conj (quadratic_section ρ X Y hq) g
  obtain ⟨hrank, hno⟩ := actor_facts_of_radical_bounds hb
    (sectionRepresentation ρ X Y) eH hXY P hP
    (V.map (MulAut.conj g).toMonoidHom) hV hq' (by rwa [rank_map_conj])
  refine ⟨(rank_map_conj V g).symm.trans hrank, ?_⟩
  intro B hBA hB
  exact hno (B.map (MulAut.conj g).toMonoidHom)
    (Subgroup.map_mono (hBA.trans hAV)) (hB.map_conj _ g)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix
