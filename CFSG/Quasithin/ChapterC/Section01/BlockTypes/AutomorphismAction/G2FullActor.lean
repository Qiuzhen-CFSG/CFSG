module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup
public import Theory.Representation.FirstCohomologyG2Natural.Commutant


/-!
# Full actors of intrinsic binary G₂ blocks

The actual automorphism group of G₂(2)′ is the full split group G₂(2).
Transporting a block automorphism through this identification gives its
full actor. The induced module automorphism has the same natural action:
after canceling the full actor, the additive scalar commutant is F₂ and
invertibility forces its scalar to be one. All maps retain the original
quotient U(L)/C_U(L), including its central kernel before passage to the quotient.

Source: Aschbacher–Smith B.4.6 and 3.3.28, printed pp.88–90 and 601.
-/

public noncomputable section

open Subgroup
open Atlas.G2.Natural
namespace CFSG.Quasithin.ChapterC
namespace BlockModuleModel
open Atlas.G2.LieAutomorphismExtensions
local notation "Actor" => commutator (Atlas.G2.Model (ZMod 2))
local notation "Vector" => Atlas.G2.Natural.Space (ZMod 2)
variable {L : Type*} [Group L]
/-- The full binary actor induced by an automorphism of the intrinsic block. -/
@[expose] def g2FullActor (m : BlockModuleModel L g2TwoNaturalAction) :
    MulAut L →* Atlas.G2.Model (ZMod 2) :=
  binaryAutomorphismEquiv.symm.toMonoidHom.comp m.quotientAction
@[simp] theorem g2FullActor_conjugation (m : BlockModuleModel L g2TwoNaturalAction)
    (a : MulAut L) :
    binaryAutomorphismEquiv (g2FullActor m a) = m.quotientAction a := by
  simp [g2FullActor]

/-- The original module coordinates intertwine every block automorphism
with its full actor, without a second choice of natural-module marking. -/
theorem g2_moduleAction_eq_natural (m : BlockModuleModel L g2TwoNaturalAction)
    (a : MulAut L) (v : Vector) :
    (m.moduleAction a (Multiplicative.ofAdd v)).toAdd =
      Atlas.G2.Natural.action (ZMod 2) (m.g2FullActor a) v := by
  let g : Atlas.G2.Model (ZMod 2) := g2FullActor m a
  let f₀ : Vector →+ Vector := MonoidHom.toAdditiveLeft (m.moduleAction a).toMonoidHom
  have hf₀ (h : Actor) (v : Vector) :
      f₀ ((Atlas.G2.Natural.derivedAction (ZMod 2)) h v) =
        (Atlas.G2.Natural.derivedAction (ZMod 2)) (m.quotientAction a h) (f₀ v) := by
    have harg : Multiplicative.ofAdd ((Atlas.G2.Natural.derivedAction (ZMod 2)) h v) =
        g2TwoNaturalAction h (Multiplicative.ofAdd v) := by
      apply Multiplicative.toAdd.injective
      simp [g2TwoNaturalAction_apply]
    change (m.moduleAction a (Multiplicative.ofAdd
      ((Atlas.G2.Natural.derivedAction (ZMod 2)) h v))).toAdd = _
    rw [harg]
    have hh := congrArg Multiplicative.toAdd
      (m.actions_compatible a h (Multiplicative.ofAdd v))
    rw [g2TwoNaturalAction_apply] at hh
    exact hh
  let f : Vector →+ Vector :=
    (Atlas.G2.Natural.action (ZMod 2) g⁻¹).toAddMonoidHom.comp f₀
  have hf (h : Actor) (v : Vector) :
      f ((Atlas.G2.Natural.derivedAction (ZMod 2)) h v) =
        (Atlas.G2.Natural.derivedAction (ZMod 2)) h (f v) := by
    change Atlas.G2.Natural.action (ZMod 2) g⁻¹
      (f₀ ((Atlas.G2.Natural.derivedAction (ZMod 2)) h v)) = _
    rw [hf₀]
    have heq : m.quotientAction a h =
        binaryConjugation g h := by
      rw [← g2FullActor_conjugation m a]
      rfl
    rw [heq]
    change Atlas.G2.Natural.action (ZMod 2) g⁻¹
      ((Atlas.G2.Natural.derivedAction (ZMod 2))
        (⟨g * (h : Atlas.G2.Model (ZMod 2)) * g⁻¹, _⟩ : Actor)
        (f₀ v)) = _
    have he : g⁻¹ * (g * (h : Atlas.G2.Model (ZMod 2)) * g⁻¹) =
        (h : Atlas.G2.Model (ZMod 2)) * g⁻¹ := by group
    calc
      _ = Atlas.G2.Natural.action (ZMod 2)
          (g⁻¹ * (g * (h : Atlas.G2.Model (ZMod 2)) * g⁻¹)) (f₀ v) := by
        rw [map_mul]
        rfl
      _ = Atlas.G2.Natural.action (ZMod 2)
          ((h : Atlas.G2.Model (ZMod 2)) * g⁻¹) (f₀ v) := by rw [he]
      _ = (Atlas.G2.Natural.derivedAction (ZMod 2)) h
          (Atlas.G2.Natural.action (ZMod 2) g⁻¹ (f₀ v)) := by
        rw [map_mul]
        rfl
  obtain ⟨c, hc⟩ := Atlas.G2.Natural.exists_scalar_of_additive_commutes_derived f hf
  have ht (v : Vector) : f₀ v = c • Atlas.G2.Natural.action (ZMod 2) g v := by
    have he := congrArg (Atlas.G2.Natural.action (ZMod 2) g) (hc v)
    change Atlas.G2.Natural.action (ZMod 2) g
      (Atlas.G2.Natural.action (ZMod 2) g⁻¹ (f₀ v)) = _ at he
    have hcancel (w : Vector) : Atlas.G2.Natural.action (ZMod 2) g
        (Atlas.G2.Natural.action (ZMod 2) g⁻¹ w) = w := by
      change (Atlas.G2.Natural.action (ZMod 2) g *
        Atlas.G2.Natural.action (ZMod 2) g⁻¹) w = w
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    simpa only [hcancel, map_smul] using he
  have hfi : Function.Injective f₀ := by
    intro x y hxy
    exact (AddEquiv.toMultiplicative.symm (m.moduleAction a)).injective hxy
  have hc0 : c ≠ 0 := by
    intro hz
    let : Nontrivial Vector := Module.nontrivial_of_finrank_pos
      (show 0 < Module.finrank (ZMod 2) Vector by
        rw [Atlas.G2.Natural.finrank_space]
        decide)
    obtain ⟨v, hv⟩ := exists_ne (0 : Vector)
    have hh : f₀ v = f₀ 0 := by
      simp only [ht, hz, zero_smul]
    exact hv (hfi hh)
  have hc1 : c = 1 := by
    fin_cases c
    · exact (hc0 rfl).elim
    · rfl
  change f₀ v = _
  simpa only [hc1, one_smul] using ht v
/-- Inner block automorphisms restrict to the original derived quotient actor. -/
@[simp] theorem g2FullActor_inner (m : BlockModuleModel L g2TwoNaturalAction) (l : L) :
    m.g2FullActor (MulAut.conj l) = (m.actor l).val := by
  apply binaryAutomorphismEquiv.injective
  rw [g2FullActor_conjugation, binaryAutomorphismEquiv_apply, binaryConjugation_inner]
  apply MulEquiv.ext
  intro x
  obtain ⟨k, rfl⟩ := m.actor_surjective x
  rw [m.quotientAction_actor]
  change m.actor (l * k * l⁻¹) = m.actor l * m.actor k * (m.actor l)⁻¹
  simp only [map_mul, map_inv]

/-- On the actual intrinsic module quotient, full actors give literal
conjugation through the originally supplied `moduleIso`. -/
theorem g2_moduleIso_characteristic (m : BlockModuleModel L g2TwoNaturalAction)
    (a : MulAut L) (u : blockU L) :
    (m.moduleIso (QuotientGroup.mk' (blockFixed L)
      (MulAut.characteristic (blockU L) a u))).toAdd =
        Atlas.G2.Natural.action (ZMod 2) (m.g2FullActor a)
          (m.moduleIso (QuotientGroup.mk' (blockFixed L) u)).toAdd := by
  rw [← m.moduleAction_mk]
  exact m.g2_moduleAction_eq_natural a _

end BlockModuleModel
end CFSG.Quasithin.ChapterC
