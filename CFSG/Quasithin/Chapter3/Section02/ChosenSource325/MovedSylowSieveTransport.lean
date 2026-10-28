module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderTransport
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions

/-!
# Literal constituent action equivalences for the moved-seed sieve

Restriction through an invariant overmodule preserves the full faithful
stabilizer action on a constituent. Conjugation transports this action to
an actual translated constituent. Both equivalences retain the vector maps
and induced group maps, so ratios and best offenders transport together.

The consumer is `SeedAlternativesMovedSylowStability`.
Source: Aschbacher--Smith D.3.5, printed pp.195--196.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

/-- The faithful seed action is unchanged by passage through an invariant overmodule. -/
def nestedImageActionEquiv
    (U I : Submodule (ZMod 2) W)
    (hU : (⊤ : Subgroup H) ≤ subspaceStabilizer ρ U) (hIU : I ≤ U) :
    ActionEquiv (subspaceImageRepresentation (subspaceImageRepresentation ρ U)
      (I.comap U.subtype)) (subspaceImageRepresentation ρ I) := by
  let σ := subspaceImageRepresentation ρ U
  let J := I.comap U.subtype
  let f := invariantActionHom ρ U hU
  have hs (g : H) : g ∈ subspaceStabilizer ρ I ↔ f g ∈ subspaceStabilizer σ J := by
    constructor
    · intro hg v
      change (σ (f g) v : W) ∈ I ↔ (v : W) ∈ I
      rw [invariantActionHom_apply]
      exact hg v
    · intro hg v
      constructor
      · intro hv
        have hvU : v ∈ U := (hU (mem_top g) v).1 (hIU hv)
        have he := (hg (⟨v,hvU⟩ : U)).1
        apply he
        change (σ (f g) ⟨v,hvU⟩ : W) ∈ I
        rwa [invariantActionHom_apply]
      · intro hv
        have he := (hg (⟨v,hIU hv⟩ : U)).2 hv
        change (σ (f g) ⟨v,hIU hv⟩ : W) ∈ I at he
        rwa [invariantActionHom_apply] at he
  let q : subspaceStabilizer ρ I →* subspaceStabilizer σ J :=
    { toFun := fun g => ⟨f g,(hs g).mp g.property⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun g k => Subtype.ext (f.map_mul g k) }
  have hq : Function.Surjective q := by
    intro g
    obtain ⟨x,hx⟩ := invariantActionHom_surjective ρ U hU g.val
    exact ⟨⟨x,(hs x).mpr (hx.symm ▸ g.property)⟩,Subtype.ext hx⟩
  let E : J ≃ₗ[ZMod 2] I := Submodule.comapSubtypeEquivOfLe hIU
  have hE : ∀ g v, stabilizerRepresentation ρ I g (E v) =
      E (stabilizerRepresentation σ J (q g) v) := by
    intro g v
    apply Subtype.ext
    exact (invariantActionHom_apply ρ U hU g v.val).symm
  let ψ := equivariantActionImageEquiv (stabilizerRepresentation ρ I)
    (stabilizerRepresentation σ J) q E hq hE
  refine ⟨ψ,E,?_⟩
  intro d w
  change E (d.val.val w) = E (d.val.val (E.symm (E w)))
  rw [E.symm_apply_apply]

/-- Conjugating by the actual representation operator identifies the faithful
stabilizer images on the original and translated constituents. -/
def conjugateImageActionEquiv (I : Submodule (ZMod 2) W) (a : H) :
    ActionEquiv (subspaceImageRepresentation ρ (I.map (ρ a)))
      (subspaceImageRepresentation ρ I) := by
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W (ρ.asGroupHom a)
  let f := MulAut.conj a
  have he (g : H) (v : W) : e (ρ g v) = ρ (f g) (e v) := by
    change ρ a (ρ g v) = ρ (a * g * a⁻¹) (ρ a v)
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
  have hs (g : H) : g ∈ subspaceStabilizer ρ I ↔
      f g ∈ subspaceStabilizer ρ (I.map (ρ a)) :=
    mem_subspaceStabilizer_equivariant ρ ρ f e he I g
  let q : subspaceStabilizer ρ I →* subspaceStabilizer ρ (I.map (ρ a)) :=
    { toFun := fun g => ⟨f g,(hs g).mp g.property⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun g k => Subtype.ext (f.map_mul g k) }
  have hq : Function.Surjective q := by
    intro g
    refine ⟨⟨f.symm g, (hs _).mpr ?_⟩,Subtype.ext (f.apply_symm_apply g)⟩
    simpa only [f.apply_symm_apply] using g.property
  let E : I ≃ₗ[ZMod 2] I.map (ρ a) := e.submoduleMap I
  have hE : ∀ g v, stabilizerRepresentation ρ I g (E.symm v) =
      E.symm (stabilizerRepresentation ρ (I.map (ρ a)) (q g) v) := by
    intro g v
    apply E.injective
    rw [E.apply_symm_apply]
    apply Subtype.ext
    exact (he g (E.symm v)).trans
      (congrArg (ρ (f g)) (congrArg Subtype.val (E.apply_symm_apply v)))
  let ψ := equivariantActionImageEquiv (stabilizerRepresentation ρ I)
    (stabilizerRepresentation ρ (I.map (ρ a))) q E.symm hq hE
  refine ⟨ψ,E.symm,?_⟩
  intro d w
  change E.symm (d.val.val w) = E.symm (d.val.val (E (E.symm w)))
  rw [E.apply_symm_apply]

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
