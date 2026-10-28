module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Contracts
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Transporting Chapter K ratios through actual module identifications

An action equivalence preserves elementary actors, their fixed codimensions,
and every iterated displacement. Taking infima transports both the quadratic
and cubic ratios, separately. The final application transfers the two natural
A₇ model calculations to the literal source action when G = L.

Source: Aschbacher–Smith, K.1.1–K.1.3, pp.452–453: the module identifications
are quasiequivalences, so their group automorphism twists must also transport
the actor indexing the ratio.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.QuasisimpleSource

variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) H W}

private def reverseAction (e : ActionEquiv ρ σ) : ActionEquiv σ ρ where
  groupEquiv := e.groupEquiv.symm
  linearEquiv := e.linearEquiv.symm
  intertwines g w := by
    apply e.linearEquiv.injective
    rw [e.linearEquiv.apply_symm_apply, e.intertwines,
      e.groupEquiv.apply_symm_apply, e.linearEquiv.apply_symm_apply]

private theorem elementary_map (e : G ≃* H) {A : Subgroup G}
    (hA : IsElementaryTwo A) : IsElementaryTwo (A.map e.toMonoidHom) := by
  let : IsElementaryAbelian 2 A := hA.2
  refine ⟨?_, IsElementaryAbelian.map _⟩
  intro hb
  apply hA.1
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  simpa only [Subgroup.map_bot] using hb

/-- Both ratios use the same transported actor and its unchanged rank. -/
theorem actionRatio_map (e : ActionEquiv ρ σ) (A : Subgroup G) :
    actionRatio σ (A.map e.groupEquiv.toMonoidHom) = actionRatio ρ A := by
  unfold actionRatio
  rw [← fixedCodim_map_equivariant ρ σ _ e.linearEquiv e.intertwines,
    rank_map_injective _ e.groupEquiv.injective]

private theorem displacement_intertwines (e : ActionEquiv ρ σ) (g : G) (v : V) :
    e.linearEquiv (displacement ρ g v) =
      displacement σ (e.groupEquiv g) (e.linearEquiv v) := by
  exact (map_sub e.linearEquiv _ _).trans (congrArg (fun w => w - e.linearEquiv v)
    (e.intertwines g v))

/-- Cubicity is preserved under the group twist and the linear intertwiner. -/
theorem cubic_map (e : ActionEquiv ρ σ) {A : Subgroup G}
    (hA : IsCubic ρ A) : IsCubic σ (A.map e.groupEquiv.toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ w
  obtain ⟨v, rfl⟩ := e.linearEquiv.surjective w
  have h := congrArg e.linearEquiv (hA a ha b hb c hc v)
  simpa only [displacement_intertwines, map_zero, MulEquiv.coe_toMonoidHom] using h

private theorem quadratic_map (e : ActionEquiv ρ σ) {A : Subgroup G}
    (hA : IsQuadratic ρ A) : IsQuadratic σ (A.map e.groupEquiv.toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w
  obtain ⟨v, rfl⟩ := e.linearEquiv.surjective w
  have h := congrArg e.linearEquiv (hA a ha b hb v)
  change σ (e.groupEquiv a) (σ (e.groupEquiv b) (e.linearEquiv v) - e.linearEquiv v) =
    σ (e.groupEquiv b) (e.linearEquiv v) - e.linearEquiv v
  simpa only [map_sub, e.intertwines] using h

private theorem cubicRatio_le (e : ActionEquiv ρ σ) : cubicRatio σ ≤ cubicRatio ρ := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA, hc⟩
  exact iInf_le_of_le (A.map e.groupEquiv.toMonoidHom)
    (iInf_le_of_le ⟨elementary_map e.groupEquiv hA, cubic_map e hc⟩
      (actionRatio_map e A).le)

/-- Quasiequivalence preserves the cubic infimum, without replacing it by q. -/
theorem cubicRatio_eq (e : ActionEquiv ρ σ) : cubicRatio ρ = cubicRatio σ :=
  le_antisymm (cubicRatio_le (reverseAction e)) (cubicRatio_le e)

private theorem quadraticRatio_le (e : ActionEquiv ρ σ) :
    quadraticRatio σ ≤ quadraticRatio ρ := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA, hq⟩
  exact iInf_le_of_le (A.map e.groupEquiv.toMonoidHom)
    (iInf_le_of_le ⟨elementary_map e.groupEquiv hA, quadratic_map e hq⟩
      (actionRatio_map e A).le)

/-- The quadratic ratio is transported over its own actor family. -/
theorem quadraticRatio_eq (e : ActionEquiv ρ σ) : quadraticRatio ρ = quadraticRatio σ :=
  le_antisymm (quadraticRatio_le (reverseAction e)) (quadraticRatio_le e)

/-- Turn a full-component identification into an identification of the ambient action. -/
noncomputable def wholeAction {L : Subgroup G} (hL : L = ⊤)
    (e : ActionEquiv (ρ.comp L.subtype) σ) : ActionEquiv ρ σ := by
  subst L
  exact {
    groupEquiv := Subgroup.topEquiv.symm.trans e.groupEquiv
    linearEquiv := e.linearEquiv
    intertwines := fun g v => e.intertwines ⟨g, Subgroup.mem_top g⟩ v }

/-- The literal K.1 natural-A₇ consumer of the two independent model ratios.
The model calculations remain explicit until their owner proves them. -/
theorem sevenNatural_of_model_ratios {L : Subgroup G} (hL : L = ⊤)
    (e : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 7))
    (hq : quadraticRatio (alternatingNatural 7) = 3 / 2)
    (hc : cubicRatio (alternatingNatural 7) = 3 / 2) : Conclusion ρ L :=
  .sevenNatural hL e ((quadraticRatio_eq (wholeAction hL e)).trans hq)
    ((cubicRatio_eq (wholeAction hL e)).trans hc)

end CFSG.Quasithin.ChapterK.Alternating
