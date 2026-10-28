module

public import Theory.Representation.SL3FourNaturalDual.Markings
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Transporting quadratic actors in the SL₃(4) component

The subgroup `modelActor` is the original actor restricted to the specified
component and then mapped through the given matrix-group equivalence. When
the actor lies in that component, this construction preserves its rank,
fixed codimension, elementary structure and quadratic action. Actual linear
markings, including their equivariance equations, transfer back to the
ambient representation.

These results implement the transport step for the matrix classification in
Aschbacher--Smith, proof of 13.8.20, printed p.955 (1 March 2004 manuscript).
They do not assert component containment or classify arbitrary actors.
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors
open BinaryOffender

variable {J U : Type*} [Group J] [AddCommGroup U] [Module (ZMod 2) U]

/-- The specified copy of SL₃(4) in the ambient group. -/
def componentEmbedding (K : Subgroup J) (eK : K ≃* SL) : SL →* J :=
  K.subtype.comp eK.symm.toMonoidHom

lemma componentEmbedding_injective (K : Subgroup J) (eK : K ≃* SL) :
    Function.Injective (componentEmbedding K eK) :=
  K.subtype_injective.comp eK.symm.injective

/-- The actor inside the concrete matrix group, retaining the original subgroup. -/
def modelActor (K : Subgroup J) (eK : K ≃* SL) (A : Subgroup J) : Subgroup SL :=
  (A.subgroupOf K).map eK.toMonoidHom

lemma modelActor_map (K : Subgroup J) (eK : K ≃* SL) (A : Subgroup J)
    (hAK : A ≤ K) : (modelActor K eK A).map (componentEmbedding K eK) = A := by
  rw [modelActor, Subgroup.map_map]
  have hcomp : (componentEmbedding K eK).comp eK.toMonoidHom = K.subtype := by
    ext k
    exact congrArg Subtype.val (eK.symm_apply_apply k)
  rw [hcomp, Subgroup.map_subgroupOf_eq_of_le hAK]

lemma modelActor_rank (K : Subgroup J) (eK : K ≃* SL) (A : Subgroup J)
    (hAK : A ≤ K) : rank (modelActor K eK A) = rank A := by
  calc
    rank (modelActor K eK A) =
        rank ((modelActor K eK A).map (componentEmbedding K eK)) :=
      (rank_map_injective _ (componentEmbedding_injective K eK) _).symm
    _ = rank A := by rw [modelActor_map K eK A hAK]

lemma modelActor_elementary (K : Subgroup J) (eK : K ≃* SL) (A : Subgroup J)
    (hAK : A ≤ K) (hA : IsElementaryTwo A) : IsElementaryTwo (modelActor K eK A) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf hAK
  refine ⟨?_, IsElementaryAbelian.map eK.toMonoidHom⟩
  intro hb
  apply hA.1
  rw [← modelActor_map K eK A hAK, hb, Subgroup.map_bot]

lemma component_equivariant (ρ : Representation (ZMod 2) J U)
    (K : Subgroup J) (eK : K ≃* SL) (E : U ≃ₗ[ZMod 2] V)
    (hE : ∀ (k : K) u, E (ρ k u) = representation (eK k) (E u)) :
    ∀ g u, E (ρ (componentEmbedding K eK g) u) = representation g (E u) := by
  intro g u
  change E (ρ (eK.symm g : J) u) = representation g (E u)
  simpa only [MulEquiv.apply_symm_apply] using hE (eK.symm g) u

lemma modelActor_fixedCodim (ρ : Representation (ZMod 2) J U)
    (K : Subgroup J) (eK : K ≃* SL) (E : U ≃ₗ[ZMod 2] V)
    (hE : ∀ (k : K) u, E (ρ k u) = representation (eK k) (E u))
    (A : Subgroup J) (hAK : A ≤ K) :
    fixedCodim representation (modelActor K eK A) = fixedCodim ρ A := by
  have he : ∀ g v, E.symm (representation g v) =
      ρ (componentEmbedding K eK g) (E.symm v) := by
    intro g v
    apply E.injective
    simp only [E.apply_symm_apply, component_equivariant ρ K eK E hE]
  have h := fixedCodim_map_equivariant representation ρ _ E.symm he (modelActor K eK A)
  simpa only [modelActor_map K eK A hAK] using h

lemma modelActor_quadratic (ρ : Representation (ZMod 2) J U)
    (K : Subgroup J) (eK : K ≃* SL) (E : U ≃ₗ[ZMod 2] V)
    (hE : ∀ (k : K) u, E (ρ k u) = representation (eK k) (E u))
    (A : Subgroup J) (hA : IsQuadratic ρ A) :
    IsQuadratic representation (modelActor K eK A) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  obtain ⟨u, rfl⟩ := E.surjective v
  have he := congrArg E (hA a ha b hb u)
  simpa only [MulEquiv.coe_toMonoidHom, hE, map_sub] using he

/-- Transport all marking data, including actual equivariance and exact
fixed codimension, from a faithful subgroup embedding. -/
theorem criticalShapes_map (ρ : Representation (ZMod 2) J U)
    (f : SL →* J) (hf : Function.Injective f) (E : U ≃ₗ[ZMod 2] V)
    (hE : ∀ g u, E (ρ (f g) u) = representation g (E u))
    (B : Subgroup SL) (hB : CriticalShapes representation B) :
    CriticalShapes ρ (B.map f) := by
  have hr : rank (B.map f) = rank B := rank_map_injective f hf B
  have hc : fixedCodim representation B = fixedCodim ρ (B.map f) := by
    apply fixedCodim_map_equivariant representation ρ f E.symm
    intro g v
    apply E.injective
    simp only [E.apply_symm_apply, hE]
  let lift (m : LinearMarking representation) : LinearMarking ρ :=
    { actor := f.comp m.actor
      coordinates := E.trans m.coordinates
      equivariant := by
        intro g u
        change m.coordinates (E (ρ (f (m.actor g)) u)) = _
        rw [hE, m.equivariant]
        rfl }
  rcases hB with ⟨hrB, hcB, m, hm⟩ | ⟨hrB, hrB', hcB, hm | hm⟩
  · exact Or.inl ⟨hr.trans hrB, hc.symm.trans hcB, lift m,
      fun a => Subgroup.mem_map_of_mem f (hm a)⟩
  · obtain ⟨m, hm, hs⟩ := hm
    exact Or.inr ⟨by omega, by omega, hc.symm.trans hcB,
      Or.inl ⟨lift m, fun a => Subgroup.mem_map_of_mem f (hm a),
        Subgroup.mem_map_of_mem f hs⟩⟩
  · obtain ⟨m⟩ := hm
    refine Or.inr ⟨by omega, by omega, hc.symm.trans hcB, Or.inr ⟨{
      actor := f m.actor
      mem := Subgroup.mem_map_of_mem f m.mem
      coordinates := E.trans m.coordinates
      equivariant := ?_ }⟩⟩
    intro u
    change m.coordinates (E (ρ (f m.actor) u)) = _
    rw [hE, m.equivariant]
    rfl

/-- Once the actor lies in the specified component, its concrete matrix
classification transfers to the original ambient action. -/
theorem criticalShapes_of_modelActor (ρ : Representation (ZMod 2) J U)
    (K : Subgroup J) (eK : K ≃* SL) (E : U ≃ₗ[ZMod 2] V)
    (hE : ∀ (k : K) u, E (ρ k u) = representation (eK k) (E u))
    (A : Subgroup J) (hAK : A ≤ K)
    (hA : CriticalShapes representation (modelActor K eK A)) : CriticalShapes ρ A := by
  have h := criticalShapes_map ρ _ (componentEmbedding_injective K eK) E
    (component_equivariant ρ K eK E hE) _ hA
  simpa only [modelActor_map K eK A hAK] using h

end Representation.SL3FourNaturalDual.QuadraticActors
