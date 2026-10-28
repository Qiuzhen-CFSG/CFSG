module
public import Theory.Representation.InvertedCubicTensor.MovedPairs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.SectionModel
public import Theory.Representation.BinaryOffender.Homogeneous.Embedding
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.CubicOrbit.Quotients

/-!
# Realized constituents under multiplicity embeddings

An injective equivariant inclusion carries the actual constituent actor and
its component marking into the ambient group. Its induced central quotient
map intertwines the entire actor. For a two-conjugate orbit, the central
quotient comparison then gives the exact multiplicity coordinates consumed
by the natural-layer and marked-five reconstruction theorems.
These constructions are applied to the original FF multiplicity action in
OriginalSource.LinearTwoComplete. No Sylow-invariance or whole-space equality
is asserted. Source: Aschbacher–Smith, F.9.18 and 13.8.20(a), pp.325–326,954.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction
variable {D G V W E N : Type*} [Group D] [Group G] [Group E]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup N] [Module (ZMod 2) N]
  (ρ : Representation (ZMod 2) D V) (τ : Representation (ZMod 2) G W)
  (f : D →* G) (hf : Function.Injective f)
  (j : V →ₗ[ZMod 2] W) (hj : Function.Injective j)
  (he : ∀ g v, j (ρ g v) = τ (f g) (j v))

/-- The quotient map induced by the actual embedding of a constituent,
with its acting component replaced by its literal subgroup image. -/
def embeddedQuotient (K : Subgroup D) (I : Submodule (ZMod 2) V) :
    centralQuotient ρ K I ≃ₗ[ZMod 2] centralQuotient τ (K.map f) (I.map j) :=
  Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective j hj I) (by
    ext v
    constructor
    · rintro ⟨v,hv,rfl⟩
      rintro ⟨_,g,hg,rfl⟩
      change τ (f g) (j v) = j v
      rw [←he]
      exact congrArg j (hv ⟨g,hg⟩)
    · intro hv
      obtain ⟨v,rfl⟩ := (Submodule.equivMapOfInjective j hj I).surjective v
      refine ⟨v,?_,rfl⟩
      intro k
      apply hj
      change j (ρ k v) = j v
      rw [he]
      exact hv ⟨f k,Subgroup.mem_map_of_mem f k.property⟩)

/-- The induced quotient map sends a represented vector to its actual image. -/
theorem embeddedQuotient_mk (K : Subgroup D) (I : Submodule (ZMod 2) V) (v : I) :
    embeddedQuotient ρ τ f j hj he K I (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (⟨j v,Submodule.mem_map_of_mem v.property⟩ : I.map j) := by rfl

/-- Preserve a realized constituent, its full actor, component marking and
literal central quotient under injective equivariant embeddings. -/
def ConstituentRealization.mapEmbedding
    {K : Subgroup D} {σ : Representation (ZMod 2) E N} {L : Subgroup E}
    (r : ConstituentRealization ρ K σ L) :
    ConstituentRealization τ (K.map f) σ L := by
  let a := r.actor.equivMapOfInjective f hf
  let b := K.equivMapOfInjective f hf
  let q := embeddedQuotient ρ τ f j hj he K r.space
  refine {
    actor := r.actor.map f
    contains := Subgroup.map_mono r.contains
    space := r.space.map j
    stable := map_le_subspaceStabilizer_embedding ρ τ f j he r.stable
    irrPlus := r.irrPlus.map_equivariant_embedding ρ τ f j he hj
    groupMap := r.groupMap.comp a.symm.toMonoidHom
    surjective := r.surjective.comp a.symm.surjective
    component := b.symm.trans r.component
    component_map := ?_
    linearEquiv := q.symm.trans r.linearEquiv
    intertwines := ?_ }
  · intro k
    obtain ⟨k,rfl⟩ := b.surjective k
    change r.groupMap (a.symm (a ⟨k,r.contains k.property⟩)) =
      (r.component (b.symm (b k)) : E)
    rw [a.symm_apply_apply,b.symm_apply_apply,r.component_map]
  · intro g v
    obtain ⟨g,rfl⟩ := a.surjective g
    obtain ⟨v,rfl⟩ := (Submodule.equivMapOfInjective j hj r.space).surjective v
    change r.linearEquiv (q.symm (Submodule.Quotient.mk _)) =
      σ (r.groupMap (a.symm (a g)))
        (r.linearEquiv (q.symm (Submodule.Quotient.mk _)))
    have hvq : q.symm (Submodule.Quotient.mk
        (⟨j v,Submodule.mem_map_of_mem v.property⟩ : r.space.map j)) =
        Submodule.Quotient.mk v := by
      apply q.injective
      rw [q.apply_symm_apply]
      exact (embeddedQuotient_mk ρ τ f j hj he K r.space v).symm
    have haq : q.symm (Submodule.Quotient.mk
        (⟨τ (f g) (j v),
          (map_le_subspaceStabilizer_embedding ρ τ f j he r.stable
            (Subgroup.mem_map_of_mem f g.property) _).mpr
            (Submodule.mem_map_of_mem v.property)⟩ : r.space.map j)) =
        Submodule.Quotient.mk (⟨ρ g v,(r.stable g.property v).mpr v.property⟩ : r.space) := by
      apply q.injective
      rw [q.apply_symm_apply]
      change _ = embeddedQuotient ρ τ f j hj he K r.space _
      rw [embeddedQuotient_mk]
      congr 1
      apply Subtype.ext
      exact (he g v).symm
    calc
      _ = r.linearEquiv (Submodule.Quotient.mk
          (⟨ρ g v,(r.stable g.property v).mpr v.property⟩ : r.space)) :=
        congrArg r.linearEquiv haq
      _ = σ (r.groupMap g) (r.linearEquiv (Submodule.Quotient.mk v)) := r.intertwines g v
      _ = _ := by
        rw [a.symm_apply_apply]
        exact congrArg (σ (r.groupMap g)) (congrArg r.linearEquiv hvq).symm
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction
variable {D G V W E N : Type*} [Group D] [Group G] [Group E]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup N] [Module (ZMod 2) N]
  (ρ : Representation (ZMod 2) D V) (τ : Representation (ZMod 2) G W)
  (f : D →* G) (hf : Function.Injective f)
  (j : V →ₗ[ZMod 2] W) (hj : Function.Injective j)
  (he : ∀ g v, j (ρ g v) = τ (f g) (j v))

include hf hj he in
theorem ConstituentRealization.exists_mapEmbedding
    {K : Subgroup D} {σ : Representation (ZMod 2) E N} {L : Subgroup E}
    (r : ConstituentRealization ρ K σ L) (K' : Subgroup G) (hK' : K.map f = K') :
    ∃ r' : ConstituentRealization τ K' σ L, r'.space = r.space.map j := by
  subst K'
  exact ⟨r.mapEmbedding ρ τ f hf j hj he,rfl⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal]
  (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))

private def sectionEquiv (W : Subrepresentation ρ) :
    SectionSpace ρ (SourceOrbit.selectedOrbitLower ρ K) W ≃ₗ[ZMod 2]
      SectionSpace ρ (LinearTwo.centralBottom ρ K W) W :=
  Submodule.quotEquivOfEq _ _ (LinearTwo.centralBottom_comap ρ K W).symm

private theorem sectionEquiv_equivariant (W : Subrepresentation ρ) (g : D)
    (v : SectionSpace ρ (SourceOrbit.selectedOrbitLower ρ K) W) :
    sectionEquiv ρ K W (sectionRepresentation ρ (SourceOrbit.selectedOrbitLower ρ K) W g v) =
      sectionRepresentation ρ (LinearTwo.centralBottom ρ K W) W g (sectionEquiv ρ K W v) := by
  induction v using Submodule.Quotient.induction_on with | _ v => rfl

private def multiplicityEquiv (W : Subrepresentation ρ) :
    SectionMultiplicity ρ s (SourceOrbit.selectedOrbitLower ρ K) W ≃ₗ[ZMod 2]
      SectionMultiplicity ρ s (LinearTwo.centralBottom ρ K W) W :=
  multiplicityCongr _ _ (sectionEquiv ρ K W)
    (fun g v => sectionEquiv_equivariant ρ K W (s g) v)

private theorem multiplicityEquiv_equivariant (W : Subrepresentation ρ) (k : K)
    (v : SectionMultiplicity ρ s (SourceOrbit.selectedOrbitLower ρ K) W) :
    multiplicityEquiv ρ K s W
      (sectionMultiplicityAction ρ K.subtype s hs (SourceOrbit.selectedOrbitLower ρ K) W k v) =
      sectionMultiplicityAction ρ K.subtype s hs (LinearTwo.centralBottom ρ K W) W k
        (multiplicityEquiv ρ K s W v) := by
  apply Subtype.ext
  simp only [multiplicityEquiv,sectionMultiplicityAction,multiplicity_apply,multiplicityCongr_apply]
  exact sectionEquiv_equivariant ρ K W k v.val


/-- A realized two-conjugate orbit supplies the required marked multiplicity
coordinates, using the literal quotient by the component fixed space. -/
theorem ConstituentRealization.exists_multiplicityCoordinates
    [FiniteDimensional (ZMod 2) V]
    {E N : Type*} [Group E] [AddCommGroup N] [Module (ZMod 2) N]
    {σ : Representation (ZMod 2) E N} {L : Subgroup E}
    (r : ConstituentRealization ρ K σ L)
    (horbit : orbitSpan ρ ⊤ r.space = r.space ⊔ r.space.map (ρ (s cubic)))
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤) :
    let W := SourceOrbit.selectedOrbitUpper ρ r.space
    ∃ a : SectionMultiplicity ρ s (LinearTwo.centralBottom ρ K W) W ≃ₗ[ZMod 2] N,
      ∀ k v, a (sectionMultiplicityAction ρ K.subtype s hs
        (LinearTwo.centralBottom ρ K W) W k v) = σ (r.component k) (a v) := by
  have horbit' : orbitSpan ρ ⊤ r.space =
      r.space ⊔ rightConjugate ρ r.space (s cubic)⁻¹ := by
    simpa only [rightConjugate,inv_inv] using horbit
  let e := SourceOrbit.selectedMultiplicityEquiv ρ K s hs r.space r.irrPlus
    (s cubic)⁻¹ horbit' hgen
  let W := SourceOrbit.selectedOrbitUpper ρ r.space
  let b := e.toLinearEquiv.trans (multiplicityEquiv ρ K s W)
  have hb (k : K) (v : centralQuotient ρ K r.space) :
      b (centralQuotientRepresentation ρ K r.space r.irrPlus.choose k v) =
        sectionMultiplicityAction ρ K.subtype s hs (LinearTwo.centralBottom ρ K W) W k (b v) :=
    (congrArg (multiplicityEquiv ρ K s W)
      (e.toIntertwiningMap.isIntertwining _ _ k v)).trans
        (multiplicityEquiv_equivariant ρ K s hs W k (e v))
  refine ⟨b.symm.trans r.linearEquiv,?_⟩
  intro k v
  have hsym : b.symm
      (sectionMultiplicityAction ρ K.subtype s hs (LinearTwo.centralBottom ρ K W) W k v) =
      centralQuotientRepresentation ρ K r.space r.irrPlus.choose k (b.symm v) := by
    apply b.injective
    rw [b.apply_symm_apply,hb,b.apply_symm_apply]
  change r.linearEquiv (b.symm _) = σ (r.component k) (r.linearEquiv (b.symm v))
  rw [hsym]
  exact r.component_intertwines k (b.symm v)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction
