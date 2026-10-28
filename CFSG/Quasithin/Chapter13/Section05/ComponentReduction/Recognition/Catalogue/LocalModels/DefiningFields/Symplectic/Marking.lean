module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.FullCatalogue
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.GroupTheory.SymmetricThreePairs.Transport
public import Theory.SpecificGroups.SymplecticFour.SylowCentralMarking
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Involutions.RootIdentification

/-!
# The actual symplectic involution in the 13.5.21 configuration

The B.4.2(3) action equivalence identifies the chief component with the
native matrix group. Its central quotient, together with the original
comparison K̂ ≃ L/Z(L), supplies a compatible matrix marking of K̂.
The proved Sylow-central innerness theorem then places V̂ inside K̂.

The resulting native involution retains its literal embedded cyclic subgroup
and the exact two-conjugate S₃ condition. Its central normal form has both
root coefficients: the mixed c₂ type has not been discarded. The later pair
obstruction must cover it along with the two root types.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.2(3), printed p.86, and 13.5.21(i),(iv), printed pp.923–924.
-/

public section
open Subgroup Theory.GroupTheory Representation
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.SylowCentralMarking
open Theory.GroupTheory.SymmetricThreePairs
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields.Symplectic
open Configuration ChapterB.QuasisimpleSource

variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]

/-- The actual chief action induces the component marking, through its central quotient. -/
noncomputable def sourceModelEquiv
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) (F : BinaryField)
    (action : ActionEquiv (ρ.comp L.subtype) (binarySymplectic F)) :
    Khat s h ≃* Sp F.Carrier :=
  comparison.trans (centralQuotientEquiv L action.groupEquiv)

/-- The original Sylow-central order-two subgroup is inner in every larger-field symplectic row. -/
theorem source_actor_le_component
    (hFitting : generalizedFitting (Xhat s h) = Khat s h)
    (hSylow : ∃ S : Sylow 2 (Xhat s h), (S : Subgroup (Xhat s h)) = That s h)
    (hcentral : Vhat s h ≤ centralizer (That s h : Set (Xhat s h)))
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) (F : BinaryField) (hlarge : 1 < F.degree)
    (action : ActionEquiv (ρ.comp L.subtype) (binarySymplectic F)) :
    Vhat s h ≤ Khat s h := by
  let : (Khat s h).Normal := hFitting ▸ inferInstance
  have hc : centralizer (Khat s h : Set (Xhat s h)) = ⊥ := by
    let : IsSimpleGroup (generalizedFitting (Xhat s h)) := hFitting.symm ▸ Khat_simple s h
    let : Group.IsPerfect (generalizedFitting (Xhat s h)) := hFitting.symm ▸ Khat_perfect s h
    simpa only [hFitting] using SimpleSocle.centralizer_eq_bot
      (Group.IsPerfect.not_isMulCommutative (generalizedFitting (Xhat s h)))
  obtain ⟨S, hS⟩ := hSylow
  intro v hv
  apply centralizes_sylow_mem_component (Khat s h) hc
    (sourceModelEquiv s h ρ L comparison F action) F.card_eq hlarge S
  change v ∈ centralizer ((S : Subgroup (Xhat s h)) : Set (Xhat s h))
  rw [hS]
  exact hcentral hv

/-- The matrix model is embedded back into the literal X̂ through its marked K̂. -/
noncomputable def sourceModelEmbedding
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) (F : BinaryField)
    (action : ActionEquiv (ρ.comp L.subtype) (binarySymplectic F)) :
    Sp F.Carrier →* Xhat s h :=
  (Khat s h).subtype.comp (sourceModelEquiv s h ρ L comparison F action).symm.toMonoidHom

theorem sourceModelEmbedding_injective
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) (F : BinaryField)
    (action : ActionEquiv (ρ.comp L.subtype) (binarySymplectic F)) :
    Function.Injective (sourceModelEmbedding s h ρ L comparison F action) :=
  (Khat s h).subtype_injective.comp (sourceModelEquiv s h ρ L comparison F action).symm.injective

/-- Sylow centrality supplies an actual native matrix involution, including all three central types. -/
theorem source_marked_involution
    (hFitting : generalizedFitting (Xhat s h) = Khat s h)
    (hSylow : ∃ S : Sylow 2 (Xhat s h), (S : Subgroup (Xhat s h)) = That s h)
    (hcentral : Vhat s h ≤ centralizer (That s h : Set (Xhat s h)))
    (hcard : Nat.card (Vhat s h) = 2)
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) (F : BinaryField) (hlarge : 1 < F.degree)
    (action : ActionEquiv (ρ.comp L.subtype) (binarySymplectic F)) :
    ∃ t : Sp F.Carrier, orderOf t = 2 ∧
      (zpowers t).map (sourceModelEmbedding s h ρ L comparison F action) = Vhat s h := by
  exact exists_marked_involution (Khat s h) (Vhat s h)
    (sourceModelEquiv s h ρ L comparison F action)
    (source_actor_le_component s h hFitting hSylow hcentral ρ L comparison F hlarge action) hcard

/-- Condition (iv) holds for the literal marked generator in the native group. -/
theorem source_native_pair_condition
    (hpair : PairCondition s h)
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) (F : BinaryField)
    (action : ActionEquiv (ρ.comp L.subtype) (binarySymplectic F))
    (t : Sp F.Carrier)
    (hmark : (zpowers t).map (sourceModelEmbedding s h ρ L comparison F action) = Vhat s h) :
    ∀ x : Sp F.Carrier,
      ¬ IsPGroup 2 (zpowers t ⊔ (zpowers t).map (MulAut.conj x).toMonoidHom : Subgroup (Sp F.Carrier)) →
      Nonempty ((zpowers t ⊔ (zpowers t).map (MulAut.conj x).toMonoidHom : Subgroup (Sp F.Carrier)) ≃*
        Equiv.Perm (Fin 3)) :=
  pairs_of_embedding (sourceModelEmbedding s h ρ L comparison F action)
    (sourceModelEmbedding_injective s h ρ L comparison F action) (Vhat s h) (zpowers t) hmark hpair

/-- The derived marking admits the full central two-root normal form; neither coefficient is assumed zero. -/
theorem source_marked_central_form
    (hFitting : generalizedFitting (Xhat s h) = Khat s h)
    (hSylow : ∃ S : Sylow 2 (Xhat s h), (S : Subgroup (Xhat s h)) = That s h)
    (hcentral : Vhat s h ≤ centralizer (That s h : Set (Xhat s h)))
    (hcard : Nat.card (Vhat s h) = 2)
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) (F : BinaryField) (hlarge : 1 < F.degree)
    (action : ActionEquiv (ρ.comp L.subtype) (binarySymplectic F)) :
    ∃ t : Sp F.Carrier, orderOf t = 2 ∧
      (zpowers t).map (sourceModelEmbedding s h ρ L comparison F action) = Vhat s h ∧
      ∃ a : Sp F.Carrier, ∃ b c : F.Carrier, a * t * a⁻¹ =
        Representation.OneCohomology.SymplecticFour.rootElement 0 b *
        Representation.OneCohomology.SymplecticFour.rootElement 4 c := by
  obtain ⟨t, ht, hm⟩ := source_marked_involution s h hFitting hSylow hcentral hcard
    ρ L comparison F hlarge action
  exact ⟨t, ht, hm, SymplecticConjugatePair.Involutions.involution_conjugate_central F.card_eq t ht⟩

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields.Symplectic
