module
public import CFSG.Quasithin.Defs
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.ComponentPairNormalizer
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio.Comparisons

/-!
# Restriction to the component and its quadratic actor

For D=KA, the original component, quadratic actor and marked Sylow normalizer
retain their literal inclusions. Restriction preserves the actor rank and fixed
codimension, its faithful conjugation on K, and the marked simple central
quotient. The final fixed-space implication transports back along these same
inclusions. This is the local group used in the constituent proof of 15.3.65.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
F.9.18(3–4), printed pp.325–326, and 15.3.65, printed p.1152.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal
open RepresentationReduction.SourceRestrictions
open Cases.Single.SmallRatio FFExclusions.ModelRigidity
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

/-- The component in the subgroup generated with the chosen actor. -/
def componentInSupEquiv (K A : Subgroup G) : K.subgroupOf (K ⊔ A) ≃* K :=
  subgroupOfEquivOfLe le_sup_left

theorem componentInSup_quasisimple (K A : Subgroup G) [IsQuasisimple K] :
    IsQuasisimple (K.subgroupOf (K ⊔ A)) :=
  IsQuasisimple.of_mulEquiv (componentInSupEquiv K A).symm

theorem componentInSup_center (K A : Subgroup G) (hZ : center K = ⊥) :
    center (K.subgroupOf (K ⊔ A)) = ⊥ := by
  apply _root_.eq_bot_iff.mpr
  intro z hz
  have he : componentInSupEquiv K A z ∈ center K :=
    (centerCongr (componentInSupEquiv K A) ⟨z,hz⟩).property
  apply (componentInSupEquiv K A).injective
  simpa only [map_one] using mem_bot.mp (hZ ▸ he)

theorem componentInSup_generated (K A : Subgroup G) :
    K.subgroupOf (K ⊔ A) ⊔ A.subgroupOf (K ⊔ A) = ⊤ := by
  rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]

theorem componentInSup_quotient [Finite G] (K A : Subgroup G) [K.Normal]
    (hA : IsElementaryTwo A) :
    IsPGroup 2 (↥(K ⊔ A) ⧸ K.subgroupOf (K ⊔ A)) := by
  let := hA.2
  exact isPGroup_quotient_of_sup_eq_top _ _
    (IsElementaryAbelian.isPGroup 2 A).comap_subtype (componentInSup_generated K A)

theorem actorInSup_elementary (K A : Subgroup G) (hA : IsElementaryTwo A) :
    IsElementaryTwo (A.subgroupOf (K ⊔ A)) := by
  let := hA.2
  refine ⟨?_,IsElementaryAbelian.subgroupOf (show A ≤ K ⊔ A from le_sup_right)⟩
  intro he
  apply hA.1
  rw [← map_subgroupOf_eq_of_le (show A ≤ K ⊔ A from le_sup_right),he,Subgroup.map_bot]

theorem actorInSup_faithful (K A : Subgroup G)
    (hAC : A ⊓ centralizer (K : Set G) = ⊥) :
    A.subgroupOf (K ⊔ A) ⊓
      centralizer (K.subgroupOf (K ⊔ A) : Set ↥(K ⊔ A)) = ⊥ := by
  apply _root_.eq_bot_iff.mpr
  intro x hx
  apply Subtype.ext
  apply mem_bot.mp
  rw [← hAC]
  refine ⟨hx.1,?_⟩
  intro k hk
  exact congrArg Subtype.val (hx.2 ⟨k,(le_sup_left : K ≤ K ⊔ A) hk⟩ hk)

theorem actorInSup_quadratic (ρ : Representation (ZMod 2) G V)
    (K A : Subgroup G) (hq : IsQuadratic ρ A) :
    IsQuadratic (ρ.comp (K ⊔ A).subtype) (A.subgroupOf (K ⊔ A)) := by
  intro a ha b hb w
  exact hq a.val ha b.val hb w

theorem actorInSup_bound (ρ : Representation (ZMod 2) G V)
    (K A : Subgroup G) (hc : fixedCodim ρ A ≤ 2 * rank A) :
    fixedCodim (ρ.comp (K ⊔ A).subtype) (A.subgroupOf (K ⊔ A)) ≤
      2 * rank (A.subgroupOf (K ⊔ A)) := by
  rwa [fixedCodim_subgroupOf ρ le_sup_right,rank_subgroupOf le_sup_right]

theorem componentInSup_model (K A : Subgroup G) {f : ℕ}
    (hm : SourceModel (K ⧸ center K) f) :
    SourceModel (K.subgroupOf (K ⊔ A) ⧸ center (K.subgroupOf (K ⊔ A))) f :=
  hm.transport (centralQuotientCongr (componentInSupEquiv K A))

/-- The marked Borel is transported by the actual component inclusion. -/
def borelInSup (K A : Subgroup G) (B : Subgroup K) :
    Subgroup (K.subgroupOf (K ⊔ A)) := B.comap (componentInSupEquiv K A).toMonoidHom

theorem borelInSup_sylow [Finite G] (K A : Subgroup G) (B : Subgroup K)
    (hB : ∃ S : Sylow 2 K, normalizer (S : Set K) = B) :
    ∃ S : Sylow 2 (K.subgroupOf (K ⊔ A)),
      normalizer (S : Set (K.subgroupOf (K ⊔ A))) = borelInSup K A B := by
  obtain ⟨S,hS⟩ := hB
  let e := componentInSupEquiv K A
  let P := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hP : (P : Subgroup (K.subgroupOf (K ⊔ A))) = (S : Subgroup K).comap e.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨s,hs,rfl⟩
      change e (e.symm s) ∈ (S : Subgroup K)
      rw [e.apply_symm_apply]
      exact hs
    · intro hx
      exact ⟨e x,hx,e.symm_apply_apply x⟩
  refine ⟨P,?_⟩
  change normalizer (↑(P : Subgroup (K.subgroupOf (K ⊔ A))) : Set (K.subgroupOf (K ⊔ A))) = _
  rw [hP,← comap_normalizer_eq_of_surjective _ e.surjective]
  change (normalizer (S : Set K)).comap e.toMonoidHom = _
  rw [hS]
  rfl

/-- The conclusion on the generated subgroup is the original component
fixed-space conclusion, with no replacement of its Borel or representation. -/
theorem fixedSpace_le_of_componentInSup (ρ : Representation (ZMod 2) G V)
    (K A : Subgroup G) (B : Subgroup K)
    (h : fixedSpace ((ρ.comp (K ⊔ A).subtype).comp
          (K.subgroupOf (K ⊔ A)).subtype) (borelInSup K A B) ≤
      fixedSpace ((ρ.comp (K ⊔ A).subtype).comp
          (K.subgroupOf (K ⊔ A)).subtype) ⊤) :
    fixedSpace (ρ.comp K.subtype) B ≤ fixedSpace (ρ.comp K.subtype) ⊤ := by
  intro w hw k
  have hw' : w ∈ fixedSpace ((ρ.comp (K ⊔ A).subtype).comp
      (K.subgroupOf (K ⊔ A)).subtype) (borelInSup K A B) := by
    intro b
    exact hw ⟨componentInSupEquiv K A b.val,b.property⟩
  exact h hw' ⟨(componentInSupEquiv K A).symm k.val,mem_top _⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal
