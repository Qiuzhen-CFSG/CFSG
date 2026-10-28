module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.OrdinaryGeometry
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Splitting
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Field restrictions for the ordinary nonsplit second factor

If a perfect actor has vanishing H¹ on its quotient by fixed vectors, then
H¹ on the original module also vanishes: subtract a principal cocycle lifting
the quotient class, and the remaining fixed-valued cocycle is a homomorphism
from a perfect group to an abelian group, hence zero.

Apply this to V₂=C_V(G₁), using the literal quotient comparisons. Vanishing
on V₂ supplies fixed lifts in V, since [V,G₂] is contained in V₂. The checked
large-field SL₃ cohomology calculation therefore forces the field degree to
be one in both the natural and doubled-natural rows whenever C_V(G₂)+V₂<V.
No offender generation is transferred from V₂ to V, and no earlier-source
implication is assumed. The separate S₅ exclusion and binary fixed-kernel
argument are not consequences of this field restriction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the concluding
proof of B.5.6, printed p.110, and the cohomology in I.1.6, printed p.408.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
open Representation.OneCohomology
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
open ComponentReduction

variable {D U : Type*} [Group D] [Group.IsPerfect D]
  [AddCommGroup U] [Module (ZMod 2) U] (σ : Representation (ZMod 2) D U)

private theorem perfect_H1_of_reduced [Subsingleton (H1 (reducedAction σ))] : Subsingleton (H1 σ) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro f _
  let q := σ.invariants.mkQ
  let cf : cocycles (reducedAction σ) :=
    ⟨fun g => q (f.val g), fun g h => by
      change q (f.val (g*h)) = q (σ g (f.val h)) + q (f.val g)
      rw [f.property, map_add]⟩
  obtain ⟨u, hu⟩ := (classMap_eq_zero_iff _ cf).mp (Subsingleton.elim _ _)
  obtain ⟨v, rfl⟩ := σ.invariants.mkQ_surjective u
  let d := f - principal σ v
  have hd (g : D) : d.val g ∈ σ.invariants := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have he := congrArg (fun x : cocycles (reducedAction σ) => x.val g) hu
    change q (σ g v) - q v = q (f.val g) at he
    change q (f.val g - (σ g v - v)) = 0
    rw [map_sub, map_sub, he, sub_self]
  let h : D →* Multiplicative U :=
    { toFun := fun g => Multiplicative.ofAdd (d.val g)
      map_one' := by
        change d.val 1 = 0
        have he := d.property 1 1
        simpa using he
      map_mul' := fun g t => by
        change d.val (g*t) = d.val g + d.val t
        rw [d.property, hd t g, add_comm] }
  let : Group.IsPerfect h.range := Group.IsPerfect.range h
  have hz (g : D) : d.val g = 0 := by
    have he : (⟨h g, g, rfl⟩ : h.range) = 1 := Subsingleton.elim _ _
    exact congrArg (fun x : h.range => Multiplicative.toAdd x.val) he
  refine ⟨v, ?_⟩
  apply Subtype.ext
  funext g
  exact (sub_eq_zero.mp (hz g)).symm


private def compAction {A B C X Y Z : Type*} [Group A] [Group B] [Group C]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    {α : Representation (ZMod 2) A X} {β : Representation (ZMod 2) B Y}
    {γ : Representation (ZMod 2) C Z}
    (e : ActionEquiv α β) (f : ActionEquiv β γ) : ActionEquiv α γ :=
  ⟨e.groupEquiv.trans f.groupEquiv,e.linearEquiv.trans f.linearEquiv,
    fun g v => (congrArg f.linearEquiv (e.intertwines g v)).trans (f.intertwines _ _)⟩

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The actual fixed quotient on V₂, with the factor actor unwrapped. -/
noncomputable def secondReducedFactorEquiv (c : Conclusion ρ)
    (f : FactorModuleConclusion (secondAction c)) :
    ActionEquiv (reducedAction (secondAction c)) (secondFactorAction c f) :=
  compAction (secondQuotientEquiv c) (actionSymm (factorQuotientEquiv c f))

/-- Vanishing on V₂ supplies a fixed lift of every vector of V/V₂. -/
theorem second_fixed_supplement_of_H1 (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    [Subsingleton (H1 (secondAction c))] :
    fixedSpace ρ (second c) ⊔ c.productConfiguration.fixed.toSubmodule = ⊤ := by
  let U : Subrepresentation (ρ.comp (second c).subtype) :=
    { toSubmodule := c.productConfiguration.fixed.toSubmodule
      apply_mem_toSubmodule g v hv := c.productConfiguration.fixed.apply_mem_toSubmodule g hv }
  let : Subsingleton (H1 U.toRepresentation) := ‹Subsingleton (H1 (secondAction c))›
  have ht : HasTrivialQuotient U := by
    intro g v
    exact second_moved_le_fixed c he (Submodule.subset_span
      ⟨g,g.property,v,Submodule.mem_top,rfl⟩)
  apply top_unique
  intro v _
  have hv := (extensionClass_eq_zero_iff U ht v).mp (Subsingleton.elim _ _)
  change v ∈ c.productConfiguration.fixed.toSubmodule ⊔ fixedSpace ρ (second c) at hv
  rwa [sup_comm] at hv

/-- The natural SL₃ row over a larger field forces the excluded supplement. -/
theorem linearThree_degree_eq_one (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (hp : fixedSpace ρ (second c) ⊔ c.productConfiguration.fixed.toSubmodule ≠ ⊤)
    (F : BinaryField) (hn : IsLinearNatural (secondFactorAction c f) F 3) :
    F.degree = 1 := by
  by_contra hF
  have hlarge : 1 < F.degree := by have h := F.degree_pos; omega
  obtain ⟨n⟩ := hn
  let e := compAction (secondReducedFactorEquiv c f) n
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :=
    Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect (second c) :=
    Group.IsPerfect.ofSurjective (f := e.groupEquiv.symm.toMonoidHom) e.groupEquiv.symm.surjective
  let := H1_three_large F hlarge
  let := e.H1_subsingleton
  let := perfect_H1_of_reduced (secondAction c)
  exact hp (second_fixed_supplement_of_H1 c he)

/-- The same cohomology argument applies to both copies with their common marking. -/
theorem doubleThree_degree_eq_one (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (hp : fixedSpace ρ (second c) ⊔ c.productConfiguration.fixed.toSubmodule ≠ ⊤)
    (F : BinaryField) (hn : IsRepeatedLinearNatural (secondFactorAction c f) F 3 2) :
    F.degree = 1 := by
  by_contra hF
  have hlarge : 1 < F.degree := by have h := F.degree_pos; omega
  obtain ⟨n⟩ := hn
  let e := compAction (secondReducedFactorEquiv c f) n
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :=
    Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect (second c) :=
    Group.IsPerfect.ofSurjective (f := e.groupEquiv.symm.toMonoidHom) e.groupEquiv.symm.surjective
  let := H1_three_large F hlarge
  let := H1_repeated_subsingleton (ρ := linearNatural F 3) 2
  let := e.H1_subsingleton
  let := perfect_H1_of_reduced (secondAction c)
  exact hp (second_fixed_supplement_of_H1 c he)

end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
