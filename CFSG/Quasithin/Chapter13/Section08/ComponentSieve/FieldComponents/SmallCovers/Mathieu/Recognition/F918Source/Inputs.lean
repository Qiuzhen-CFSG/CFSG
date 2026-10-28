module
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.Contracts
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.F918Source.Actions
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Sections

/-!
# The earlier F.9.18 outputs in the ordinary M₂₂ branch

These are explicit source inputs, not assertions of F.9.18. The chosen
space satisfies the homogeneous Irr⁺ convention of A.1.40. The offender
lies in the actual edge core, acts faithfully on the component, and
retains both orbit-section actions from (3). All three alternatives in
(4) are retained, including the natural identifications, right conjugate,
direct sum, and nonisomorphism in (iii). The M₂₂ group assertion at the
start of (4) is already witnessed by the placement's actual model.

The source actor in (7) is literally K₀*T*. Relative normality and H=KT
identify it with H*. The universal no-FF contract therefore proves the
whole antecedent of (7), rather than non-FF status of one chosen module.

Source: Aschbacher–Smith, A.1.40, p.31, F.9.18(2–4),(7), pp.325–326,
and 13.8.21(2), p.956 (1 March 2004 manuscript).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.F918Source
universe u v

/-- The actual component models in F.9.18(4iii), used only as a consequence
of the complete action alternative below. -/
inductive SplitComponentModel (D : Type u) [Group D] : Prop
  | linearThree (F : BinaryField)
      (e : D ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
  | symplecticFour (F : BinaryField)
      (e : D ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | alternatingSix (e : D ≃* alternatingGroup (Fin 6))
  | linearFour (e : D ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
  | linearFive (e : D ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
  | alternatingSeven (e : D ≃* alternatingGroup (Fin 7))

variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (K T : Subgroup D) (I : Submodule (ZMod 2) V)

/-- The module assertion in F.9.18(4iii). Every natural action is an
intertwining equivalence on I/C_I(K). The A₇ exception bounds I itself. -/
inductive SplitAction (hI : IsIrrPlus ρ K I) : Prop
  | linearThree (F : BinaryField)
      (action : ActionEquiv (centralQuotientRepresentation ρ K I hI.choose)
        (linearNatural F 3))
  | symplecticFour (F : BinaryField)
      (action : ActionEquiv (centralQuotientRepresentation ρ K I hI.choose)
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))
  | alternatingSix
      (action : ActionEquiv (centralQuotientRepresentation ρ K I hI.choose)
        (alternatingNatural 6))
  | linearFour
      (action : ActionEquiv (centralQuotientRepresentation ρ K I hI.choose)
        (linearNatural BinaryField.two 4))
  | linearFive
      (action : ActionEquiv (centralQuotientRepresentation ρ K I hI.choose)
        (linearNatural BinaryField.two 5))
  | alternatingSeven (actor : K ≃* alternatingGroup (Fin 7))
      (dimension : Module.finrank (ZMod 2) I = 4)

/-- Forgetting the module retains an actual group isomorphism, not a tag. -/
theorem SplitAction.componentModel {hI : IsIrrPlus ρ K I}
    (h : SplitAction ρ K I hI) : SplitComponentModel K := by
  cases h with
  | linearThree F a => exact .linearThree F a.groupEquiv
  | symplecticFour F a => exact .symplecticFour F a.groupEquiv
  | alternatingSix a => exact .alternatingSix a.groupEquiv
  | linearFour a => exact .linearFour a.groupEquiv
  | linearFive a => exact .linearFive a.groupEquiv
  | alternatingSeven e _ => exact .alternatingSeven e

/-- All the clauses of the paired alternative: the nonstabilizing source
right conjugate, its direct sum modulo C_V(K), and nonisomorphism as K-modules. -/
structure SplitAlternative (hI : IsIrrPlusWith ρ K T I) where
  action : SplitAction ρ K I hI.isIrrPlus
  t : T
  not_stable : (t : D) ∉ subspaceStabilizer ρ I
  sum : (orbitSpan ρ ⊤ I).map (fixedSpace ρ K).mkQ =
    I.map (fixedSpace ρ K).mkQ ⊔ (rightConjugate ρ I t).map (fixedSpace ρ K).mkQ
  disjoint : Disjoint (I.map (fixedSpace ρ K).mkQ)
    ((rightConjugate ρ I t).map (fixedSpace ρ K).mkQ)
  nonisomorphic : ¬ SameModule (quotientImage ρ K I hI.invariant)
    (quotientImage ρ K (rightConjugate ρ I t)
      (hI.isIrrPlus.map_normalizer ρ (hI.normalizes (T.inv_mem t.property))).choose)

/-- Absence of every finite faithful FF-module for this exact actor. -/
def NoFFModules (D : Type u) [Group D] : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : Representation (ZMod 2) D V), Function.Injective σ → ¬ IsFFModule σ

variable {G : Type u} [Group G] [Finite G]
  {H K L₁ T G₁ M V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (s : Placement.Setup H K L₁ T G₁ M) (d : SourceAction H V₃ V₁)

include s in
omit [Finite G] in
/-- The source K₀, before taking its star image, is exactly K. -/
theorem component_orbit : conjugateSpanBy K T = K := by
  let := s.component_normal
  apply le_antisymm _ (le_conjugateSpanBy K T)
  apply conjugateSpanBy_le le_rfl
  exact (le_sup_right.trans s.seed_join_sylow_le).trans
    (le_normalizer_of_normal_subgroupOf s.component_le)

/-- Literal K₀*T*, not an arbitrary irreducible action image. -/
abbrev sourceActor : Subgroup (Source.Hstar H) :=
  Source.starImage H (conjugateSpanBy K T) ⊔ Source.starImage H T

include s in
omit [Finite G] in
theorem sourceActor_eq_top : sourceActor (H := H) (K := K) (T := T) = ⊤ := by
  rw [sourceActor, component_orbit s]
  exact s.star_component_join_sylow

include s in
/-- Derive F.9.18(7)'s universal antecedent for its actual source actor. -/
theorem no_ff_actor {𝒦 : GroupClass.{u}} (hH : IsSQTK 𝒦 H) (hno : NoFaithfulFF 𝒦) :
    NoFFModules (sourceActor (H := H) (K := K) (T := T)) := by
  let e : sourceActor (H := H) (K := K) (T := T) ≃* Source.Hstar H :=
    (MulEquiv.subgroupCongr (sourceActor_eq_top s)).trans (Subgroup.topEquiv)
  intro V _ _ _ σ hf
  exact hno _ _ σ ((IsSQTK.equiv e).mpr (source_sqtk hH)) hf
    ⟨(M22ValueBound.generalizedFittingEquiv e).trans (fittingCoordinates s)⟩

/-- K-invariance and T-invariance imply H*-invariance, since H = KT. -/
def stableSubrepresentation (I : Submodule (ZMod 2) (SourceSpace H V₃ V₁))
    (hK : Source.starImage H K ≤ subspaceStabilizer d.representation I)
    (hT : Source.starImage H T ≤ subspaceStabilizer d.representation I) :
    Subrepresentation d.representation where
  toSubmodule := I
  apply_mem_toSubmodule g v hv := by
    have hs := sup_le hK hT
    rw [s.star_component_join_sylow] at hs
    exact (hs (mem_top g) v).2 hv

/-- The action of K*T* on I_X, for X=T or H*, after forming the actual orbit span. -/
def orbitSubrepresentationT (I : Submodule (ZMod 2) (SourceSpace H V₃ V₁))
    (hI : IsIrrPlusWith d.representation (Source.starImage H K) (Source.starImage H T) I) :
    Subrepresentation d.representation :=
  orbitSubrepresentation d.representation hI.normalizes hI.isIrrPlus
    s.star_component_join_sylow

def orbitSubrepresentationH (I : Submodule (ZMod 2) (SourceSpace H V₃ V₁)) :
    Subrepresentation d.representation :=
  ⟨orbitSpan d.representation ⊤ I, fun g _ hv =>
    (orbitSpan_invariant d.representation ⊤ I (mem_top g) _).2 hv⟩

/-- The faithful offender and its quadratic bound in Aut_{K₀*T*}(I_X).
The subgroup map is surjective by construction, so faithfulness gives
exactly the isomorphism B* ≅ Aut_{B*}(I_X) in F.9.18(3). -/
structure OrbitOffender (A : Subgroup (Source.Hstar H))
    (W : Subrepresentation d.representation) : Prop where
  faithful : Function.Injective ((actionHom W.toRepresentation).subgroupMap A)
  elementary : IsElementaryTwo (actionSubgroup W.toRepresentation A)
  quadratic : IsQuadratic (imageRepresentation W.toRepresentation)
    (actionSubgroup W.toRepresentation A)
  bound : fixedCodim (imageRepresentation W.toRepresentation)
    (actionSubgroup W.toRepresentation A) ≤ 2 * rank (actionSubgroup W.toRepresentation A)

/-- The exact isomorphism in (3), retaining the original offender map. -/
def OrbitOffender.actorEquiv {A : Subgroup (Source.Hstar H)}
    {W : Subrepresentation d.representation} (h : OrbitOffender d A W) :
    A ≃* actionSubgroup W.toRepresentation A :=
  MulEquiv.ofBijective ((actionHom W.toRepresentation).subgroupMap A)
    ⟨h.faithful, (actionHom W.toRepresentation).subgroupMap_surjective A⟩

/-- The last numerical assertion of (3) is a consequence of its same offender. -/
theorem OrbitOffender.ratio_le_two {A : Subgroup (Source.Hstar H)}
    {W : Subrepresentation d.representation} (h : OrbitOffender d A W) :
    quadraticRatio (imageRepresentation W.toRepresentation) ≤ 2 :=
  (quadraticRatio_le_two_iff _).mpr
    ⟨actionSubgroup W.toRepresentation A, h.elementary, h.quadratic, h.bound⟩

/-- The three alternatives of F.9.18(4), prior to the M₂₂ deductions.
The second uses the actual faithful image Aut_{KT}(I), not a chosen K-module. -/
inductive FourAlternatives
    (I : Submodule (ZMod 2) (SourceSpace H V₃ V₁))
    (hI : IsIrrPlusWith d.representation (Source.starImage H K) (Source.starImage H T) I) : Prop
  | invariant (stable : (⊤ : Subgroup (Source.Hstar H)) ≤ subspaceStabilizer d.representation I)
  | ff (stable : Source.starImage H T ≤ subspaceStabilizer d.representation I)
      (ff : IsFFModule (imageRepresentation
        (stableSubrepresentation s d I hI.invariant stable).toRepresentation))
  | split (alternative : SplitAlternative d.representation
      (Source.starImage H K) (Source.starImage H T) I hI)

/-- The relevant earlier outputs, specialized to the genuine ordinary-M₂₂
setup. L is the earlier source L, so the edge core is O₂(LT ∩ H).
The initial model assertion in (4) is already witnessed by s.model.
The action and two orbit-offender outputs retain (2),(3); (4) retains
all three alternatives and all clauses of (iii); (7) uses its universal
faithful-module antecedent on the literal K₀*T* actor. -/
structure Earlier (L : Subgroup G) where
  I : Submodule (ZMod 2) (SourceSpace H V₃ V₁)
  irrPlus : IsIrrPlusWith d.representation (Source.starImage H K) (Source.starImage H T) I
  faithful : Function.Injective d.representation
  B : Subgroup G
  edge_core : B ≤ ((L ⊔ T) ⊓ H).pCoreIn 2
  sylow : B ≤ T
  elementary : IsElementaryTwo (Source.starImage H B)
  quadratic : IsQuadratic d.representation (Source.starImage H B)
  bound : fixedCodim d.representation (Source.starImage H B) ≤ 2 * rank (Source.starImage H B)
  faithful_component : Disjoint (Source.starImage H B)
    (centralizer (Source.starImage H K : Set (Source.Hstar H)))
  central_kernel_T : ((actionHom (orbitSubrepresentationT s d I irrPlus).toRepresentation).ker).subgroupOf (Source.starImage H K) ≤ center (Source.starImage H K)
  orbit_T : OrbitOffender d (Source.starImage H B) (orbitSubrepresentationT s d I irrPlus)
  orbit_H : OrbitOffender d (Source.starImage H B) (orbitSubrepresentationH d I)
  alternatives : FourAlternatives s d I irrPlus
  saturation : NoFFModules (sourceActor (H := H) (K := K) (T := T)) →
    orbitSpan d.representation ⊤ I =
      subspaceCommutator d.representation ⊤ (Source.starImage H K)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.F918Source
