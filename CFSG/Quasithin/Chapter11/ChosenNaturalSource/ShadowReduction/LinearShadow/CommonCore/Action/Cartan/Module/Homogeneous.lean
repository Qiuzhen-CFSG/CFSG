module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Classification
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.FullMovedEquivalence
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.CaseComparison
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The original component orbit as copies of the chosen natural module

B.5.1(3) makes the fixed-free moved orbit homogeneous unless its component
is binary SL₄ or SL₅. The original SL₃/Sp₄ marking excludes those groups.
An injective equivariant copy of the chosen seed has a nonzero coordinate
projection onto an irreducible homogeneous summand, hence an isomorphism.
Applying it in every coordinate produces copies with the original field,
component quotient and left conjugation marking. No bound on multiplicity
is needed for the Cartan calculation; in particular the doubled SL₃ case
is retained. The zero fixed kernel used here is proved from local uniqueness
before applying B.5.1, so no central extension is silently split.

The actual application is `source_cartan_dichotomy` in Module/Dichotomy.lean.
The natural quotient marking and Hall containment are discharged by
Action/SourceComplete.lean, owned by qt-d-1222-shadow-common-action.
Source: Aschbacher--Smith, 11.3.7(3), printed p.773, using B.5.1(3), p.99.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

private theorem homogeneous_coordinates_of_embedding
    {A B M N P : Type*} [Group A] [Group B]
    [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N]
    [AddCommGroup P] [Module (ZMod 2) P]
    (ρ : Representation (ZMod 2) A M) (σ : Representation (ZMod 2) B N)
    (τ : Representation (ZMod 2) A P)
    (φ : A →* B) (hφ : Function.Surjective φ)
    (e : M ≃ₗ[ZMod 2] N) (he : ∀ a m, e (ρ a m) = σ (φ a) (e m))
    (hh : IsHomogeneousAction σ) (ht : IsIrreducible τ)
    (j : P →ₗ[ZMod 2] M) (hj : Function.Injective j)
    (hact : ∀ a p, j (τ a p) = ρ a (j p)) :
    ∃ r : ℕ, 0 < r ∧ ∃ f : M ≃ₗ[ZMod 2] (Fin r → P),
      ∀ a m i, f (ρ a m) i = τ a (f m i) := by
  classical
  obtain ⟨r,hr,W,hi,f,hf⟩ := hh
  let κ := W.toRepresentation.comp φ
  let : IsIrreducible κ := (irreducible_comp_surjective_iff φ hφ _).mpr hi
  let : IsIrreducible τ := ht
  let : Nontrivial P := Subrepresentation.irreducible_module_nontrivial τ
  obtain ⟨v,hv⟩ := exists_ne (0 : P)
  have hne : f (e (j v)) ≠ 0 := by
    intro hz
    apply hv
    apply hj
    apply e.injective
    apply f.injective
    simpa using hz
  obtain ⟨i,hi⟩ : ∃ i : Fin r, f (e (j v)) i ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  let p : τ.IntertwiningMap κ :=
    ((LinearMap.proj i).comp (f.toLinearMap.comp (e.toLinearMap.comp j))).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro a v
      change f (e (j (τ a v))) i = W.toRepresentation (φ a) (f (e (j v)) i)
      rw [hact,he,hf]
      rfl)
  have hp : p ≠ 0 := by
    intro hp
    apply hi
    exact congrArg (fun q : τ.IntertwiningMap κ => q v) hp
  let E := p.ofBijective ((IsIrreducible.bijective_or_eq_zero p).resolve_right hp)
  refine ⟨r,hr,(e.trans f).trans (LinearEquiv.piCongrRight fun _ : Fin r => E.symm.toLinearEquiv),?_⟩
  intro a m i
  change E.symm (f (e (ρ a m)) i) = τ a (E.symm (f (e m) i))
  rw [he,hf]
  exact IntertwiningMap.isIntertwining (ρ := κ) (σ := τ) E.symm.toIntertwiningMap a (f (e m) i)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The literal omega-center orbit is a positive sum of the original chosen natural action. -/
theorem source_component_coordinates
    (cL : Coordinates D S.field)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (s : Hypothesis1131At D S U₁ H) (c : NaturalQuotientMarking T H S.field)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hAL : oddCartanPart A ≤ L) :
    ∃ r : ℕ, 0 < r ∧ ∃ e : ComponentOmegaSpace D S ≃ₗ[ZMod 2] (Fin r → cL.Space),
      ∀ (l : L) (v : ComponentOmegaSpace D S) i,
        e (componentOmegaRepresentation D S (componentOmegaActorMap D S l) v) i =
          cL.modelAction (cL.quotientMap l) (e v i) := by
  obtain ⟨_,hv,_,hVU,hm,hc⟩ := source_component_module s c A hA hHall hAL
  obtain ⟨C⟩ := componentOmega_classification_of_seed s hVU
  let ρ := componentOmegaRepresentation D S
  let O := offenderSubgroup ρ
  let B := (componentOmegaActor D S).subgroupOf O
  let σ := ρ.comp O.subtype
  have hBO := componentOmegaActor_le_offender s
  let eB : (L ⧸ pCore 2 L) ≃* B :=
    (componentOmegaActorEquiv (D := D) (S := S) hVU).trans (subgroupOfEquivOfLe hBO).symm
  let φ : L →* B := eB.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hφ : Function.Surjective φ := eB.surjective.comp (QuotientGroup.mk'_surjective _)
  have hm' : moved σ B = ⊤ := by
    rw [moved,subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hBO]
    exact componentOmega_moved_eq_top hm
  have hc' : fixedSpace σ B = ⊥ := by
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hBO]
    exact componentOmega_fixed_eq_bot hc
  have hh : IsHomogeneousAction (C.sectionData.action.comp B.subtype) := by
    rcases C.clause_three with hh | ⟨d,hd,⟨a⟩⟩
    · exact hh
    · have e' := eB.trans a.groupEquiv
      cases cL with
      | sl3 m => exact (SourceCompletion.no_linearThree_binary_equiv S.field hd
          (m.groupEquiv.symm.trans e')).elim
      | sp4 m => exact (SourceCompletion.no_symplectic_binary_equiv S.field hd
          (m.groupEquiv.symm.trans e')).elim
      | g2 m => exact (hG2 ⟨m⟩).elim
  let E := C.sectionData.fullProjectionEquiv hm' hc'
  let τ := (restrictScalars (k := ZMod 2) cL.modelAction).comp cL.quotientMap
  have hτ : IsIrreducible τ := by
    have hq : IsIrreducible D.chosenCentralAction :=
      (irreducible_comp_surjective_iff (QuotientGroup.mk' (pCore 2 L))
        (QuotientGroup.mk'_surjective _) D.centralQuotientAction).mpr
          D.centralQuotientAction_irreducible
    let a : ActionEquiv D.chosenCentralAction τ :=
      ⟨MulEquiv.refl L,cL.linearEquiv,fun l v => cL.intertwines (QuotientGroup.mk' _ l) v⟩
    exact ExtensionConsequences.irreducible_of_equiv (ExtensionConsequences.actionSymm a) hq
  have hi : Function.Injective cL.projection := by
    apply cL.projection.ker_eq_bot_iff.mp
    apply bot_unique
    intro v hv'
    exact Subtype.ext (hv.le ⟨v.property,(cL.projection_eq_one_iff v).mp hv'⟩)
  let eV : V ≃* Multiplicative cL.Space := MulEquiv.ofBijective cL.projection
    ⟨hi,cL.projection_surjective⟩
  let J := L ⊔ (T : Subgroup G)
  let jMul : Multiplicative cL.Space →* (componentOmegaSpan T L).subgroupOf J := {
    toFun v := ⟨⟨eV.symm v, (D.le_sylow.trans le_sup_right) (eV.symm v).property⟩,
      hVU (eV.symm v).property⟩
    map_one' := by apply Subtype.ext; apply Subtype.ext; exact congrArg (fun x : V => (x : G)) eV.symm.map_one
    map_mul' v w := by apply Subtype.ext; apply Subtype.ext; exact congrArg (fun x : V => (x : G)) (eV.symm.map_mul v w) }
  let j : cL.Space →ₗ[ZMod 2] ComponentOmegaSpace D S :=
    (MonoidHom.toAdditive jMul).toZModLinearMap 2
  have hj : Function.Injective j := by
    intro x y he
    apply eV.symm.injective
    apply Subtype.ext
    exact congrArg (fun z : ComponentOmegaSpace D S => (z.toMul.val : G)) he
  have heV (l : L) (v : cL.Space) :
      eV.symm (Multiplicative.ofAdd (τ l v)) =
        V.normalizerMonoidHom (inclusion D.normalizes l) (eV.symm (Multiplicative.ofAdd v)) := by
    apply eV.injective
    rw [eV.apply_symm_apply]
    change Multiplicative.ofAdd (τ l v) = cL.projection _
    apply Multiplicative.toAdd.injective
    rw [cL.projection_component_conjugation]
    change _ = cL.modelAction _ (eV (eV.symm _)).toAdd
    rw [eV.apply_symm_apply]
    rfl
  have hjact (l : L) (v : cL.Space) :
      j (τ l v) = (ρ.comp (componentOmegaActorMap D S)) l (j v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (eV.symm (Multiplicative.ofAdd (τ l v)) : G) = _
    rw [heV]
    exact (componentOmegaRepresentation_apply (D := D) (S := S)
      (inclusion le_sup_left l) (j v)).symm
  have he (l : L) (v : ComponentOmegaSpace D S) :
      E ((ρ.comp (componentOmegaActorMap D S)) l v) =
        (C.sectionData.action.comp B.subtype) (φ l) (E v) := by
    exact C.sectionData.fullProjection_intertwines hm' (φ l).val v
  exact homogeneous_coordinates_of_embedding (ρ.comp (componentOmegaActorMap D S))
    (C.sectionData.action.comp B.subtype) τ φ hφ E he hh hτ j hj hjact

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
