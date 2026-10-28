module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MinimalPlanes.SourceAction.CoprimeSpace
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MinimalPlanes.Assembly

/-!
# The source action reduction for a minimal Fitting offender

The homomorphism H=F_A A → Aut_H(W) is the literal restricted action on
W=[C_V(C_A(F_A)),F_A]. Faithfulness of F_A on W embeds the action kernel
in the two-group H/F_A. Thus its kernel is O₂(H)=C_A(F_A), and the faithful
image has trivial two-core. Solvability and normal generation pass through
this same surjection. Coprime idempotence excludes trivial action by A.

Together with odd-order splitting, these facts construct every field of
`SourceReduction` from the original hypotheses. The last theorem applies
the existing B.1.5/B.1.8 assembly to recover the actual minimal Fitting plane.
No plane dimension, order-three, or ambient solvability premise is added.

Source: Aschbacher–Smith, B.1.9, first proof paragraph,
printed p.71 (PDF p.82), combined manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure.MinimalPlanes
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The actual action map from the whole local group onto its image on W. -/
noncomputable def sourceActionHom {A : Subgroup G} (hA : IsElementaryTwo A) :
    localGroup A →* testImage ρ A :=
  (subgroupActionHom (localRepresentation ρ A) (testSpace ρ A) ⊤
    (source_local_stable ρ hA)).comp Subgroup.topEquiv.symm.toMonoidHom

theorem sourceActionHom_surjective {A : Subgroup G} (hA : IsElementaryTwo A) :
    Function.Surjective (sourceActionHom ρ hA) := by
  intro x
  obtain ⟨g, rfl⟩ := (stabilizerRepresentation (localRepresentation ρ A)
    (testSpace ρ A)).asGroupHom.rangeRestrict_surjective x
  exact ⟨g, rfl⟩

theorem sourceActionHom_ker {A : Subgroup G} (hA : IsElementaryTwo A) :
    (sourceActionHom ρ hA).ker =
      subspaceKernel (localRepresentation ρ A) (testSpace ρ A) ⊤ := by
  ext g
  constructor
  · intro hg
    refine ⟨mem_top g, fun v hv => ?_⟩
    have he := congrArg (fun a => subspaceImageRepresentation (localRepresentation ρ A)
      (testSpace ρ A) a ⟨v, hv⟩) hg
    exact congrArg Subtype.val he
  · rintro ⟨_, hg⟩
    apply subspaceImageRepresentation_injective (localRepresentation ρ A) (testSpace ρ A)
    ext v
    exact hg v v.property

theorem source_restricted_eq_map {A : Subgroup G} (hA : IsElementaryTwo A)
    (X : Subgroup (localGroup A)) :
    restrictedSubgroup (localRepresentation ρ A) (testSpace ρ A) X =
      X.map (sourceActionHom ρ hA) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, source_local_stable ρ hA (mem_top a)⟩, ha, rfl⟩

variable [Finite G]

theorem source_image_solvable {A : Subgroup G} (hA : IsElementaryTwo A) :
    Group.IsSolvable (testImage ρ A) := by
  let := localGroup_solvable hA
  exact Group.isSolvable_of_surjective (sourceActionHom_surjective ρ hA)

theorem source_image_generated (hcore : pCore 2 G = ⊥) {A : Subgroup G}
    (hA : IsElementaryTwo A) : normalClosure
      (restrictedSubgroup (localRepresentation ρ A) (testSpace ρ A) (localActor A) :
        Set (testImage ρ A)) = ⊤ := by
  rw [source_restricted_eq_map ρ hA, coe_map,
    ← map_normalClosure _ _ (sourceActionHom_surjective ρ hA),
    localActor_normally_generates hcore hA]
  exact map_top_of_surjective _ (sourceActionHom_surjective ρ hA)

omit [Finite G] in
private theorem localOdd_quotient_two {A : Subgroup G} (hA : IsElementaryTwo A) :
    IsPGroup 2 (localGroup A ⧸ localOdd A) := by
  let := hA.2
  let q := QuotientGroup.mk' (localOdd A)
  have hmap : (localActor A).map q = ⊤ := by
    have h := congrArg (fun D : Subgroup (localGroup A) => D.map q) (localOdd_sup_localActor A)
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective (localOdd A))] at h
    exact h
  exact ((IsElementaryAbelian.isPGroup 2 A).comap_subtype (K := localGroup A)).of_surjective
    (q.domRestrict (localActor A)) (MonoidHom.range_eq_top.mp ((MonoidHom.domRestrict_range (localActor A) q).trans hmap))

variable [FiniteDimensional (ZMod 2) V]

theorem sourceActionHom_ker_two (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {A : Subgroup G} (hA : IsElementaryTwo A) : IsPGroup 2 (sourceActionHom ρ hA).ker := by
  let K := (sourceActionHom ρ hA).ker
  let q := QuotientGroup.mk' (localOdd A)
  have hinj : Function.Injective (q.comp K.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro g hg
    have hN : (g : localGroup A) ∈ localOdd A :=
      (QuotientGroup.eq_one_iff (N := localOdd A) g.val).mp hg
    have hfix : g.val ∈ subspaceKernel (localRepresentation ρ A) (testSpace ρ A) ⊤ := by
      rw [← sourceActionHom_ker ρ hA]
      exact g.property
    have hz : (g.val : G) = 1 := (subspaceKernel_eq_bot_iff ρ _ _).mp
      (source_oddPart_faithful ρ hf hcore hA) g.val hN hfix.2
    exact Subtype.ext (Subtype.ext hz)
  exact (localOdd_quotient_two hA).of_injective _ hinj

/-- The pointwise kernel on W is exactly the relative centralizer B inside H. -/
theorem source_kernel (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {A : Subgroup G} (hA : IsElementaryTwo A) :
    subspaceKernel (localRepresentation ρ A) (testSpace ρ A) ⊤ =
      (kernelActor A).subgroupOf (localGroup A) := by
  rw [← sourceActionHom_ker ρ hA]
  apply le_antisymm
  · rw [← localGroup_twoCore hcore hA]
    exact le_sSup ⟨inferInstance, sourceActionHom_ker_two ρ hf hcore hA⟩
  · intro g hg
    rw [sourceActionHom_ker ρ hA]
    exact ⟨mem_top g, fun w hw => testSpace_le_fixed ρ A hw ⟨g.val, hg⟩⟩

theorem source_image_core (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {A : Subgroup G} (hA : IsElementaryTwo A) : pCore 2 (testImage ρ A) = ⊥ := by
  let f := sourceActionHom ρ hA
  have hker : f.ker = pCore 2 (localGroup A) :=
    (sourceActionHom_ker ρ hA).trans ((source_kernel ρ hf hcore hA).trans
      (localGroup_twoCore hcore hA).symm)
  have hp := pCore_isPGroup.comap_of_ker_isPGroup f (sourceActionHom_ker_two ρ hf hcore hA)
  have hle : (pCore 2 (testImage ρ A)).comap f ≤ f.ker := by
    rw [hker]
    exact le_sSup ⟨inferInstance, hp⟩
  apply bot_unique
  intro x hx
  obtain ⟨g, rfl⟩ := sourceActionHom_surjective ρ hA x
  exact hle hx

theorem source_actor_moving (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hne : oddPart A ≠ ⊥) :
    subspaceCommutator (localRepresentation ρ A) (testSpace ρ A) (localActor A) ≠ ⊥ := by
  intro hz
  have hfix := (subspaceCommutator_eq_bot_iff (localRepresentation ρ A)
    (testSpace ρ A) (localActor A)).mp hz
  have hc : A ≤ centralizer (oddPart A : Set G) := by
    intro a ha
    let a' : localGroup A := ⟨a, (show A ≤ localGroup A from le_sup_right) ha⟩
    have hm : a' ∈ subspaceKernel (localRepresentation ρ A) (testSpace ρ A) ⊤ :=
      ⟨mem_top a', fun w hw => hfix hw ⟨a', ha⟩⟩
    rw [source_kernel ρ hf hcore hA] at hm
    exact hm.2
  apply hne
  rw [← oddPart_idempotent hcore hA, commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hc

/-- The full fixed-space action reduction, with no extra mathematical premises. -/
theorem sourceReduction (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A) (hne : oddPart A ≠ ⊥) :
    SourceReduction ρ A where
  stable := source_local_stable ρ hA.1.1
  moving := source_actor_moving ρ hf hcore hA.1.1 hne
  fixed := testSpace_le_fixed ρ A
  self_moved := source_testSpace_self_moved ρ hcore hA.1.1
  image_solvable := source_image_solvable ρ hA.1.1
  image_core := source_image_core ρ hf hcore hA.1.1
  image_generated := source_image_generated ρ hcore hA.1.1
  kernel := source_kernel ρ hf hcore hA.1.1
  odd := oddPart_odd hcore A

/-- Applying the checked B.1.5/B.1.8 assembly to the source action reduction
produces all seven conclusions for the original Fitting plane. -/
theorem minimalFittingPlane_of_sourceAction (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) {A : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (hne : oddPart A ≠ ⊥) :
    Nonempty (MinimalFittingPlane ρ A) :=
  minimalFittingPlane_of_reduction ρ hf hA hne (sourceReduction ρ hf hcore hA hne)

end CFSG.Quasithin.ChapterB.FittingStructure.MinimalPlanes
