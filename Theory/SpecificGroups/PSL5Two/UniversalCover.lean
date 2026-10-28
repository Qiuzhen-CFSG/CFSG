module

public import Theory.SpecificGroups.PSL5Two.UniversalCover.Lifts
public import Theory.SpecificGroups.PSL5Two.UniversalCover.LiftRelations
public import Theory.SpecificGroups.PSL5Two.UniversalCover.Faithfulness
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.CoveringKernelBound

/-!
# Assembly of the PSL₅(2) universal-cover calculation

Faithfulness of the binary Steinberg presentation and its relations in the
commutator lifts imply that the actual universal projection has trivial kernel.
The identity covering is then universal, and the universal kernel is explicitly
isomorphic to the trivial group. Entrywise field transport supplies the same
conclusions over every finite field of cardinality two.

The Bruhat normal form proves faithfulness, and the spare-index commutator
calculation proves the lifted relations. Applying both results discharges all
premises of the multiplier calculation. The conditional assembly statements
are retained alongside the unconditional conclusions.

Source: Aschbacher–Smith A.2.2(4), A.2.3(4), printed p.33, and I.1.3,
printed p.407, citing GLS98 §6.1.
-/

@[expose] public section

namespace Theory.SpecificGroups.PSL5Two.UniversalCover

open Theory.GroupTheory PerfectCentralCovering

universe u w

/-- The quasisimple structure on the actual projective matrix group. -/
theorem isQuasisimple (F : Type u) [Field F] :
    IsQuasisimple (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F) where
  toIsPerfect := Atlas.psl_perfect 5 (by decide)
  simple := by
    let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 5) F) :=
      Atlas.sl_perfect 5 (by decide)
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F) :=
      Atlas.psl_simple_high_rank 5 (by decide)
    have hz : Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F) = ⊥ :=
      Group.IsPerfect.center_quotient_center_eq_bot _
    exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup

local instance : IsQuasisimple G := isQuasisimple (ZMod 2)

/-- Conditional calculation for the literal free-central universal projection. -/
theorem universalProjection_ker_eq_bot_of_relations
    (hinj : Function.Injective projectiveMap)
    (hrel : Relations (rootLift (universalProjection G) (universalProjection_surjective G))) :
    (universalProjection G).ker = ⊥ :=
  ker_eq_bot_of_faithful_of_relations hinj _ (universalProjection_surjective G)
    (universalProjection_ker_le_center G) hrel

/-- The kernel bound certifies the identity map as a universal covering. -/
theorem identity_isUniversal_of_relations
    (hinj : Function.Injective projectiveMap)
    (hrel : Relations (rootLift (universalProjection G) (universalProjection_surjective G))) :
    Covering.IsUniversal.{0, 0, w} (Covering.id : Covering G G) := by
  apply Covering.isUniversal_of_kernel_card_le
  rw [Subgroup.card_eq_one.mpr (universalProjection_ker_eq_bot_of_relations hinj hrel)]
  exact Nat.card_pos

/-- The multiplier isomorphism retains its group structure. -/
noncomputable def universalKernelEquivPUnitOfRelations
    (hinj : Function.Injective projectiveMap)
    (hrel : Relations (rootLift (universalProjection G) (universalProjection_surjective G))) :
    (universalProjection G).ker ≃* PUnit := by
  have hk := universalProjection_ker_eq_bot_of_relations hinj hrel
  letI : Subsingleton (universalProjection G).ker := by rw [hk]; infer_instance
  letI : Unique (universalProjection G).ker := uniqueOfSubsingleton 1
  exact MulEquiv.ofUnique

/-- The actual PSL₅(2) universal central projection has trivial kernel. The
faithful matrix presentation and its lifted relations discharge both inputs
to the central-extension splitting argument. -/
theorem universalProjection_ker_eq_bot :
    (universalProjection G).ker = ⊥ :=
  universalProjection_ker_eq_bot_of_relations
    projectiveMap_injective universalProjection_rootLift_relations

/-- The identity covering of the actual PSL₅(2) is universal in every target
universe. -/
theorem identity_isUniversal :
    Covering.IsUniversal.{0, 0, w} (Covering.id : Covering G G) :=
  identity_isUniversal_of_relations
    projectiveMap_injective universalProjection_rootLift_relations

/-- The Schur multiplier of the actual PSL₅(2), as a multiplicative group. -/
noncomputable def universalKernelEquivPUnit :
    (universalProjection G).ker ≃* PUnit :=
  universalKernelEquivPUnitOfRelations
    projectiveMap_injective universalProjection_rootLift_relations

/-- The equivalence is induced entrywise by the field isomorphism, then descends
through the scalar center. It is not inferred from the order of the groups. -/
noncomputable def fieldEquiv (F : Type u) [Field F] [Finite F] (hF : Nat.card F = 2) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 5) F ≃* G := by
  letI := Fintype.ofFinite F
  exact Atlas.fieldEquivPSL 5 (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm

/-- Transport of triviality to the literal universal projection over an
arbitrary field of order two, allowing a different universe. -/
theorem field_universalProjection_ker_eq_bot_of_binary
    (F : Type u) [Field F] [Finite F] (hF : Nat.card F = 2)
    (hbinary : (universalProjection G).ker = ⊥) :
    (universalProjection (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)).ker = ⊥ := by
  let B := Matrix.ProjectiveSpecialLinearGroup (Fin 5) F
  let : IsQuasisimple B := isQuasisimple F
  have hid : Covering.IsUniversal.{0, 0, u} (Covering.id : Covering G G) := by
    apply Covering.isUniversal_of_kernel_card_le
    rw [Subgroup.card_eq_one.mpr hbinary]
    exact Nat.card_pos
  let c : Covering (UniversalGroup B) G :=
    (Covering.ofMulEquiv (fieldEquiv F hF)).comp (universalQuasisimpleCover B)
  let s := hid.lift c
  have hs := hid.lift_fac c
  apply (MonoidHom.ker_eq_bot_iff _).mpr
  intro x y hxy
  obtain ⟨a, rfl⟩ := s.surjective x
  obtain ⟨b, rfl⟩ := s.surjective y
  have ha : c (s a) = a := congrArg (fun k : Covering G G => k a) hs
  have hb : c (s b) = b := congrArg (fun k : Covering G G => k b) hs
  have hab : a = b := by
    rw [← ha, ← hb]
    exact congrArg (fieldEquiv F hF) hxy
  rw [hab]

theorem field_universalProjection_ker_eq_bot_of_relations
    (F : Type u) [Field F] [Finite F] (hF : Nat.card F = 2)
    (hinj : Function.Injective projectiveMap)
    (hrel : Relations (rootLift (universalProjection G) (universalProjection_surjective G))) :
    (universalProjection (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)).ker = ⊥ :=
  field_universalProjection_ker_eq_bot_of_binary F hF
    (universalProjection_ker_eq_bot_of_relations hinj hrel)

theorem field_identity_isUniversal_of_relations
    (F : Type u) [Field F] [Finite F] (hF : Nat.card F = 2)
    (hinj : Function.Injective projectiveMap)
    (hrel : Relations (rootLift (universalProjection G) (universalProjection_surjective G))) :
    letI := isQuasisimple F
    Covering.IsUniversal.{u, u, w} (Covering.id :
      Covering (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)
        (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)) := by
  let := isQuasisimple F
  apply Covering.isUniversal_of_kernel_card_le
  rw [Subgroup.card_eq_one.mpr (field_universalProjection_ker_eq_bot_of_relations F hF hinj hrel)]
  exact Nat.card_pos

noncomputable def fieldUniversalKernelEquivPUnitOfRelations
    (F : Type u) [Field F] [Finite F] (hF : Nat.card F = 2)
    (hinj : Function.Injective projectiveMap)
    (hrel : Relations (rootLift (universalProjection G) (universalProjection_surjective G))) :
    (universalProjection (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)).ker ≃* PUnit := by
  have hk := field_universalProjection_ker_eq_bot_of_relations F hF hinj hrel
  letI : Subsingleton (universalProjection
      (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)).ker := by rw [hk]; infer_instance
  letI : Unique (universalProjection (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)).ker :=
    uniqueOfSubsingleton 1
  exact MulEquiv.ofUnique

/-- Triviality of the literal universal kernel over every finite field of
cardinality two, transported through the field-induced matrix equivalence. -/
theorem field_universalProjection_ker_eq_bot
    (F : Type u) [Field F] [Finite F] (hF : Nat.card F = 2) :
    (universalProjection (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)).ker = ⊥ :=
  field_universalProjection_ker_eq_bot_of_binary F hF universalProjection_ker_eq_bot

/-- The identity covering remains universal over every field of order two. -/
theorem field_identity_isUniversal
    (F : Type u) [Field F] [Finite F] (hF : Nat.card F = 2) :
    letI := isQuasisimple F
    Covering.IsUniversal.{u, u, w} (Covering.id :
      Covering (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)
        (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)) :=
  field_identity_isUniversal_of_relations F hF
    projectiveMap_injective universalProjection_rootLift_relations

/-- The multiplicative Schur-multiplier equivalence over an arbitrary field
of order two, with no presentation or lifting hypotheses remaining. -/
noncomputable def fieldUniversalKernelEquivPUnit
    (F : Type u) [Field F] [Finite F] (hF : Nat.card F = 2) :
    (universalProjection (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)).ker ≃* PUnit :=
  fieldUniversalKernelEquivPUnitOfRelations F hF
    projectiveMap_injective universalProjection_rootLift_relations

end Theory.SpecificGroups.PSL5Two.UniversalCover
