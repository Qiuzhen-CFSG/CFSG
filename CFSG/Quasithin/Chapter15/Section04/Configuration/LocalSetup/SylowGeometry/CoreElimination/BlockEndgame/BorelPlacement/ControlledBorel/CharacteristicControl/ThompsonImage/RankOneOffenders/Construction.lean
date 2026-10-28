module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.ThompsonImage.RankOneOffenders.Section
public import Theory.GroupTheory.PCoreKernelRange

/-!
# A faithful natural section of the omega-center action

Write D = K₁R, Q = O₂(D), and V = Ω₁(Z(Q)). Under the kernel equality
C_D(V) = Q, the block layer U(K₁) lies in V. Its central fixed subgroup
C_U(K₁)(K₁) and U(K₁) therefore give invariant binary subspaces of the
literal V-representation. The block model supplies the quotient coordinates
and the first-image matrix isomorphism together, preserving conjugation.

For faithfulness, the section kernel meets the first image trivially because
the natural matrix action is faithful. It consequently embeds in the
two-group quotient of the action group by that image. It is a normal
two-subgroup, whereas the kernel equality makes the action group's two-core
trivial. This proves faithfulness on the section without a field-size
restriction or a cohomology hypothesis.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–13,
printed pp.123–125; C.2.7, pp.145–146; the block case in the proof of
15.4.20, p.1164. This is the conditional natural-section construction;
offender recognition and the source-theorem assembly are separate.
-/

public section

open Subgroup Stellmacher
open Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.ThompsonImage
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
variable {c : ContraryData κ d i j} (b : ExchangedBlock c)
noncomputable section

namespace NaturalSectionConstruction

/-- The literal automorphism image is two-reduced under the prescribed kernel equality. -/
theorem actionGroup_pCore_eq_bot
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b)) :
    pCore 2 (ActionGroup b) = ⊥ := by
  apply pCore_range_eq_bot_of_ker_eq_pCore 2 (action b)
  rw [hker]
  change ((pCore 2 (localGroup b)).map (localGroup b).subtype).comap
    (localGroup b).subtype = _
  exact comap_map_eq_self_of_injective (localGroup b).subtype_injective _

/-- The image of R supplements the first image, so the quotient by the first image is a two-group. -/
theorem actionGroup_quotient_first_isPGroup :
    IsPGroup 2 (ActionGroup b ⧸ faithfulImage b b.first) := by
  apply isPGroup_quotient_of_sup_eq_top (faithfulImage b b.first)
    (faithfulImage b (contraryCore c))
    (((isPGroup_pCoreIn 2 _).comap_subtype).map (actionProjection b))
  rw [faithfulImage, faithfulImage, ← Subgroup.map_sup,
    ← subgroupOf_sup (show b.first ≤ localGroup b from le_sup_left)
      (show contraryCore c ≤ localGroup b from le_sup_right)]
  change ((localGroup b).subgroupOf (localGroup b)).map (actionProjection b) = ⊤
  rw [subgroupOf_self, map_top_of_surjective _ (actionProjection_surjective b)]

/-- A representation faithful on the first image is faithful on the whole action group.
The kernel embeds into the two-group quotient and hence lies in the trivial two-core. -/
theorem faithful_of_first_restriction
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b))
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (ActionGroup b) V)
    (hf : Function.Injective (ρ.comp (faithfulImage b b.first).subtype)) :
    Function.Injective ρ := by
  have hmeet : ∀ x ∈ ρ.ker, x ∈ faithfulImage b b.first → x = 1 := by
    intro x hx hxL
    have h : (⟨x, hxL⟩ : faithfulImage b b.first) = 1 := by
      apply hf
      exact hx.trans ρ.map_one.symm
    exact congrArg Subtype.val h
  let q := QuotientGroup.mk' (faithfulImage b b.first)
  have hinj : Function.Injective (q.comp ρ.ker.subtype) := by
    apply (q.comp ρ.ker.subtype).ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    exact hmeet x x.property ((QuotientGroup.eq_one_iff (x := (x : ActionGroup b))).mp hx)
  have hp : IsPGroup 2 ρ.ker :=
    (actionGroup_quotient_first_isPGroup b).of_injective (q.comp ρ.ker.subtype) hinj
  have hle : ρ.ker ≤ pCore 2 (ActionGroup b) := le_sSup ⟨inferInstance, hp⟩
  rw [actionGroup_pCore_eq_bot b hker] at hle
  exact ρ.ker_eq_bot_iff.mp (bot_unique hle)

/-- An ambient subgroup normalized by D gives an invariant binary subspace of V. -/
private def ambientSpace (H : Subgroup G)
    (hH : localGroup b ≤ normalizer (H : Set G)) : Subrepresentation (representation b) where
  toSubmodule := AddSubgroup.toZModSubmodule 2
    (H.comap ((localGroup b).subtype.comp (intrinsicModule b).subtype)).toAddSubgroup
  apply_mem_toSubmodule g := by
    obtain ⟨x, rfl⟩ := actionProjection_surjective b g
    intro v hv
    change (((representation b (actionProjection b x) v).toMul : localGroup b) : G) ∈ H
    rw [representation_apply]
    exact (mem_normalizer_iff.mp (hH x.property) _).mp hv

/-- The binary subspace cut out by the ambient block layer U(K₁). -/
def naturalUpper : Subrepresentation (representation b) :=
  ambientSpace b (FieldFourCentrality.firstLayer b) (localGroup_normalizes_firstLayer b)

/-- The binary subspace cut out by U(K₁) ∩ Z(K₁). -/
def naturalLower : Subrepresentation (representation b) :=
  ambientSpace b ((ChapterC.blockU b.first ⊓ center b.first).map b.first.subtype)
    ((localGroup_normalizes_first b).trans
      (normalizer_le_normalizer_characteristic_image b.first
        (ChapterC.blockU b.first ⊓ center b.first)))

/-- The central fixed layer is contained in the block layer. -/
theorem naturalLower_le_upper : naturalLower b ≤ naturalUpper b := by
  intro v hv
  exact (map_mono inf_le_left) hv

/-- The upper subspace is exactly U(K₁), with its additive group written multiplicatively. -/
def upperToBlock
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b)) :
    Multiplicative (naturalUpper b).toSubmodule ≃* ChapterC.blockU b.first where
  toFun v := ⟨⟨v.toAdd.val.toMul.val.val, by
    obtain ⟨u, hu, he⟩ := v.toAdd.property
    exact (show (u : G) = v.toAdd.val.toMul.val.val from he) ▸ u.property⟩, by
      obtain ⟨u, hu, he⟩ := v.toAdd.property
      exact (show u = ⟨v.toAdd.val.toMul.val.val, _⟩ from Subtype.ext he) ▸ hu⟩
  invFun u := Multiplicative.ofAdd ⟨Additive.ofMul
    ⟨⟨u.val.val, (show b.first ≤ localGroup b from le_sup_left) u.val.property⟩,
      firstLayer_le_omegaModule_of_kernel b hker ⟨u.val, u.property, rfl⟩⟩,
    ⟨u.val, u.property, rfl⟩⟩
  left_inv v := rfl
  right_inv u := rfl
  map_mul' v w := rfl

variable {F : Type} [Field F] [Algebra (ZMod 2) F]
variable (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b))
variable (m : ChapterC.BlockModuleModel b.first (Matrix.SL2.naturalAction F))

/-- Quotient by the intrinsic fixed subgroup, followed by the given model coordinates. -/
private def upperCoordinatesHom :
    Multiplicative (naturalUpper b).toSubmodule →* Multiplicative (Fin 2 → F) :=
  m.moduleIso.toMonoidHom.comp
    ((QuotientGroup.mk' (ChapterC.blockFixed b.first)).comp
      (upperToBlock b hker).toMonoidHom)

/-- The model coordinates on the upper binary subspace are binary linear. -/
def upperCoordinates : (naturalUpper b).toSubmodule →ₗ[ZMod 2] (Fin 2 → F) :=
  ({ toFun v := (upperCoordinatesHom b hker m (Multiplicative.ofAdd v)).toAdd
     map_zero' := (upperCoordinatesHom b hker m).map_one
     map_add' v w := (upperCoordinatesHom b hker m).map_mul
       (Multiplicative.ofAdd v) (Multiplicative.ofAdd w) } :
    (naturalUpper b).toSubmodule →+ (Fin 2 → F)).toZModLinearMap 2

/-- Every natural vector is represented by an element of the actual upper subspace. -/
theorem upperCoordinates_surjective : Function.Surjective (upperCoordinates b hker m) := by
  intro v
  obtain ⟨u, hu⟩ := m.moduleIso.surjective (Multiplicative.ofAdd v)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (ChapterC.blockFixed b.first) u
  refine ⟨((upperToBlock b hker).symm w).toAdd, ?_⟩
  change (m.moduleIso (QuotientGroup.mk' _
    ((upperToBlock b hker) ((upperToBlock b hker).symm w)))).toAdd = v
  rw [MulEquiv.apply_symm_apply, hu]
  rfl

/-- The coordinate map kills precisely the actual central fixed layer. -/
theorem upperCoordinates_ker :
    LinearMap.ker (upperCoordinates b hker m) =
      (sectionLower (representation b) (naturalLower b) (naturalUpper b)).toSubmodule := by
  ext v
  change (m.moduleIso (QuotientGroup.mk' _
    (upperToBlock b hker (Multiplicative.ofAdd v)))).toAdd = 0 ↔
      v.val.toMul.val.val ∈ (ChapterC.blockU b.first ⊓ center b.first).map b.first.subtype
  change m.moduleIso (QuotientGroup.mk' _
    (upperToBlock b hker (Multiplicative.ofAdd v))) = 1 ↔ _
  rw [m.moduleIso.map_eq_one_iff]
  change _ ∈ (QuotientGroup.mk' (ChapterC.blockFixed b.first)).ker ↔ _
  rw [QuotientGroup.ker_mk']
  constructor
  · intro hv
    exact ⟨(upperToBlock b hker (Multiplicative.ofAdd v)).val,
      ⟨(upperToBlock b hker (Multiplicative.ofAdd v)).property, hv⟩, rfl⟩
  · rintro ⟨u, hu, he⟩
    have he' : u = (upperToBlock b hker (Multiplicative.ofAdd v)).val := Subtype.ext he
    change (upperToBlock b hker (Multiplicative.ofAdd v)).val ∈ center b.first
    exact he' ▸ hu.2

/-- The first isomorphism theorem identifies the literal linear section with the natural plane. -/
def sectionModuleIso :
    ((naturalUpper b).toSubmodule ⧸
      (sectionLower (representation b) (naturalLower b) (naturalUpper b)).toSubmodule)
        ≃ₗ[ZMod 2] (Fin 2 → F) :=
  (Submodule.quotEquivOfEq _ _ (upperCoordinates_ker b hker m).symm).trans
    ((upperCoordinates b hker m).quotKerEquivOfSurjective
      (upperCoordinates_surjective b hker m))

/-- The quotient equivalence evaluates on a representative using the given block model. -/
theorem sectionModuleIso_mk (v : (naturalUpper b).toSubmodule) :
    sectionModuleIso b hker m
      ((sectionLower (representation b) (naturalLower b) (naturalUpper b)).toSubmodule.mkQ v) =
        upperCoordinates b hker m v := by
  simp only [sectionModuleIso, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
    Submodule.mkQ_apply]

/-- The first-image isomorphism uses the group isomorphism from the same block model. -/
def sectionFirstIso :
    faithfulImage b b.first ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
  (firstQuotientEquiv b hker).symm.trans m.quotientIso

omit [Algebra (ZMod 2) F] in
/-- An element of K₁ has the same matrix in the model and in the first action image. -/
theorem sectionFirstIso_projection (l : b.first) :
    sectionFirstIso b hker m (firstProjection b l) =
      m.quotientIso (QuotientGroup.mk' (pCore 2 b.first) l) := by
  rw [← firstQuotientEquiv_mk b hker]
  exact congrArg m.quotientIso ((firstQuotientEquiv b hker).symm_apply_apply _)

/-- The upper-subspace action is the intrinsic block conjugation action. -/
theorem upperToBlock_conjugate (l : b.first) (v : (naturalUpper b).toSubmodule) :
    upperToBlock b hker (Multiplicative.ofAdd
      ((naturalUpper b).toRepresentation (firstProjection b l) v)) =
      ChapterC.blockConjugate b.first l
        (upperToBlock b hker (Multiplicative.ofAdd v)) := by
  apply Subtype.ext
  apply Subtype.ext
  change (((representation b (actionProjection b
    ⟨l, (show b.first ≤ localGroup b from le_sup_left) l.property⟩) v.val).toMul
    : localGroup b) : G) = _
  rw [representation_apply]
  rfl

/-- The two identifications intertwine the actual first-image action and matrix multiplication. -/
theorem section_intertwining (g : faithfulImage b b.first) v :
    sectionModuleIso b hker m
      (sectionRepresentation (representation b) (naturalLower b) (naturalUpper b) g v) =
      Matrix.mulVec (sectionFirstIso b hker m g).val (sectionModuleIso b hker m v) := by
  obtain ⟨l, rfl⟩ := firstProjection_surjective b g
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change sectionModuleIso b hker m
      ((sectionLower (representation b) (naturalLower b) (naturalUpper b)).toSubmodule.mkQ
        ((naturalUpper b).toRepresentation (firstProjection b l) v)) =
      Matrix.mulVec (sectionFirstIso b hker m (firstProjection b l)).val
        (sectionModuleIso b hker m
          ((sectionLower (representation b) (naturalLower b) (naturalUpper b)).toSubmodule.mkQ v))
    rw [sectionModuleIso_mk, sectionModuleIso_mk,
      sectionFirstIso_projection]
    change (m.moduleIso (QuotientGroup.mk' _
      (upperToBlock b hker (Multiplicative.ofAdd
        ((naturalUpper b).toRepresentation (firstProjection b l) v))))).toAdd = _
    rw [upperToBlock_conjugate, m.intertwining]
    rfl

include hker m in
/-- Faithfulness of matrix multiplication on the first image forces faithfulness on the whole section. -/
theorem naturalSection_faithful :
    Function.Injective
      (sectionRepresentation (representation b) (naturalLower b) (naturalUpper b)) := by
  apply faithful_of_first_restriction b hker
  intro g h he
  apply (sectionFirstIso b hker m).injective
  apply Matrix.SpecialLinearGroup.toLin'_injective
  ext v : 1
  obtain ⟨w, rfl⟩ := (sectionModuleIso b hker m).surjective v
  have hw := congrArg (fun f => sectionModuleIso b hker m (f w)) he
  exact (section_intertwining b hker m g w).symm.trans
    (hw.trans (section_intertwining b hker m h w))

/-- Construct all fields of the natural section from one specified block module model. -/
def naturalSectionOfModel : NaturalSection b F where
  lower := naturalLower b
  upper := naturalUpper b
  lower_le_upper := naturalLower_le_upper b
  moduleIso := sectionModuleIso b hker m
  faithful := naturalSection_faithful b hker m
  firstIso := sectionFirstIso b hker m
  intertwining := section_intertwining b hker m

end NaturalSectionConstruction

/-- A genuine faithful natural section exists over the field supplied by the block type,
with all three field, finiteness, and binary-algebra instances retained in the witness. -/
theorem exists_naturalSection
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : Algebra (ZMod 2) F),
      Nat.card F = 2 ^ b.n ∧ Nonempty (NaturalSection b F) := by
  obtain ⟨F, hF, hfin, hchar, hcard, _, ⟨m⟩⟩ := even_block_model b.model
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  exact ⟨F, hF, hfin, inferInstance, hcard, ⟨NaturalSectionConstruction.naturalSectionOfModel b hker m⟩⟩

end
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.ThompsonImage
