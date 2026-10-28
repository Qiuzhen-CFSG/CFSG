module

public import Theory.AtlasPort.LinearGroups.G2.LieBinaryCompatibility
public import Theory.AtlasPort.LinearGroups.G2.LieCoreSpecialness
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions
public import Theory.GroupTheory.Amalgam.RankTwoTransport

/-!
# The concrete G₂ alternative of F.1.12

Both inclusions below are taken inside the full split-octonion automorphism
model. The middle group is the whole intersection, and the positive root
subgroup supplies the common Sylow marking. The two local groups are kept
separate from the torus-extended parabolics.

The root pair is compatibly isomorphic to the actual null-plane/point
stabilizer amalgam, with Borel as whole overlap. Both local two-core
quotients are the actual PSL₂(F). The first core is special of order q⁵
with center order q; the second has order q⁵. The first local centralizes
the whole Sylow center, fixing the source numbering. These are assembled
in `source_I_3`, including q = 2 in full G₂(2) of order 12096.

For q > 2 both locals equal their solvable residuals. The imported
automorphism theorem identifies the full automorphism group with genuine
inner and coefficientwise field actions. The concrete field-extension core
and quotient-action theorems have all local-map premises discharged here.
At q = 2 conjugation identifies the full model with Aut(G₂(2)′), excluding
a further faithful extension; `binaryExtensionIso` retains the whole marked
amalgam. Recognition of an arbitrary weak BN-pair and elimination of its
q > 2 extension remain with the higher source assembly.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.11--12, printed pp. 262--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2

open Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped Pointwise MatrixGroups
variable {F : Type*} [Field F]

/-- The whole intersection of the two root-defined parabolics. -/
def overlap : Subgroup (Model F) := parabolic₁ ⊓ parabolic₂

/-- The compatible inclusion amalgam, using the whole actual overlap. -/
def amalgam : RankTwoAmalgam (parabolic₁ (F := F))
    (overlap (F := F)) (parabolic₂ (F := F)) where
  left := Subgroup.inclusion (show overlap (F := F) ≤ parabolic₁ from inf_le_left)
  right := Subgroup.inclusion (show overlap (F := F) ≤ parabolic₂ from inf_le_right)

theorem left_injective : Function.Injective (amalgam (F := F)).left :=
  Subgroup.inclusion_injective (show overlap (F := F) ≤ parabolic₁ from inf_le_left)

theorem right_injective : Function.Injective (amalgam (F := F)).right :=
  Subgroup.inclusion_injective (show overlap (F := F) ≤ parabolic₂ from inf_le_right)

theorem borel_le_overlap : borel (K := F) ≤ parabolic₁ ⊓ parabolic₂ :=
  le_inf borel_le_parabolic₁ borel_le_parabolic₂

theorem sylow_le_overlap [Finite F] [CharP F 2] :
    (sylow (F := F) : Subgroup (Model F)) ≤ parabolic₁ ⊓ parabolic₂ :=
  sylow_le_borel.trans borel_le_overlap

/-- The binary specialization uses G₂(2) of order 12096. -/
theorem card_full_binary_model : Nat.card (Model (ZMod 2)) = 12096 := by
  rw [card_Model, Nat.card_eq_fintype_card, ZMod.card]
  norm_num

/-- The whole overlap is the Borel for every field parameter. -/
theorem overlap_eq_borel : overlap (F := F) = borel := parabolics_intersection

/-- The source's middle group is the full Borel. -/
def borelAmalgam : RankTwoAmalgam (parabolic₁ (F := F))
    (borel (K := F)) (parabolic₂ (F := F)) :=
  RankTwoAmalgam.ofSubgroups _ _ _ borel_le_parabolic₁ borel_le_parabolic₂

/-- Identifying the overlap with B preserves both inclusion maps. -/
def borelIso : RankTwoAmalgam.Iso (amalgam (F := F)) (borelAmalgam (F := F)) where
  left := MulEquiv.refl _
  middle := MulEquiv.subgroupCongr overlap_eq_borel
  right := MulEquiv.refl _
  left_commutes _ := by apply Subtype.ext; rfl
  right_commutes _ := by apply Subtype.ext; rfl

/-- The standard incident geometric stabilizers in the actual octonion model. -/
def geometricAmalgam : RankTwoAmalgam (shortPlaneStabilizer (F := F))
    (shortPlaneStabilizer (F := F) ⊓ pointStabilizer : Subgroup (Model F))
    (pointStabilizer (K := F)) :=
  RankTwoAmalgam.ofSubgroups _ _ _ inf_le_left inf_le_right

/-- The same ambient identity identifies both parabolics and their whole overlap. -/
def geometricIso : RankTwoAmalgam.Iso (amalgam (F := F)) (geometricAmalgam (F := F)) where
  left := MulEquiv.subgroupCongr parabolic₁_eq_shortPlaneStabilizer
  middle := MulEquiv.subgroupCongr (show overlap (F := F) =
      shortPlaneStabilizer ⊓ pointStabilizer by
    change parabolic₁ ⊓ parabolic = _
    rw [parabolic₁_eq_shortPlaneStabilizer, parabolic_eq_pointStabilizer])
  right := MulEquiv.subgroupCongr parabolic_eq_pointStabilizer
  left_commutes _ := by apply Subtype.ext; rfl
  right_commutes _ := by apply Subtype.ext; rfl

variable [CharP F 2]

/-- The source parabolics are literal products with B, with separate locals. -/
theorem parabolic_products :
    (parabolic₁ (F := F) : Set (Model F)) =
      (local₁ (F := F) : Set (Model F)) * (borel (K := F) : Set (Model F)) ∧
    (parabolic₂ (F := F) : Set (Model F)) =
      (local₂ (F := F) : Set (Model F)) * (borel (K := F) : Set (Model F)) :=
  ⟨parabolic₁_eq_local₁_mul_borel, parabolic₂_eq_local₂_mul_borel⟩

variable [Finite F]

/-- The common ambient Sylow subgroup restricted to the entire overlap. -/
def overlapSylow : Sylow 2 (overlap (F := F)) :=
  (sylow (F := F)).subtype sylow_le_overlap

def leftSylow : Sylow 2 (parabolic₁ (F := F)) :=
  (sylow (F := F)).subtype (sylow_le_borel.trans borel_le_parabolic₁)

def rightSylow : Sylow 2 (parabolic₂ (F := F)) :=
  (sylow (F := F)).subtype (sylow_le_borel.trans borel_le_parabolic₂)

/-- The two inclusion maps preserve the same Sylow marking. -/
theorem sylow_marking :
    (overlapSylow (F := F) : Subgroup (overlap (F := F))).map (amalgam (F := F)).left =
      (leftSylow (F := F) : Subgroup (parabolic₁ (F := F))) ∧
    (overlapSylow (F := F) : Subgroup (overlap (F := F))).map (amalgam (F := F)).right =
      (rightSylow (F := F) : Subgroup (parabolic₂ (F := F))) := by
  constructor
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x.val, sylow_le_overlap hx⟩, hx, Subtype.ext rfl⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x.val, sylow_le_overlap hx⟩, hx, Subtype.ext rfl⟩

/-- LᵢS is already Lᵢ, as a literal product as well as a subgroup join. -/
theorem local_sylow_products :
    (local₁ (F := F) : Set (Model F)) * (sylow (F := F) : Set (Model F)) =
      (local₁ (F := F) : Set (Model F)) ∧
    (local₂ (F := F) : Set (Model F)) * (sylow (F := F) : Set (Model F)) =
      (local₂ (F := F) : Set (Model F)) :=
  ⟨local₁_mul_sylow, local₂_mul_sylow⟩

/-- F.1.12(I)(3) for the concrete full G₂ model, with the complete special-group
meaning of q^(1+4) from F.1.11 and the prescribed Sylow-center numbering. -/
theorem source_I_3 :
    let Q := pCore 2 (local₁ (F := F) ⊔ (sylow (F := F) : Subgroup (Model F)) :
      Subgroup (Model F))
    Nonempty (RankTwoAmalgam.Iso (amalgam (F := F)) (geometricAmalgam (F := F))) ∧
    Nonempty (local₁ (F := F) ⧸ pCore 2 (local₁ (F := F)) ≃* PSL(2,F)) ∧
    Nonempty (local₂ (F := F) ⧸ pCore 2 (local₂ (F := F)) ≃* PSL(2,F)) ∧
    (IsPGroup 2 Q ∧ commutator Q ≠ ⊥ ∧
      commutator Q = Subgroup.center Q ∧ frattini Q = Subgroup.center Q ∧
      IsElementaryAbelian 2 (Subgroup.center Q) ∧
      Nat.card Q = Nat.card F ^ 5 ∧ Nat.card (Subgroup.center Q) = Nat.card F) ∧
    Nat.card (pCore 2 (local₂ (F := F) ⊔ (sylow (F := F) : Subgroup (Model F)) :
      Subgroup (Model F))) = Nat.card F ^ 5 ∧
    ⁅local₁ (F := F),
      (Subgroup.center (sylow (F := F) : Subgroup (Model F))).map
        (sylow (F := F) : Subgroup (Model F)).subtype⁆ = ⊥ :=
  ⟨⟨geometricIso⟩, ⟨local₁CoreQuotientEquivPSL⟩, ⟨local₂CoreQuotientEquivPSL⟩,
    local₁_sylow_pCore_special, card_local₂_sylow_pCore, local₁_commutator_sylow_center⟩

/-- The nonbinary case has precisely the residual and Sylow conclusions of F.1.12(II)(i). -/
theorem source_II_i (hq : 2 < Nat.card F) :
    (Subgroup.solvableResidual (local₁ (F := F))).map (local₁ (F := F)).subtype = local₁ ∧
    (Subgroup.solvableResidual (local₂ (F := F))).map (local₂ (F := F)).subtype = local₂ ∧
    (sylow (F := F) : Subgroup (Model F)) ≤ local₁ ∧
    (sylow (F := F) : Subgroup (Model F)) ≤ local₂ :=
  ⟨local₁_map_solvableResidual hq, local₂_map_solvableResidual hq,
    sylow_le_local₁, sylow_le_local₂⟩

open Atlas.G2.LieAutomorphismExtensions

/-- The two field extensions use the actual locals and preserve their intrinsic two-cores.
The source's faithful two-group actors are included among these finite actors. -/
theorem field_extension_cores {A : Type*} [Group A] [Finite A]
    (σ : A →* (F ≃+* F)) (hσ : Function.Injective σ) :
    pCore 2 ((local₁ (F := F)) ⋊[shortFieldAction.comp σ] A) =
      (pCore 2 (local₁ (F := F))).map SemidirectProduct.inl ∧
    pCore 2 ((local₂ (F := F)) ⋊[longFieldAction.comp σ] A) =
      (pCore 2 (local₂ (F := F))).map SemidirectProduct.inl := by
  rw [local₁_intrinsic_pCore, local₂_pCore]
  exact ⟨shortFieldExtension_twoCore σ hσ, longFieldExtension_twoCore σ hσ⟩

omit [Finite F] in
/-- Inner action on either concrete PSL₂ quotient kills the extending field component.
Both quotient maps and their equivariance are the proved root representations. -/
theorem field_extension_inner {A : Type*} [Group A]
    (σ : A →* (F ≃+* F)) (hσ : Function.Injective σ) :
    (∀ z : (local₁ (F := F)) ⋊[shortFieldAction.comp σ] A,
      (∃ g : PSL(2,F), localQuotientAction shortPSLHom (shortFieldAction.comp σ) σ
        (fun a x => shortPSLHom_field (σ a) x) z = MulAut.conj g) ↔ z.right = 1) ∧
    (∀ z : (local₂ (F := F)) ⋊[longFieldAction.comp σ] A,
      (∃ g : PSL(2,F), localQuotientAction longPSLHom (longFieldAction.comp σ) σ
        (fun a x => longPSLHom_field (σ a) x) z = MulAut.conj g) ↔ z.right = 1) :=
  ⟨shortFieldExtension_inner_iff σ hσ, longFieldExtension_inner_iff σ hσ⟩

/-- No further faithful binary extension changes the full marked amalgam. The
isomorphisms on all three groups are restrictions of the original embedding. -/
noncomputable def binaryExtensionIso {E : Type*} [Group E]
    (j : Model (ZMod 2) →* E) (a : E →* MulAut BinaryDerived)
    (ha : Function.Injective a) (haj : a.comp j = binaryConjugation)
    (P : Fin 2 → Subgroup E)
    (hP : ∀ i, (P i).comap j = if i = 0 then parabolic₁ else parabolic₂) :
    RankTwoAmalgam.Iso (amalgam (F := ZMod 2))
      (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right) := by
  have hj := binaryExtension_embedding_bijective j a ha haj
  obtain ⟨hp, hb⟩ := binaryExtension_marked_eq j a ha haj P hP
  have h₀ : P 0 = parabolic₁.map j := by simpa using hp 0
  have h₁ : P 1 = parabolic₂.map j := by simpa using hp 1
  let e := RankTwoAmalgam.ofSubgroupsMapIso j hj.1
    parabolic₁ (overlap (F := ZMod 2)) parabolic₂ inf_le_left inf_le_right
  refine {
    left := e.left.trans (MulEquiv.subgroupCongr h₀.symm)
    middle := e.middle.trans (MulEquiv.subgroupCongr hb.symm)
    right := e.right.trans (MulEquiv.subgroupCongr h₁.symm)
    left_commutes := ?_
    right_commutes := ?_ }
  · intro b
    apply Subtype.ext
    rfl
  · intro b
    apply Subtype.ext
    rfl

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2
