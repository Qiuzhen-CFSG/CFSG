module

public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Geometry
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Perfectness
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.FieldCompatibility

/-!
# The short local subgroup and geometric parabolic of split G₂

The short-Weyl local group has the five-root two-core omitting root F. Its
explicit action on the standard null plane induces an isomorphism of the
quotient by this core with PSL₂, including in the full group G₂(2). The core
is the previously constructed special group of order q⁵ and center order q.
The quotient map is compatible with the root coordinates and with coefficient
field automorphisms.

The Borel normalizes the local group, and their literal product is the full
null-plane stabilizer. Its intersection with the long point parabolic is
exactly the Borel. Local torus and root commutators prove perfectness for
q > 2. The common Sylow subgroup is already contained in the local group,
so adjoining it leaves both the group and its core unchanged.

Source: Aschbacher--Smith, F.1.12(I)(3) and (II), printed pp. 262--264.
These are the short-local model calculations; the source classification and
amalgam assembly remain with the Chapter F consumer.
-/

public section
open scoped Pointwise
namespace Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2]

/-- Relative normality in the short parabolic. -/
theorem parabolic₁_normalizes_local₁ :
    parabolic₁ (F := F) ≤ Subgroup.normalizer (local₁ (F := F) : Set (Model F)) := by
  rw [← local₁_sup_borel]
  exact sup_le local₁.le_normalizer borel_normalizes_local₁

instance local₁_normal_in_parabolic₁ :
    ((local₁ (F := F)).subgroupOf parabolic₁).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer parabolic₁_normalizes_local₁

variable [Finite F]

theorem local₁_pCoreIn : (local₁ (F := F)).pCoreIn 2 = radical₁ := local₁_pCore

theorem sylow_le_local₁ : (sylow (F := F) : Subgroup (Model F)) ≤ local₁ :=
  unipotent_le_local₁

theorem local₁_sup_sylow :
    local₁ (F := F) ⊔ (sylow (F := F) : Subgroup (Model F)) = local₁ :=
  sup_eq_left.mpr sylow_le_local₁

/-- The source product `L₁ S` as a literal set product. -/
theorem local₁_mul_sylow :
    (local₁ (F := F) : Set (Model F)) *
      ((sylow (F := F) : Subgroup (Model F)) : Set (Model F)) =
        (local₁ (F := F) : Set (Model F)) := by
  ext g
  constructor
  · rintro ⟨l,hl,s,hs,rfl⟩
    exact local₁.mul_mem hl (sylow_le_local₁ hs)
  · intro hg
    exact ⟨g,hg,1,(sylow (F := F)).one_mem,mul_one g⟩

/-- The source core of the local group with the common Sylow adjoined. -/
theorem local₁_sylow_pCoreIn :
    (local₁ (F := F) ⊔ (sylow (F := F) : Subgroup (Model F))).pCoreIn 2 = radical₁ := by
  rw [local₁_sup_sylow,local₁_pCoreIn]

noncomputable def local₁SylowCoreEquivRadical :
    pCore 2 (local₁ (F := F) ⊔ (sylow (F := F) : Subgroup (Model F)) :
      Subgroup (Model F)) ≃* radical₁ (F := F) := by
  rw [local₁_sup_sylow]
  exact local₁CoreEquivRadical

theorem card_local₁_sylow_pCore :
    Nat.card (pCore 2 (local₁ (F := F) ⊔ (sylow (F := F) : Subgroup (Model F)) :
      Subgroup (Model F))) = Nat.card F ^ 5 := by
  rw [local₁_sup_sylow,card_local₁_pCore]

/-- At the binary parameter this is the order-32 core inside full G₂(2). -/
theorem card_local₁_pCore_binary :
    Nat.card (pCore 2 (local₁ (F := ZMod 2))) = 32 := by
  rw [card_local₁_pCore]
  norm_num

noncomputable def local₁BinaryCoreQuotientEquivPSL :
    local₁ (F := ZMod 2) ⧸ pCore 2 (local₁ (F := ZMod 2)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) := local₁CoreQuotientEquivPSL

end Atlas.G2.LieParabolicSetup
