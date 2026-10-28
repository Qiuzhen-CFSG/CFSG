module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.Annihilator
public import Theory.Representation.BinaryTransvectionGroups.Duality

/-!
# Inputs to quintet duality

These interfaces retain the precise cocode chief factors and full center
transvection action of H.15.4(1--2). The five-dimensional module is marked by
an actual group isomorphism with K, intertwining Q-conjugation. Its
indecomposability and one earlier inner-involution displacement are separate
H.14 inputs. No code fixed space, code action image, or code/K marking is an
input. The source assembly must construct these cocode and earlier data.

Source: Aschbacher--Smith, H.14.3(2), H.14.4(2--3), H.15.4(1--2), and
H.16.3(1--3), printed pp.397--400,403, manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
namespace MathieuCode.M22Quintet.DualAction

/-- The actual cocode chief flag, expressed as covers in the lattice of
Q-invariant subspaces. The dimensions alone would not assert chiefness. -/
structure CocodeFlag where
  one : Subrepresentation cocodeAction
  two : Subrepresentation cocodeAction
  one_eq : one.toSubmodule = V1
  two_eq : two.toSubmodule = V2
  chief01 : (⊥ : Subrepresentation cocodeAction) ⋖ one
  chief12 : one ⋖ two
  chief26 : two ⋖ V6Subrepresentation
  chief6top : V6Subrepresentation ⋖ (⊤ : Subrepresentation cocodeAction)
  dim1 : Module.finrank (ZMod 2) V1 = 1
  dim2 : Module.finrank (ZMod 2) V2 = 2
  dim6 : Module.finrank (ZMod 2) V6 = 6

namespace CocodeFlag

theorem one_le_six (F : CocodeFlag) : V1 ≤ V6 := by
  rw [← F.one_eq]
  exact F.chief12.le.trans F.chief26.le

theorem two_le_six (F : CocodeFlag) : V2 ≤ V6 := by
  rw [← F.two_eq]
  exact F.chief26.le

/-- The literal center V1 inside the six-dimensional cocode space. -/
def center (F : CocodeFlag) : Subrepresentation V6Subrepresentation.toRepresentation where
  toSubmodule := V1.comap V6.subtype
  apply_mem_toSubmodule g v hv := by
    change m22OuterCocodeRepresentation g.val v.val ∈ V1
    rw [← F.one_eq] at hv ⊢
    exact F.one.apply_mem_toSubmodule g hv

/-- The literal five-dimensional cocode section, with the induced Q-action. -/
abbrev middleAction (F : CocodeFlag) := F.center.quotientRepresentation

end CocodeFlag

/-- Realize a representation by actual invertible linear maps. -/
def linearAction {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) : G →* BinaryLinear.GL W :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp
    ρ.asGroupHom

@[simp] theorem linearAction_apply {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W) (g : G) (w : W) :
    linearAction ρ g w = ρ g w := rfl

/-- The intrinsic two-core is included in its actual quintet stabilizer. -/
def kernelInclusion : K →* Q := Subgroup.inclusion (Subgroup.map_subtype_le _)

/-- The actual action of K on the cocode middle term. -/
def cocodeKernelAction : K →* BinaryLinear.GL V6 :=
  (linearAction V6Subrepresentation.toRepresentation).comp kernelInclusion

/-- The actual action of K on the code quotient by the canonical annihilator. -/
def codeQuotientKernelAction : K →* BinaryLinear.GL (M22Code ⧸ V4) :=
  (linearAction V4Subrepresentation.quotientRepresentation).comp kernelInclusion

/-- The axis in H.16.3 is this literal image, not an abstract hyperplane. -/
def codeAxis : Submodule (ZMod 2) (M22Code ⧸ V4) := V9.map V4.mkQ

/-- The representation identifications and faithful full transvection assertion
of H.15.4, with an actual conjugation marking of its group module. -/
structure CocodeActionData (F : CocodeFlag) (E : Type*)
    [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E] where
  kernelAction : Representation (ZMod 2) Q E
  kernelMarking : Multiplicative E ≃* K
  kernelMarking_equivariant : ∀ (g : Q) (v : E),
    (kernelMarking (Multiplicative.ofAdd (kernelAction g v))).val =
      g.val * (kernelMarking (Multiplicative.ofAdd v)).val * g.val⁻¹
  kernel_dim : Module.finrank (ZMod 2) E = 5
  middleEquiv : (V6 ⧸ F.center.toSubmodule) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) E
  middleEquiv_equivariant : ∀ (g : Q) v,
    middleEquiv (F.middleAction g v) = kernelAction.dual g (middleEquiv v)
  quotientMap : Q →* Equiv.Perm (Fin 5)
  quotientMap_surjective : Function.Surjective quotientMap
  quotientMap_ker : quotientMap.ker = K.subgroupOf Q
  naturalQuotient : (M22Cocode ⧸ V6) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5)
  naturalQuotient_equivariant : ∀ (g : Q) v,
    naturalQuotient (V6Subrepresentation.quotientRepresentation g v) =
      BinaryPermutation.naturalRepresentation (Fin 5) (quotientMap g) (naturalQuotient v)
  centerAction_faithful : Function.Injective cocodeKernelAction
  centerAction_full : cocodeKernelAction.range = BinaryLinear.radical F.center.toSubmodule

/-- Only earlier facts needed to distinguish the commutator from a proper
subspace of V6. The complement criterion is indecomposability of the actual
five-dimensional K-module under conjugation, transported through its marking.
The displacement four is the earlier H.14.4 inner-involution datum. -/
structure EarlierInputs {F : CocodeFlag} {E : Type*}
    [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E] (D : CocodeActionData F E) : Prop where
  indecomposable : ∀ A B : Subrepresentation D.kernelAction,
    IsCompl A B → A = ⊥ ∨ B = ⊥
  involution_displacement : ∃ i : K, i.val ∈ L ∧ i ≠ 1 ∧ i ^ 2 = 1 ∧
    Module.finrank (ZMod 2)
      (LinearMap.range (m22OuterCocodeRepresentation i.val - LinearMap.id)) = 4

end MathieuCode.M22Quintet.DualAction
