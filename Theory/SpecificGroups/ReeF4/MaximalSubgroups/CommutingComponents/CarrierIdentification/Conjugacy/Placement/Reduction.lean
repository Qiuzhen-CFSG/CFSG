module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification.Conjugacy.Geometry
public import Theory.GroupTheory.CComponent.LayerTransport

/-!
# The semisimple subgroup normalized by a Ree maximal subgroup

For a radical-free subgroup M, take the ambient images of all its C-components.
They are nonabelian simple and pairwise commute. Their join is the image of the
characteristic C-component layer of M, so M normalizes this join. Distinct
supplied components give two distinct members of the family. This construction
uses relative subnormality in M throughout; it does not make an individual
component, or the originally supplied pair, normal in M.

The remaining recognition problem concerns the normalizer of such a semisimple
subgroup. Its two possible targets are concrete: the Suzuki pair of `Geometry`
and the linear pair defined below using the fixed outer-node Levi and the word
rᵦ rₐ rᵦ. A second, independent problem places the full linear-pair normalizer
strictly inside a proper overgroup. The source constructs that overgroup by
adjoining the root groups U₇ and U₉, obtaining a symplectic group.

Source: Malle, *The maximal subgroups of ²F₄(q²)*, J. Algebra 139 (1991),
52–69, DOI 10.1016/0021-8693(91)90283-E, §2.2 and Proposition 2.3.
The printed proposition concerns isomorphic simple factors. Our component
hypotheses do not supply that restriction, so the recognition obligation below
must also establish the necessary local restrictions on arbitrary commuting
simple factors. The CFSG-dependent catalogue of §2.1 is not used here.

Neither recognition nor the strict proper overgroup is proved in this module.
The linear definitions do not assert any matrix-group identification or
normalizer structure. Only the strict proper overgroup is needed for exclusion;
its order and an abstract symplectic identification are not assembly inputs.
-/

@[expose] public section

namespace ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification

open Subgroup
open ReeF4.Parabolics.Binary.FixedGeometry
open ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration

/-- The fixed intersection of the full signed outer-node A₁ × A₁ Levi. -/
noncomputable def standardLinearLevi (m : ℕ) : Subgroup (Model m) :=
  (splitLevi m .linear).subgroupOf (fixedSubgroup m)

/-- The specified word rᵦ rₐ rᵦ from the linear-product construction. -/
noncomputable def linearFactorSwap (m : ℕ) : Model m :=
  weylLift m .suzuki * weylLift m .linear * weylLift m .suzuki

/-- The actual conjugate of the outer-node fixed Levi by the specified word. -/
noncomputable def companionLinearLevi (m : ℕ) : Subgroup (Model m) :=
  (standardLinearLevi m).map (MulAut.conj (linearFactorSwap m)).toMonoidHom

/-- The concrete join used in the linear alternative. -/
noncomputable def linearLeviPair (m : ℕ) : Subgroup (Model m) :=
  standardLinearLevi m ⊔ companionLinearLevi m

/-- The full ambient normalizer, not an assumed wreath-product model. -/
noncomputable def linearLeviPairNormalizer (m : ℕ) : Subgroup (Model m) :=
  normalizer (linearLeviPair m : Set (Model m))

/-- Intrinsic conditions on a family of at least two commuting nonabelian
simple subgroups. No normality in the Ree group or common isomorphism type
is imposed. Finiteness follows from finiteness of `Model m`. -/
def IsCommutingSimpleFamily {m : ℕ} (F : Set (Subgroup (Model m))) : Prop :=
  (∀ A ∈ F, IsSimpleGroup A ∧ ¬ IsMulCommutative A) ∧
    F.Pairwise (fun A B => ⁅A, B⁆ = ⊥) ∧
      ∃ A ∈ F, ∃ B ∈ F, A ≠ B

/-- The ambient images of all C-components of the supplied subgroup. -/
def componentFamily {m : ℕ} (M : Subgroup (Model m)) : Set (Subgroup (Model m)) :=
  (fun L : Subgroup M => L.map M.subtype) '' {L | L.IsCComponent}

/-- The generated family is precisely the image of the relative component layer. -/
theorem sSup_componentFamily {m : ℕ} (M : Subgroup (Model m)) :
    sSup (componentFamily M) = (cComponentLayer M).map M.subtype := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro A ⟨L, hL, rfl⟩
    exact map_mono (le_cComponentLayer hL)
  · apply map_le_iff_le_comap.mpr
    refine sSup_le fun L hL => ?_
    exact map_le_iff_le_comap.mp (le_sSup ⟨L, hL, rfl⟩)

/-- Characteristicity of the layer supplies the required relative normalization. -/
theorem le_normalizer_componentFamily {m : ℕ} (M : Subgroup (Model m)) :
    M ≤ normalizer (sSup (componentFamily M) : Subgroup (Model m)) := by
  rw [sSup_componentFamily]
  let := cComponentLayer_characteristic (G := M)
  have hn := le_normalizer_map (H := cComponentLayer M) M.subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn

/-- Radical-freeness constructs all the family hypotheses. The supplied pair
need only be distinct: its commutation follows from the same component theorem. -/
theorem componentFamily_isCommutingSimpleFamily {m : ℕ} {M : Subgroup (Model m)}
    (hR : solvableRadical M = ⊥) {L K : Subgroup M}
    (hL : L.IsCComponent) (hK : K.IsCComponent) (hne : L ≠ K) :
    IsCommutingSimpleFamily (componentFamily M) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro A ⟨D, hD, rfl⟩
    let := hD.isSimpleGroup_of_solvableRadical_eq_bot hR
    let := hD.perfect
    let := (equivMapOfInjective D M.subtype M.subtype_injective).symm.isSimpleGroup
    let := Group.IsPerfect.map (H := D) M.subtype
    exact ⟨inferInstance, Group.IsPerfect.not_isMulCommutative _⟩
  · rintro A ⟨D, hD, rfl⟩ B ⟨E, hE, rfl⟩ hDE
    rw [← map_commutator, hD.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hE
      (fun h => hDE (congrArg (fun S => S.map M.subtype) h)), Subgroup.map_bot]
  · exact ⟨L.map M.subtype, ⟨L, hL, rfl⟩, K.map M.subtype, ⟨K, hK, rfl⟩,
      fun h => hne (map_injective M.subtype_injective h)⟩

/-- Remaining local recognition, before maximality. It must bound the full
normalizer of the generated family, not merely place its simple factors.
The arbitrary-factor case is part of the obligation, not a consequence of
the isomorphic-factor wording of the printed Proposition 2.3. -/
def SemisimpleNormalizerRecognition : Prop :=
  ∀ m, 1 ≤ m → ∀ F : Set (Subgroup (Model m)), IsCommutingSimpleFamily F →
    ∃ g : Model m,
      (normalizer (sSup F : Subgroup (Model m))).map (MulAut.conj g).toMonoidHom ≤
          suzukiLeviPairNormalizer m ∨
        (normalizer (sSup F : Subgroup (Model m))).map (MulAut.conj g).toMonoidHom ≤
          linearLeviPairNormalizer m

/-- The geometric exclusion input: a strict overgroup of the full linear-pair
normalizer which is still proper in the Ree group. -/
def LinearPairProperOvergroup : Prop :=
  ∀ m, 1 ≤ m → ∃ H : Subgroup (Model m),
    linearLeviPairNormalizer m < H ∧ H ≠ ⊤

end ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification
