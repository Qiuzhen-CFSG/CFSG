module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.SeedGeometry
public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore

/-!
# Concrete radical normalizers and compatible changes of coordinates

The line radical in SL₃(2) fixes exactly the binary plane with last
coordinate zero. Its normalizer therefore preserves that plane; conversely,
the parabolic normalizes its two-core. This identifies the full normalizer
with the line parabolic without a subgroup enumeration.

For the actual component action, the kernel is C_K(W_K). The normalizer
of the radical's full preimage maps onto the line parabolic. This full
preimage is not identified with the source Baumann subgroup here.

Simultaneously conjugating the actor and both natural summands gives a
new equivariant marking, with explicit formulas for the action and subgroup
images. Thus a later source alignment may change coordinates coherently.
The Thompson/Baumann image and the split-point construction still have to
be proved before applying `false_of_marked_seed_geometry`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 13.6.20, printed p.931.
-/

public section

open Subgroup Representation BinaryLinearThree Matrix
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry

private theorem fixed_radical_iff (v : Vector) :
    (∀ r ∈ R, (r : BinaryLinearThree.Group) • v = v) ↔ v 2 = 0 := by
  constructor
  · intro h
    have he := congrFun (h (shear (Multiplicative.ofAdd (1, 0))) ⟨_, rfl⟩) 0
    change (!![1,0,1; 0,1,0; 0,0,1].mulVec v) 0 = v 0 at he
    have hv : v 0 + v 2 = v 0 := by
      simpa [mulVec, dotProduct, Fin.sum_univ_three] using he
    exact add_left_cancel (hv.trans (add_zero (v 0)).symm)
  · intro hv r hr
    obtain ⟨c, rfl⟩ := hr
    change !![1,0,c.toAdd.1; 0,1,c.toAdd.2; 0,0,1].mulVec v = v
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, hv]

/-- The normalizer of the actual shear four-group is the full line parabolic. -/
theorem normalizer_radical :
    normalizer (R : Set BinaryLinearThree.Group) = Matrix.PSL3Two.lineParabolicSL := by
  apply le_antisymm
  · intro g hg
    rw [Matrix.PSL3Two.lineParabolicSL, MulAction.mem_stabilizer_set' (Set.toFinite _)]
    intro v hv
    apply (fixed_radical_iff _).mp
    intro r hr
    have hr' : g⁻¹ * r * g ∈ R := by
      simpa using (mem_normalizer_iff.mp ((normalizer (R : Set BinaryLinearThree.Group)).inv_mem hg) r).mp hr
    have he := (fixed_radical_iff v).mpr hv _ hr'
    have he' := congrArg (fun w : Vector => g • w) he
    simpa only [mul_smul, smul_inv_smul] using he'
  · rw [← Matrix.PSL3Two.lineParabolicSL_pCoreIn_two_eq_R]
    exact Matrix.PSL3Two.lineParabolicSL.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

variable {G : Type*} [_root_.Group G] {K L T : Subgroup G} {z v : G}
    {hK : K ≤ Gv v} {hL : Tv T v ≤ normalizer (Lv L v : Set G)}
    {hz : Tv T v ≤ centralizer ({z} : Set G)}
open ComponentSelection

/-- Embed the matrix model in the literal plus quotient using the chosen actor. -/
@[expose] noncomputable def modelEmbedding (d : DoubledCoordinates K L T z v hK hL hz) :
    BinaryLinearThree.Group →* Gplus K L T z v hL hz :=
  (plusImage K L T z v hL hz K).subtype.comp d.actor.symm.toMonoidHom

/-- Compatibility with representatives from the actual component. -/
theorem modelEmbedding_actionMap (d : DoubledCoordinates K L T z v hK hL hz)
    (k : K) :
    modelEmbedding d (d.actionMap k) =
      plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k) := by
  change (d.actor.symm (d.actor (componentPlus K L T z v hK hL hz k)) :
    Gplus K L T z v hL hz) = _
  rw [d.actor.symm_apply_apply]
  exact componentPlus_apply K L T z v hK hL hz k

/-- The embedded model is faithful, including the inclusion in the plus actor. -/
theorem modelEmbedding_injective (d : DoubledCoordinates K L T z v hK hL hz) :
    Function.Injective (modelEmbedding d) :=
  (plusImage K L T z v hL hz K).subtype_injective.comp d.actor.symm.injective

/-- The chosen matrix action kills exactly the component centralizer of W_K. -/
theorem actionMap_ker (d : DoubledCoordinates K L T z v hK hL hz) :
    d.actionMap.ker = (centralizer (WK K L T z v : Set G)).subgroupOf K := by
  ext k
  change d.actor (componentPlus K L T z v hK hL hz k) = 1 ↔ _
  rw [← d.actor.map_one, d.actor.injective.eq_iff]
  rw [Subtype.ext_iff, componentPlus_apply]
  change inclusion (K_le_plusActor K L T v) k ∈ (plusMk K L T z v hL hz).ker ↔ _
  rw [plusMk_ker]
  rfl

/-- Full inverse image in K; this is not the source Baumann subgroup. -/
@[expose] noncomputable def radicalPreimage (d : DoubledCoordinates K L T z v hK hL hz) : Subgroup K :=
  R.comap d.actionMap

/-- The normalizer of the full inverse image is the full parabolic inverse image. -/
theorem normalizer_radicalPreimage (d : DoubledCoordinates K L T z v hK hL hz) :
    normalizer (radicalPreimage d : Set K) =
      Matrix.PSL3Two.lineParabolicSL.comap d.actionMap := by
  rw [radicalPreimage, ← comap_normalizer_eq_of_surjective _ d.actionMap_surjective,
    normalizer_radical]

/-- Concrete application to the literal action map of the marked component. -/
theorem radicalPreimage_normalizer_image (d : DoubledCoordinates K L T z v hK hL hz) :
    (normalizer (radicalPreimage d : Set K)).map d.actionMap =
      Matrix.PSL3Two.lineParabolicSL := by
  rw [normalizer_radicalPreimage, map_comap_eq_self_of_surjective d.actionMap_surjective]

/-- The actual diagonal matrix action, as a multiplicative module equivalence.
Its exposed action is used by simultaneous coordinate changes. -/
@[expose] noncomputable def diagonalCoordinates (g : BinaryLinearThree.Group) :
    Multiplicative (Vector × Vector) ≃* Multiplicative (Vector × Vector) where
  toFun u := Multiplicative.ofAdd ((W.prod W) g u.toAdd)
  invFun u := Multiplicative.ofAdd ((W.prod W) g⁻¹ u.toAdd)
  left_inv u := by
    change (W.prod W) g⁻¹ ((W.prod W) g u.toAdd) = u.toAdd
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv u := by
    change (W.prod W) g ((W.prod W) g⁻¹ u.toAdd) = u.toAdd
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  map_mul' u w := by
    change (W.prod W) g (u.toAdd + w.toAdd) =
      (W.prod W) g u.toAdd + (W.prod W) g w.toAdd
    exact map_add _ _ _

/-- Change the actor and both module summands by the same matrix. -/
@[expose] noncomputable def conjugateCoordinates (d : DoubledCoordinates K L T z v hK hL hz)
    (g : BinaryLinearThree.Group) : DoubledCoordinates K L T z v hK hL hz where
  actor := d.actor.trans (MulAut.conj g)
  moduleEquiv := d.moduleEquiv.trans (diagonalCoordinates g)
  equivariant k u := by
    change Multiplicative.ofAdd ((W.prod W) g (d.moduleEquiv
      (conjugationAction _ _ (K_normalizes_UK K L T z v hL hz) k u)).toAdd) = _
    rw [d.equivariant]
    change (W.prod W) g ((W.prod W) (d.actor (componentPlus K L T z v hK hL hz k))
      (d.moduleEquiv u).toAdd) =
      (W.prod W) (g * d.actor (componentPlus K L T z v hK hL hz k) * g⁻¹)
        ((W.prod W) g (d.moduleEquiv u).toAdd)
    simp only [map_mul, Module.End.mul_apply]
    rw [← Module.End.mul_apply ((W.prod W) g⁻¹), ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]

/-- The new action map is the conjugate of the original literal map. -/
theorem conjugateCoordinates_actionMap (d : DoubledCoordinates K L T z v hK hL hz)
    (g : BinaryLinearThree.Group) :
    (conjugateCoordinates d g).actionMap = (MulAut.conj g).toMonoidHom.comp d.actionMap := rfl

/-- The same change acts diagonally on the module coordinates. -/
theorem conjugateCoordinates_moduleEquiv (d : DoubledCoordinates K L T z v hK hL hz)
    (g : BinaryLinearThree.Group) (u : UK K L T z v) :
    (conjugateCoordinates d g).moduleEquiv u =
      Multiplicative.ofAdd ((W.prod W) g (d.moduleEquiv u).toAdd) := rfl

/-- Every subgroup image follows the same actor conjugation. -/
theorem conjugateCoordinates_subgroup_image (d : DoubledCoordinates K L T z v hK hL hz)
    (g : BinaryLinearThree.Group) (H : Subgroup K) :
    H.map (conjugateCoordinates d g).actionMap =
      (H.map d.actionMap).map (MulAut.conj g).toMonoidHom := by
  rw [conjugateCoordinates_actionMap, Subgroup.map_map]

/-- A module automorphism commuting with the diagonal action changes only
module coordinates. This permits a multiplicity-space alignment without
altering any of the actor or radical images. -/
@[expose] noncomputable def changeModule (d : DoubledCoordinates K L T z v hK hL hz)
    (e : Multiplicative (Vector × Vector) ≃* Multiplicative (Vector × Vector))
    (he : ∀ g u, e (Multiplicative.ofAdd ((W.prod W) g u.toAdd)) =
      Multiplicative.ofAdd ((W.prod W) g (e u).toAdd)) :
    DoubledCoordinates K L T z v hK hL hz where
  actor := d.actor
  moduleEquiv := d.moduleEquiv.trans e
  equivariant k u := by
    change e (d.moduleEquiv
      (conjugationAction _ _ (K_normalizes_UK K L T z v hL hz) k u)) = _
    rw [d.equivariant]
    exact he _ _

/-- Multiplicity-coordinate changes leave the literal component action fixed. -/
theorem changeModule_actionMap (d : DoubledCoordinates K L T z v hK hL hz)
    (e : Multiplicative (Vector × Vector) ≃* Multiplicative (Vector × Vector))
    (he : ∀ g u, e (Multiplicative.ofAdd ((W.prod W) g u.toAdd)) =
      Multiplicative.ofAdd ((W.prod W) g (e u).toAdd)) :
    (changeModule d e he).actionMap = d.actionMap := rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry
