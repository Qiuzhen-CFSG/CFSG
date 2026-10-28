module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.ModuleCases
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Modules
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Structure

/-!
# Pulling a point parabolic back to the original component

The subgroup is the actual preimage under L → L/O₂(L) ≃ L₄(2) ≃ GL₄(2).
Its action is onto the full point stabilizer and uses the given natural-plus-dual
coordinates on U_L. Displacements lie in Q_P = [O₂(P),P] once U_L ≤ O₂(P).
Relative normalization transports the old component core into the parabolic core;
elementarity of W_L supplies the required core containment for U_L.
No central extension of W_L is removed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130 (PDF pp.1146–1147).
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic

variable {G : Type*} [Group G] {d : LocalData G} {L : Subgroup G}

/-- The actual point parabolic, pulled back to the original component. -/
noncomputable def point (h : NaturalDual d L) (x : Space 4) : Subgroup G :=
  ((pointStabilizer x).comap (linearAction (by decide) h.model)).map L.subtype

theorem point_le (h : NaturalDual d L) (x : Space 4) : point h x ≤ L := map_subtype_le _

theorem mem_point (h : NaturalDual d L) (x : Space 4) (l : L) :
    (l : G) ∈ point h x ↔ linearAction (by decide) h.model l ∈ pointStabilizer x := by
  constructor
  · rintro ⟨k, hk, he⟩
    exact (Subtype.ext he : k = l) ▸ hk
  · intro hl
    exact ⟨l, hl, rfl⟩

/-- The marked quotient action of the actual parabolic, before removing its radical. -/
noncomputable def pointActor (h : NaturalDual d L) (x : Space 4) :
    point h x →* pointStabilizer x where
  toFun p := ⟨linearAction (by decide) h.model ⟨p, point_le h x p.property⟩,
    (mem_point h x _).mp p.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' p q := by
    apply Subtype.ext
    exact (linearAction (by decide) h.model).map_mul
      (⟨p, point_le h x p.property⟩ : L) (⟨q, point_le h x q.property⟩ : L)

theorem pointActor_surjective (h : NaturalDual d L) (x : Space 4) :
    Function.Surjective (pointActor h x) := by
  intro g
  obtain ⟨l, hl⟩ := linearAction_surjective (by decide) h.model g.val
  refine ⟨⟨l, (mem_point h x l).mpr (hl ▸ g.property)⟩, ?_⟩
  apply Subtype.ext
  exact hl

/-- Coordinates embedded in the original ambient group. -/
def embed (h : NaturalDual d L) :
    Multiplicative (Space 4 × Module.Dual (ZMod 2) (Space 4)) →* G :=
  (spanCommutator d L).subtype.comp h.coordinates.symm.toMonoidHom

theorem embed_injective (h : NaturalDual d L) : Function.Injective (embed h) :=
  Subtype.val_injective.comp h.coordinates.symm.injective

theorem embed_mem (h : NaturalDual d L)
    (v : Space 4 × Module.Dual (ZMod 2) (Space 4)) :
    embed h (Multiplicative.ofAdd v) ∈ spanCommutator d L :=
  (h.coordinates.symm (Multiplicative.ofAdd v)).property

theorem embed_conj (h : NaturalDual d L) (l : L)
    (v : Space 4 × Module.Dual (ZMod 2) (Space 4)) :
    (l : G) * embed h (Multiplicative.ofAdd v) * (l : G)⁻¹ =
      embed h (Multiplicative.ofAdd
        (BinaryLinear.NaturalDualFlag.action (linearAction (by decide) h.model l) v)) := by
  have hh := h.equivariant l (h.coordinates.symm (Multiplicative.ofAdd v))
  rw [h.coordinates.apply_symm_apply] at hh
  have he := congrArg (fun w => (h.coordinates.symm (Multiplicative.ofAdd w) : G)) hh
  change (h.coordinates.symm (h.coordinates
    (commutatorAction d L l (h.coordinates.symm (Multiplicative.ofAdd v)))) : G) = _ at he
  rw [h.coordinates.symm_apply_apply, commutatorAction_apply] at he
  exact he

/-- The source subgroup Q_P, formed using the two-core rather than the residual. -/
def coreCommutator (P : Subgroup G) : Subgroup G := ⁅P.pCoreIn 2, P⁆

theorem coreCommutator_le (P : Subgroup G) : coreCommutator P ≤ P.pCoreIn 2 := by
  exact le_normalizer_iff_commutator_le_left.mp
    (P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))

/-- Every displacement in the coordinate module lies in the actual core commutator. -/
theorem displacement_mem (h : NaturalDual d L) (x : Space 4)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2)
    (g : pointStabilizer x) (v : Space 4 × Module.Dual (ZMod 2) (Space 4)) :
    embed h (Multiplicative.ofAdd (BinaryLinear.NaturalDualFlag.action g.val v - v)) ∈
      coreCommutator (point h x) := by
  obtain ⟨p, hp⟩ := pointActor_surjective h x g
  have hc := commutator_mem_commutator p.property (hU (embed_mem h v))
  rw [commutator_comm] at hc
  have he : (linearAction (by decide) h.model ⟨p, point_le h x p.property⟩) = g.val :=
    congrArg Subtype.val hp
  change ⁅(p : G), embed h (Multiplicative.ofAdd v)⁆ ∈ _ at hc
  rw [commutatorElement_def,
    embed_conj h (⟨p, point_le h x p.property⟩ : L) v, he] at hc
  simpa only [coreCommutator, ofAdd_sub, div_eq_mul_inv, map_mul, map_inv] using hc

/-- The radical of the actual parabolic acts through the geometric point radical. -/
theorem point_core_actor (h : NaturalDual d L) (x : Space 4)
    (p : point h x) (hp : p ∈ pCore 2 (point h x)) :
    pointActor h x p ∈ pointKernel x := by
  have hn : ((pCore 2 (point h x)).map (pointActor h x)).Normal :=
    Subgroup.Normal.map inferInstance _ (pointActor_surjective h x)
  have hm : (pCore 2 (point h x)).map (pointActor h x) ≤
      pCore 2 (pointStabilizer x) := le_sSup ⟨hn, pCore_isPGroup.map _⟩
  rw [point_twoCore] at hm
  exact hm (mem_map_of_mem _ hp)

/-- The old component core belongs to every pulled-back point parabolic. -/
theorem componentCore_le_point (h : NaturalDual d L) (x : Space 4) :
    L.pCoreIn 2 ≤ point h x := by
  rintro _ ⟨l, hl, rfl⟩
  apply (mem_point h x l).mpr
  have he : linearAction (by decide) h.model l = 1 := by
    unfold linearAction
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [show QuotientGroup.mk' (pCore 2 L) l = 1 from
      (QuotientGroup.eq_one_iff (N := pCore 2 L) l).mpr hl, map_one, map_one]
  rw [he]
  exact one_mem _

/-- Relative normalization places the old core in the new parabolic core. -/
theorem componentCore_le_pointCore (h : NaturalDual d L) (x : Space 4) :
    L.pCoreIn 2 ≤ (point h x).pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L) (componentCore_le_point h x)
  exact (point_le h x).trans
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))

/-- Elementarity and relative normalization put the commutator in the component core. -/
theorem spanCommutator_le_componentCore [IsElementaryAbelian 2 (d.componentSpan L)]
    (hW : d.componentSpan L ≤ normalizer (L : Set G)) :
    spanCommutator d L ≤ L.pCoreIn 2 :=
  le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 (d.componentSpan L)).to_le (spanCommutator_le_span d L))
    (le_normalizer_iff_commutator_le_right.mp hW)
    (normalizer_commutator_ge_right _ _)


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic

end
