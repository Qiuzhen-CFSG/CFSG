module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.Algebra
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.Cocycles
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# Commutator cocycles for the centralizing branch

An element centralizing Q defines a crossed homomorphism on L with values in
Z(Q)/C_Z(Q)(L). The three-subgroup lemma makes it vanish on O₂(L), so it
descends to the actual simple model quotient. The marked Y₊ fixes the actor
and hence kills its restricted cocycle. A model-specific restriction theorem
then makes all commutators central in L; perfectness eliminates them.

The quotient I⁺ is also realized faithfully in Aut(L). The terminal result
here remains conditional on the marked coefficient model and its cocycle
restriction calculation; it is not the source exclusion 15.3.31.

Source: Aschbacher--Smith, proof of 15.3.31, printed p.1132; I.1.5.
-/

@[expose] public section
open Subgroup Representation Representation.OneCohomology
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover

variable {G : Type*} [Group G]

/-- The actual conjugation action of I on its relatively normal component. -/
def componentAction (I L : Subgroup G) (hIL : I ≤ normalizer (L : Set G)) :
    I →* MulAut L :=
  letI := Subgroup.conjMulDistribMulActionOfLeNormalizer I L hIL
  MulDistribMulAction.toMulAut I L

theorem componentAction_apply (I L : Subgroup G) (hIL : I ≤ normalizer (L : Set G))
    (i : I) (l : L) :
    (componentAction I L hIL i l : G) = (i : G) * l * (i : G)⁻¹ := rfl

/-- Its kernel is exactly the relative centralizer used in the source quotient. -/
theorem componentAction_ker (I L : Subgroup G) (hIL : I ≤ normalizer (L : Set G)) :
    (componentAction I L hIL).ker = actionKernel I L := by
  ext i
  change componentAction I L hIL i = 1 ↔ (i : G) ∈ centralizer (L : Set G)
  constructor
  · intro hi l hl
    have he := congrArg (fun a : MulAut L => (a ⟨l,hl⟩ : G)) hi
    change (i : G) * l * (i : G)⁻¹ = l at he
    have he' := congrArg (fun x : G => x * (i : G)) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using he'.symm
  · intro hi
    ext l
    change (i : G) * l * (i : G)⁻¹ = l
    rw [← mem_centralizer_iff.mp hi l l.property, mul_inv_cancel_right]

/-- The faithful action of the actual quotient I/C_I(L), not an unrelated
model action labelled by I⁺. -/
def plusAction (I L : Subgroup G) [(actionKernel I L).Normal]
    (hIL : I ≤ normalizer (L : Set G)) : Plus I L →* MulAut L :=
  QuotientGroup.lift (actionKernel I L) (componentAction I L hIL)
    (componentAction_ker I L hIL).ge

theorem plusAction_injective (I L : Subgroup G) [(actionKernel I L).Normal]
    (hIL : I ≤ normalizer (L : Set G)) : Function.Injective (plusAction I L hIL) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [plusAction, QuotientGroup.ker_lift, componentAction_ker, QuotientGroup.map_mk'_self]

theorem plusAction_on_lift (I L : Subgroup G) [(actionKernel I L).Normal]
    (hIL : I ≤ normalizer (L : Set G)) (i : I) (l : L) :
    (plusAction I L hIL (plusMap I L i) l : G) = (i : G) * l * (i : G)⁻¹ := rfl

variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  {L D : Subgroup G} {ρ : Representation (ZMod 2) A V}

/-- The literal commutator, as an element of Z(Q). -/
def centralCommutator (hDZ : ⁅D,L⁆ ≤ coreCenter L) (x : D) (l : L) : coreCenter L :=
  ⟨⁅(x : G),(l : G)⁆, hDZ (commutator_mem_commutator x.property l.property)⟩

/-- Each centralizing actor supplies a crossed homomorphism. Its sign agrees
with the left conjugation action in `OneCohomology.cocycles`. -/
def commutatorCocycle (m : CenterModel L ρ) (hDZ : ⁅D,L⁆ ≤ coreCenter L)
    (x : D) : cocycles (ρ.comp m.actorMap) := by
  refine ⟨fun l => Multiplicative.toAdd (m.coordinates (centralCommutator hDZ x l)), ?_⟩
  intro l t
  have he : centralCommutator hDZ x (l * t) =
      centralCommutator hDZ x l * centerConjugate L l (centralCommutator hDZ x t) := by
    apply Subtype.ext
    change ⁅(x : G),(l : G) * (t : G)⁆ = _
    rw [commutatorElement_mul_right_eq_mul_conj]
    simp only [centralCommutator, centerConjugate, Subgroup.coe_mul]
    group
  change Multiplicative.toAdd (m.coordinates (centralCommutator hDZ x (l * t))) = _
  rw [he, map_mul, m.coordinates_conjugate]
  exact add_comm _ _

/-- The coefficient cocycle vanishes on the full two-core, so quotient
descent is justified even when Z(Q) has nonzero L-central submodules. -/
theorem commutatorCocycle_kills_core (m : CenterModel L ρ)
    (hDZ : ⁅D,L⁆ ≤ coreCenter L)
    (hDQ : D ≤ centralizer (extensionCore L : Set G)) (x : D) :
    ∀ l ∈ m.actorMap.ker, (commutatorCocycle m hDZ x).val l = 0 := by
  intro l hl
  rw [m.actorMap_ker] at hl
  have hp : (l : G) ∈ L.pCoreIn 2 := mem_map.mpr ⟨l,hl,rfl⟩
  have hc := commutator_core_centralizes hDZ hDQ m.core_centralizes
    (commutator_mem_commutator x.property hp)
  exact congrArg Multiplicative.toAdd ((m.coordinates_eq_one_iff _).mpr hc)

/-- The cocycle is zero on every subgroup fixed pointwise by the actor. -/
theorem commutatorCocycle_kills_marking (m : CenterModel L ρ)
    (hDZ : ⁅D,L⁆ ≤ coreCenter L) (Y : Subgroup G)
    (hDY : D ≤ centralizer (Y : Set G)) (x : D) :
    ∀ y ∈ Y.subgroupOf L, (commutatorCocycle m hDZ x).val y = 0 := by
  intro y hy
  have hc : centralCommutator hDZ x y = 1 := by
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_centralizer_iff.mp (hDY x.property) y hy).symm
  change Multiplicative.toAdd (m.coordinates (centralCommutator hDZ x y)) = 0
  rw [hc, map_one]
  rfl

/-- This is the universal-dual-cover reduction with all group-theoretic
premises discharged. Only the actual model's marked restriction calculation
remains. The central kernel is removed using perfectness, not assumed zero. -/
theorem centralizes_of_detected_model (m : CenterModel L ρ)
    (hperfect : Group.IsPerfect L) (hDZ : ⁅D,L⁆ ≤ coreCenter L)
    (hDQ : D ≤ centralizer (extensionCore L : Set G))
    (Y : Subgroup G) (hDY : D ≤ centralizer (Y : Set G))
    (hdet : DetectedOn ρ ((Y.subgroupOf L).map m.actorMap)) :
    D ≤ centralizer (L : Set G) := by
  apply centralizes_of_commutator_centralizes hperfect
  apply commutator_le.mpr
  intro x hx l hl
  let xD : D := ⟨x,hx⟩
  let lL : L := ⟨l,hl⟩
  have hf : commutatorCocycle m hDZ xD = 0 :=
    cocycle_eq_zero_of_detected_image m.actorMap m.actorMap_surjective ρ
      (Y.subgroupOf L) hdet (commutatorCocycle m hDZ xD)
      (commutatorCocycle_kills_core m hDZ hDQ xD)
      (commutatorCocycle_kills_marking m hDZ Y hDY xD)
  have he := congrArg (fun f : cocycles (ρ.comp m.actorMap) => f.val lL) hf
  apply (m.coordinates_eq_one_iff (centralCommutator hDZ xD lL)).mp
  exact Multiplicative.toAdd.injective he

/-- The actual D⁺ vanishes after the model-specific marked restriction
calculation. The centralizer bound is derived from its faithful coordinates. -/
theorem centralizerImage_eq_bot_of_detected_model (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [(actionKernel I c.L).Normal]
    (hYL : d.Yplus ≤ c.L) (hnormal : (c.L.subgroupOf I).Normal)
    (m : CenterModel c.L ρ) (hfaith : Function.Injective ρ)
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G))
    (hdet : DetectedOn ρ ((d.Yplus.subgroupOf c.L).map m.actorMap)) :
    plusImage I c.L (yplusCentralizer d I) = ⊥ := by
  have hDL := commutator_le_core_of_centralizes d c hYL hnormal
    (m.centralizer_core_le hfaith) hDQ
  have hDZ := extension_commutator_le_center d c hDL hDQ
  apply (plusImage_eq_bot_iff inf_le_left).mpr
  exact centralizes_of_detected_model m
    (component_isPerfect_of_containment d c hYL) hDZ hDQ d.Yplus inf_le_right hdet

/-- The centralizing branch has elementary actual plus image and trivial
Frattini subgroup. The model supplies its faithful action and elementary
center; the earlier checked square and commutator arguments supply the result. -/
theorem centralizing_structure_of_model [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [(actionKernel I c.L).Normal]
    (hYL : d.Yplus ≤ c.L) (hnormal : (c.L.subgroupOf I).Normal)
    (m : CenterModel c.L ρ) (hfaith : Function.Injective ρ)
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G))
    (hZ : IsElementaryAbelian 2 (coreCenter c.L)) :
    ⁅yplusCentralizer d I,c.L⁆ ≤ coreCenter c.L ∧
      IsElementaryAbelian 2 (plusImage I c.L (yplusCentralizer d I)) ∧
      frattini (plusImage I c.L (yplusCentralizer d I)) = ⊥ := by
  have hDL := commutator_le_core_of_centralizes d c hYL hnormal
    (m.centralizer_core_le hfaith) hDQ
  exact ⟨extension_commutator_le_center d c hDL hDQ,
    centralizerImage_elementary d c hDL hDQ hZ,
    centralizerImage_frattini d c hDL hDQ hZ⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover
