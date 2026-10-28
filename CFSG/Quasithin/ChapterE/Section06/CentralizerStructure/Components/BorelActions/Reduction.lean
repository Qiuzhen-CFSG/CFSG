module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Basic
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Common deductions for the Borel case of E.6.11

The E.6 setup puts the displacement [V,L ∩ M] in the center of L ∩ Q.
The two-core of the component is central and lies in every actual Sylow
two-subgroup of L, so it also lies in this center. A complement to C_L(V)
has the same displacement as L ∩ M. The direct decomposition in E.6.8
then makes its conjugation action on the displacement faithful.

The model computations still have to construct the complement and prove
the reverse Sylow-center containment. The cyclic binary action still has
to be shown regular. The specifications below separate these independent
obligations; none is asserted by a definition or a record projection.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(1)
and the Borel case of E.6.11, printed pp.247,250 (PDF pp.258,261).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.BorelActions

universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L X : Subgroup G} {n : ℕ}

/-- The intrinsic complement and remaining center containment needed from
each model. This is a proof obligation, not a hypothesis of E.6.8. -/
structure ModelWitness (M V Q L : Subgroup G) (n : ℕ) : Prop where
  exists_complement : ∃ X : Subgroup G,
    X ≤ L ⊓ M ∧ Nonempty (X ≃* Multiplicative (ZMod (2 ^ n - 1))) ∧
    (L ⊓ centralizer (V : Set G)) ⊔ X = L ⊓ M ∧
    (L ⊓ centralizer (V : Set G)) ⊓ X = ⊥
  center_le : (center ↥(L ⊓ Q)).map (L ⊓ Q).subtype ≤
    L.pCoreIn 2 ⊔ ⁅V, L ⊓ M⁆

/-- A cyclic faithful action of Singer order on a binary vector space is
regular off the identity. This universal implication is a separate proof
obligation, independent of the Borel model computations. -/
def BinarySingerRegularity : Prop :=
  ∀ (W X : Subgroup G) (n : ℕ), 1 < n → IsElementaryAbelian 2 W →
    Nat.card W = 2 ^ n → Nonempty (X ≃* Multiplicative (ZMod (2 ^ n - 1))) →
    X ≤ normalizer (W : Set G) → X ⊓ centralizer (W : Set G) = ⊥ →
    RegularConjugation X W

omit [Finite G] in
/-- Quasisimplicity transfers from the component inside its own overgroup. -/
theorem component_quasisimple (hL : ComponentIn (centralizer (U : Set G)) L) :
    IsQuasisimple L := by
  let _ := hL.2.2
  exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hL.1)

/-- The displacement is central in the actual intersection L ∩ Q. -/
theorem displacement_le_center
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V) :
    ⁅V, L ⊓ M⁆ ≤ (center ↥(L ⊓ Q)).map (L ⊓ Q).subtype := by
  have hWV : ⁅V, L ⊓ M⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp
    (component_intersection_normalizes h hU hL.1)
  have hWL : ⁅V, L ⊓ M⁆ ≤ L :=
    (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp hVL)
  have hVQ : V ≤ Q := hQ.symm ▸ h.le_sylowCentralizer
  have hQV : Q ≤ centralizer (V : Set G) := hQ.symm ▸ inf_le_right
  intro w hw
  refine ⟨⟨w, hWL hw, hVQ (hWV hw)⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro q
  apply Subtype.ext
  exact ((mem_centralizer_iff.mp (hQV q.property.2)) w (hWV hw)).symm

/-- The component two-core lies in the center of its actual Sylow subgroup. -/
theorem core_le_center
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q) :
    L.pCoreIn 2 ≤ (center ↥(L ⊓ Q)).map (L ⊓ Q).subtype := by
  let _ := component_quasisimple hL
  have hcore : L.pCoreIn 2 ≤ L ⊓ Q := hS ▸ pCoreIn_le_sylow L S
  rintro w ⟨z, hz, rfl⟩
  refine ⟨⟨(z : G), hcore (mem_map_of_mem L.subtype hz)⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro q
  apply Subtype.ext
  exact congrArg (fun a : L => (a : G))
    (mem_center_iff.mp (IsQuasisimple.pCore_le_center 2 hz) ⟨q, q.property.1⟩)

/-- The inclusion in E.6.11(3b) that needs no matrix calculation. -/
theorem core_sup_displacement_le_center
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q) :
    L.pCoreIn 2 ⊔ ⁅V, L ⊓ M⁆ ≤ (center ↥(L ⊓ Q)).map (L ⊓ Q).subtype :=
  sup_le (core_le_center hL S hS) (displacement_le_center h hU hL hVL hQ)

/-- Any centralizing complement has the required commutator equality. -/
theorem displacement_eq_of_complement
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) (hX : X ≤ L ⊓ M)
    (hgen : (L ⊓ centralizer (V : Set G)) ⊔ X = L ⊓ M) :
    ⁅V, X⁆ = ⁅V, L ⊓ M⁆ :=
  commutator_eq_of_centralizing_sup hgen inf_le_right
    (hX.trans (component_intersection_normalizes h hU hL.1))

omit [Finite G] in
/-- The fixed factor of E.6.8 makes restriction to the displacement faithful
on the induced action of L. -/
theorem displacement_centralizer (b : BorelAlternative M V U L n) (hn : 1 < n) :
    L ⊓ centralizer ((⁅V, L ⊓ M⁆ : Subgroup G) : Set G) = L ⊓ centralizer (V : Set G) := by
  have hd := b.decomposition hn
  apply le_antisymm
  · rintro x ⟨hxL, hxW⟩
    refine ⟨hxL, ?_⟩
    apply mem_centralizer_iff.mpr
    intro v hv
    have hv' : v ∈ ⁅V, L ⊓ M⁆ ⊔ (V ⊓ centralizer (L : Set G)) := hd.1.symm ▸ hv
    have hjoin : ⁅V, L ⊓ M⁆ ⊔ (V ⊓ centralizer (L : Set G)) ≤
        centralizer ({x} : Set G) := by
      apply sup_le
      · intro w hw
        exact mem_centralizer_singleton_iff.mpr
          ((mem_centralizer_iff.mp hxW) w hw)
      · intro d hd
        exact mem_centralizer_singleton_iff.mpr
          (((mem_centralizer_iff.mp hd.2) x hxL).symm)
    exact mem_centralizer_singleton_iff.mp (hjoin hv')
  · have hWV : ⁅V, L ⊓ M⁆ ≤ V := le_sup_left.trans hd.1.le
    exact inf_le_inf_left L (centralizer_le hWV)

omit [Finite G] in
/-- Disjointness of a complement is exactly the missing faithfulness on the
displacement; it is not merely faithfulness on an unrelated model. -/
theorem complement_faithful (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hX : X ≤ L ⊓ M)
    (hd : (L ⊓ centralizer (V : Set G)) ⊓ X = ⊥) :
    X ⊓ centralizer ((⁅V, L ⊓ M⁆ : Subgroup G) : Set G) = ⊥ := by
  apply le_bot_iff.mp
  rintro x ⟨hxX, hxW⟩
  have hxC : x ∈ L ⊓ centralizer (V : Set G) :=
    displacement_centralizer b hn ▸ ⟨(hX hxX).1, hxW⟩
  exact hd ▸ (show x ∈ (L ⊓ centralizer (V : Set G)) ⊓ X from ⟨hxC, hxX⟩)

/-- The displacement inherits the binary vector space structure of V. -/
theorem displacement_elementary (h : HypothesisE61 K T M V)
    (b : BorelAlternative M V U L n) (hn : 1 < n) :
    IsElementaryAbelian 2 (⁅V, L ⊓ M⁆ : Subgroup G) := by
  let _ := h.elementary
  exact IsElementaryAbelian.of_le (le_sup_left.trans (b.decomposition hn).1.le)

/-- The dimension clause of E.6.8 gives the actual order required by the
Singer action, rather than just a logarithmic bound. -/
theorem displacement_card (h : HypothesisE61 K T M V)
    (b : BorelAlternative M V U L n) (hn : 1 < n) :
    Nat.card (⁅V, L ⊓ M⁆ : Subgroup G) = 2 ^ n := by
  let _ := h.elementary
  have hp : IsPGroup 2 (⁅V, L ⊓ M⁆ : Subgroup G) :=
    (IsElementaryAbelian.isPGroup 2 V).to_le
      (le_sup_left.trans (b.decomposition hn).1.le)
  obtain ⟨d, hd⟩ := hp.exists_card_eq
  have hdn : d = n := by
    simpa only [subgroupCorank, Subgroup.relIndex_bot_left, hd,
      Nat.log_pow (by decide : 1 < 2)] using b.displacement_dimension hn
  simpa only [hdn] using hd

end CFSG.Quasithin.ChapterE.Section06.Components.BorelActions
