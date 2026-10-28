module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.FixedFamily
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.LocalMinimum
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.CriticalPair

/-!
# Reciprocal actions of the actual doubled critical pair

E.3.10 places the nontrivial action of a doubled conjugate in A_{2n}.
The fixed-space-family calculation removes its field and multiplicity
actions, and the elementary SL₃ bound makes its rank exactly 2n.
Conjugation by the inverse element gives the other centralizer corank.
The resulting two plane-shear actions identify both fixed subgroups with
the actual intersection and commutator, whose order is 2^(4n).

The final consumer applies these results to the pair produced by F.7.11
under weak-closure containment. The remaining chosen-line alignment and
its normalizer exclusion are still required to prove weak-closure escape.

Source: Aschbacher--Smith, 11.3.6, printed p.772, second paragraph.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.SL3DoubledNaturalOffenders
open CFSG.Quasithin.ChapterE
open Representation.SL3.BinaryDefiningFactors.AdjointFixedSpaces
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
namespace ShearCoordinates
variable {G F : Type*} [Group G] [Field F] {A B : Subgroup G}

/-- The common fixed plane of the full shear group is exactly its commutator. -/
theorem centralizer_eq_commutator (d : ShearCoordinates A B F) :
    B ⊓ centralizer (A : Set G) = ⁅A,B⁆ := by
  rw [d.commutator_eq_plane]
  apply le_antisymm
  · intro v hv
    apply (d.mem_lift Shears.plane ⟨v,hv.1⟩).mpr
    obtain ⟨a,ha⟩ := d.realizes 1 0
    have he : B.normalizerMonoidHom (inclusion d.normalized a) ⟨v,hv.1⟩ = ⟨v,hv.1⟩ := by
      apply Subtype.ext
      change (a:G)*v*(a:G)⁻¹=v
      rw [hv.2 a a.property,mul_inv_cancel_right]
    have hh := ha ⟨v,hv.1⟩
    rw [he] at hh
    intro i
    have hi := congrArg (fun w : Shears.Space F => w i 0) hh
    simpa [Shears.shear] using hi.symm
  · rintro v ⟨w,hw,rfl⟩
    refine ⟨w.property,fun a ha => ?_⟩
    obtain ⟨p,q,hpq⟩ := d.shear_action ⟨a,ha⟩
    have he : B.normalizerMonoidHom (inclusion d.normalized ⟨a,ha⟩) w = w := by
      apply d.coordinates.injective
      apply Multiplicative.toAdd.injective
      rw [hpq]
      ext i j
      fin_cases j <;> simp [Shears.shear,show (d.coordinates w).toAdd i 2=0 from hw i]
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)
end ShearCoordinates

namespace CriticalAction
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

private theorem family_rank_le {n : ℕ} (hn : 0<n) (hF : Nat.card F=2^n)
    (A : Subgroup (Ambient F))
    (hA : A ∈ fixedSpaceFamily (action F) (2*n))
    (hAN : A ≤ SL3DoubledNaturalOffenders.normalizer F) : rank A ≤ 2*n := by
  let := hA.2.1.2
  have hAC := FixedFamily.family_le_component hF (by omega) (by omega) hA hAN
  let e : SL F ≃* component F := MonoidHom.ofInjective
    (show Function.Injective (representation F).asGroupHom from
      fun _ _ he => representation_injective F (congrArg Units.val he))
  let B := (A.subgroupOf (component F)).map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 (A.subgroupOf (component F)) := IsElementaryAbelian.subgroupOf hAC
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hc : Nat.card B = Nat.card A := by
    rw [card_map_of_injective e.symm.injective,Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv]
  have hB : B≠⊥ := by
    intro he
    have hh := hA.2.1.1
    apply hh
    apply eq_bot_of_card_eq
    rw [←hc,he,card_bot]
  obtain ⟨g,b,hb⟩ := elementary_conjugate_le_rootPlane hn hF B ⟨hB,inferInstance⟩
  have hh := rank_le_of_le_rootPlane hF _ b hb
  rw [rank_map_conj] at hh
  simpa only [rank,hc] using hh

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- E.3.10's actual action image has rank 2n on every noncommuting doubled
conjugate which normalizes the original full module. -/
theorem conjugate_corank (d : Coordinates D S) (g : G)
    (hn : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ normalizer (fullModule L V : Set G))
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    subgroupCorank ((fullModule L V).map (MulAut.conj g).toMonoidHom)
      ((fullModule L V).map (MulAut.conj g).toMonoidHom ⊓ centralizer (fullModule L V : Set G)) = 2*S.field.degree := by
  let := fullModule_elementary d
  have hs := LocalMinimum.globalS_eq d
  have hz : subgroupCorank ((fullModule L V).map (MulAut.conj g).toMonoidHom)
      ((fullModule L V).map (MulAut.conj g).toMonoidHom) = 0 := by
    simp only [subgroupCorank,relIndex_self]
    decide
  have hf := (inducedAutomizer_mem_fixedSpaceFamily_of_corank_lt_globalS g
    (le_inf le_rfl hn) (by rw [hz,hs]; exact_mod_cast (by have := S.field.degree_pos; omega : 0 < 2*S.field.degree)) hne).2
  rw [hz,Nat.sub_zero,hs,ENat.toNat_mul,ENat.toNat_ofNat,ENat.toNat_natCast] at hf
  let A := inducedAutomizer (fullModule L V) ((fullModule L V).map (MulAut.conj g).toMonoidHom)
  have hl : 2*S.field.degree ≤ rank A :=
    parameter_le_rank_of_mem_fixedSpaceFamily (automizerRepresentation (fullModule L V))
      (automizerRepresentation_injective (fullModule L V)) hf
  obtain ⟨E,f,hfi,hE,hN,_,_⟩ := LocalMinimum.automizer_marking_component d
  have hfm := fixedSpaceFamily_map_of_equivariant
    (automizerRepresentation (fullModule L V)) (action S.field.Carrier) f hfi E hE hf
  have hb := family_rank_le S.field.degree_pos S.field.card_eq (A.map f) hfm
    (by rintro x ⟨a,ha,rfl⟩; exact hN ⟨a,rfl⟩)
  have he : rank (A.map f)=rank A := by rw [rank,card_map_of_injective hfi]; rfl
  rw [he] at hb
  have hr : rank A = 2*S.field.degree := Nat.le_antisymm hb hl
  rwa [rank_inducedAutomizer _ _ hn] at hr

omit [Finite G] in
private theorem conjugate_cancel (W : Subgroup G) (g : G) :
    (W.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = W := by
  rw [offender_map_conj_map,mul_inv_cancel]
  have he : (MulAut.conj (1:G)).toMonoidHom = MonoidHom.id G := by ext; simp
  rw [he,map_id]

/-- Symmetry preserves the literal centralizers and yields both coranks. -/
theorem pair_coranks (d : Coordinates D S) (g : G)
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
      fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom) :
    subgroupCorank ((fullModule L V).map (MulAut.conj g).toMonoidHom)
      ((fullModule L V).map (MulAut.conj g).toMonoidHom ⊓ centralizer (fullModule L V : Set G)) = 2*S.field.degree ∧
    subgroupCorank (fullModule L V)
      (fullModule L V ⊓ centralizer ((fullModule L V).map (MulAut.conj g).toMonoidHom : Set G)) = 2*S.field.degree := by
  have hn : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ normalizer (fullModule L V : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.trans inf_le_left)
  refine ⟨conjugate_corank d g hn hne,?_⟩
  have hn' : (fullModule L V).map (MulAut.conj g⁻¹).toMonoidHom ≤ normalizer (fullModule L V : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hcomm.trans inf_le_right)
    rw [map_commutator,show ((fullModule L V).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = fullModule L V from by simpa using conjugate_cancel (fullModule L V) g⁻¹] at hh
    rwa [commutator_comm] at hh
  have hne' : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g⁻¹).toMonoidHom⁆ ≠ ⊥ := by
    intro hz
    have hh := congrArg (fun X : Subgroup G => X.map (MulAut.conj g).toMonoidHom) hz
    rw [map_commutator,conjugate_cancel,Subgroup.map_bot,commutator_comm] at hh
    exact hne hh
  have hh := conjugate_corank d g⁻¹ hn' hne'
  have ht := corank_centralizer_map (A := (fullModule L V).map (MulAut.conj g⁻¹).toMonoidHom)
    (B := fullModule L V) (MulAut.conj g)
  rw [conjugate_cancel] at ht
  exact ht.trans hh

/-- Both complete plane-shear actions are constructed for the actual critical
pair, with no numerical or recognition premise. -/
theorem pair_shears (d : Coordinates D S) (g : G)
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
      fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom) :
    Nonempty (ShearCoordinates ((fullModule L V).map (MulAut.conj g).toMonoidHom)
      (fullModule L V) S.field.Carrier) ∧
    Nonempty (ShearCoordinates (fullModule L V)
      ((fullModule L V).map (MulAut.conj g).toMonoidHom) S.field.Carrier) := by
  let := fullModule_elementary d
  let : IsElementaryAbelian 2 ((fullModule L V).map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  obtain ⟨ha,hb⟩ := pair_coranks d g hne hcomm
  exact ⟨shears_of_coordinates d (le_normalizer_iff_commutator_le_left.mpr (hcomm.trans inf_le_left)) ha.ge hb.le,
    shears_of_coordinates_map d (MulAut.conj g)
      (le_normalizer_iff_commutator_le_right.mpr (hcomm.trans inf_le_right)) hb.ge ha.le⟩

/-- In the reciprocal critical pair, both fixed subgroups are the same
literal commutator subgroup. -/
theorem pair_centralizers (d : Coordinates D S) (g : G)
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
      fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom) :
    fullModule L V ⊓ centralizer ((fullModule L V).map (MulAut.conj g).toMonoidHom : Set G) =
      ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ∧
    (fullModule L V).map (MulAut.conj g).toMonoidHom ⊓ centralizer (fullModule L V : Set G) =
      ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ := by
  obtain ⟨⟨a⟩,⟨b⟩⟩ := pair_shears d g hne hcomm
  exact ⟨a.centralizer_eq_commutator.trans (commutator_comm _ _),b.centralizer_eq_commutator⟩

/-- Mutual normalization makes the actual intersection precisely the
common fixed subgroup and commutator. -/
theorem pair_intersection (d : Coordinates D S) (g : G)
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
      fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom) :
    fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom =
      ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ := by
  let := fullModule_elementary d
  let : IsElementaryAbelian 2 ((fullModule L V).map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  apply le_antisymm _ hcomm
  rw [←(pair_centralizers d g hne hcomm).1]
  exact inf_le_inf_left _ (le_centralizer_iff_isMulCommutative.mpr inferInstance)

/-- The full commutator has the source dimension 4n, now from the critical
pair hypotheses themselves. -/
theorem pair_commutator_card (d : Coordinates D S) (g : G)
    (hne : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
      fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom) :
    Nat.card (⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ : Subgroup G) =
      2^(4*S.field.degree) := by
  obtain ⟨_,⟨c⟩⟩ := pair_shears d g hne hcomm
  exact c.commutator_card S.field.degree S.field.card_eq

end CriticalAction

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Under weak-closure containment, the literal F.7.11 pair in the original T
has both full reciprocal plane actions. Their numerical and natural-placement
premises have all been discharged. The source line-alignment exclusion is
still required to deduce weak-closure escape. -/
theorem exists_sheared_critical_pair (h : Hypothesis1131At D S U₁ H)
    (d : Coordinates D S)
    (hw : indexedWeakClosure (fullModule L V) (T : Subgroup G) 0 ≤ H.pCoreIn 2) :
    ∃ g : G, (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ T ∧
      ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅fullModule L V,(fullModule L V).map (MulAut.conj g).toMonoidHom⁆ ≤
        fullModule L V ⊓ (fullModule L V).map (MulAut.conj g).toMonoidHom ∧
      Nonempty (ShearCoordinates ((fullModule L V).map (MulAut.conj g).toMonoidHom)
        (fullModule L V) S.field.Carrier) ∧
      Nonempty (ShearCoordinates (fullModule L V)
        ((fullModule L V).map (MulAut.conj g).toMonoidHom) S.field.Carrier) := by
  obtain ⟨g,hg,hne,hcomm⟩ := exists_doubled_critical_pair d H h.outside.1.1.2 h.outside.1.2 hw
  exact ⟨g,hg,hne,hcomm,CriticalAction.pair_shears d g hne hcomm⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
