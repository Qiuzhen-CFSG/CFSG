module
public import Theory.SpecificGroups.PSL3.CartanActions.RootTorusFieldOrder
public import Theory.GroupTheory.QuotientSylowNormalizerDisplacement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Normalizer.Coefficients
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Components

/-!
# Simultaneous PSL₃ odd-subfield normalizer lifts

Align the actual component quotient with the original Sylow intersection.
Every Sylow actor is linear-field-graph. The graph fixes the root torus and
the two-power coefficient action fixes the odd-degree subfield. Thus every
lift of its root-torus elements normalizes the original Sylow, by quotient
displacements. Both field and graph factors are retained.

Source: Aschbacher--Smith 11.5.6(3), printed p.781.
-/

@[expose] public noncomputable section
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.SixCommutators
open Matrix.PSL3.CartanActions.RootTorusControl
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear.RankTwo
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I : Subgroup G}

/-- Coordinates on the literal quotient, aligned with the original Sylow intersection. -/
structure Coordinates (T : Sylow 2 G) (I : Subgroup G) (F : BinaryField) where
  model : (I ⧸ pCore 2 I) ≃* PSL(3,F.Carrier)
  sylow_image : ((T : Subgroup G).subgroupOf I).map
    (model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) = unipotent F.Carrier

namespace Coordinates
variable {F : BinaryField} (c : Coordinates T I F)

def quotient : I →* PSL(3,F.Carrier) :=
  c.model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))

omit [Finite G] in
theorem quotient_surjective : Function.Surjective c.quotient :=
  c.model.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem quotient_sylow_image : ((T : Subgroup G).subgroupOf I).map c.quotient =
    unipotent F.Carrier := c.sylow_image

def actor (x : normalizer (I : Set G)) : MulAut PSL(3,F.Carrier) :=
  MulAut.congr c.model (coreQuotientAction I x)

omit [Finite G] in
theorem actor_quotient (x : normalizer (I : Set G)) (i : I) :
    c.actor x (c.quotient i) = c.quotient (I.normalizerMonoidHom x i) := by
  change c.model (coreQuotientAction I x (c.model.symm
    (c.model (QuotientGroup.mk' (pCore 2 I) i)))) = _
  rw [c.model.symm_apply_apply,coreQuotientAction_apply_mk]
  rfl

omit [Finite G] in
theorem actor_preserves_root (x : normalizer (I : Set G))
    (hx : (x : G) ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G)) :
    (unipotent F.Carrier).map (c.actor x).toMonoidHom = unipotent F.Carrier := by
  rw [← c.quotient_sylow_image]
  have he : (c.actor x).toMonoidHom.comp c.quotient =
      c.quotient.comp (I.normalizerMonoidHom x).toMonoidHom := by
    ext i
    exact c.actor_quotient x i
  rw [Subgroup.map_map,he,← Subgroup.map_map]
  congr 1
  ext i
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact ((mem_normalizer_iff.mp hx j).mp ⟨hj,j.property⟩).1
  · intro hi
    refine ⟨(I.normalizerMonoidHom x).symm i,?_,(I.normalizerMonoidHom x).apply_symm_apply i⟩
    exact ((mem_normalizer_iff.mp ((normalizer _).inv_mem hx) i).mp
      ⟨hi,i.property⟩).1

/-- Every lift of an odd-subfield root-torus element normalizes the original T. -/
theorem normalizes_of_odd_rootTorus
    (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    (b : I) (u : (oddField F).Carrierˣ)
    (hb : c.quotient b = rootTorus F.Carrier (Units.map (oddInclusion F).toMonoidHom u)) :
    (b : G) ∈ normalizer (T : Set G) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T I hTI
  have hk : c.quotient.ker ≤ (T : Subgroup G).subgroupOf I := by
    intro i hi
    have hi' : i ∈ pCore 2 I := (QuotientGroup.eq_one_iff _).mp
      (c.model.map_eq_one_iff.mp hi)
    rw [← hP]
    exact pCore_isPGroup.le_sylow_of_normal P hi'
  let a : T → MulAut PSL(3,F.Carrier) := fun t => c.actor ⟨t,hTI t.property⟩
  apply mem_normalizer_of_quotient_displacements (T : Subgroup G) I hTI
    c.quotient hk a (fun t i => c.actor_quotient ⟨t,hTI t.property⟩ i) b
  intro t
  have htS : (t : G) ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨(T : Subgroup G).le_normalizer t.property,hTI t.property⟩
  have hr := c.actor_preserves_root ⟨t,hTI t.property⟩ htS
  have hcover := Matrix.PSL3Even.AutomorphismCoverage.standard_eq_top_of_root_orientation
    F.Carrier F.degree_pos F.card_eq
    (Matrix.PSL3Even.AutomorphismCoverage.exists_oppositionGraph_preserves_roots_of_charTwo F.Carrier)
  obtain ⟨m,σ,ε,he⟩ := ActorCoverage.projectiveCoverage_of_standard_eq_top F.Carrier hcover (a t)
  obtain ⟨k,hkpow⟩ := T.isPGroup'.exists_pow_pow_eq_one t
  have hapow : a t ^ (2 ^ k) = 1 := by
    let f := (MulAut.congr c.model).toMonoidHom.comp
      ((coreQuotientAction I).comp (inclusion hTI))
    change f t ^ (2 ^ k) = 1
    rw [← map_pow,hkpow,map_one]
  have hσ := actor_coefficient_pow F.Carrier F.card_eq m σ ε (he ▸ hr) (he ▸ hapow)
  obtain ⟨v,hv,hve⟩ := actor_rootTorus_factor F.Carrier m σ ε (he ▸ hr)
    (Units.map (oddInclusion F).toMonoidHom u)
  rw [oddInclusion_fixed_of_two_power F σ hσ u] at hve
  rw [c.quotient_sylow_image,hb,he,hve]
  have hn := borel_le_normalizer_unipotent F.Carrier
    (rootTorus_le_borel F.Carrier ⟨Units.map (oddInclusion F).toMonoidHom u,rfl⟩)
  simpa only [mul_assoc,inv_inv] using
    (mem_normalizer_iff.mp ((normalizer _).inv_mem hn) v).mp hv

/-- All odd-subfield root-torus coefficients have simultaneous normalizer lifts. -/
theorem odd_rootTorus_lifts (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    (u : (oddField F).Carrierˣ) : ∃ b : I,
      (b : G) ∈ normalizer (T : Set G) ∧
      c.quotient b = rootTorus F.Carrier (Units.map (oddInclusion F).toMonoidHom u) := by
  obtain ⟨b,hb⟩ := c.quotient_surjective
    (rootTorus F.Carrier (Units.map (oddInclusion F).toMonoidHom u))
  exact ⟨b,c.normalizes_of_odd_rootTorus hTI b u hb,hb⟩
end Coordinates

/-- Sylow conjugacy aligns any actual projective quotient with the original T. -/
theorem exists_coordinates (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    (F : BinaryField) (e : (I ⧸ pCore 2 I) ≃* PSL(3,F.Carrier)) :
    Nonempty (Coordinates T I F) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T I hTI
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let S := P.mapSurjective hq
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F.Carrier) S
    (unipotentSylow F.Carrier F.degree_pos F.card_eq)
  let e' := e.trans (MulAut.conj g)
  refine ⟨⟨e',?_⟩⟩
  have hh := congrArg Sylow.toSubgroup hg
  rw [Sylow.coe_subgroup_smul,coe_unipotentSylow] at hh
  change ((P : Subgroup I).map q).map (MulAut.conj g).toMonoidHom = _ at hh
  have heq : e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I)) =
      (MulAut.conj g).toMonoidHom.comp q := rfl
  rw [heq,← Subgroup.map_map,← hP]
  exact hh
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear.RankTwo
