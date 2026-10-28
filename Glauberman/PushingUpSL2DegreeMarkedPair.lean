module
public import Glauberman.PushingUpSL2DegreeStructure
public import Theory.GroupTheory.SubgroupTransport.GapPowerTwist
/-!
# The reduced nonabelian Niles parameter

The original SL₂ marking constructs a numerical pair for the specified
conjugator and automorphism. If a central-omega subgroup escapes the core
after two twists, the diagram's center cell forces v at most two. The
class-three hypothesis excludes v = 1 because that would make the core
elementary abelian. Thus the same marked diagram has v = 2.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 6.6, pp.54--55.
The actual invariant-kernel quotient is supplied by
`Glauberman.PushingUpSL2DegreeReduction`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
open scoped MatrixGroups IsMulCommutative
namespace Glauberman
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

theorem sl2_numerical_pair_of_generating_conjugate
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) (g : G)
    (hgen : (S : Subgroup G) ⊔ (S : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤)
    (hinter : (S : Subgroup G) ⊓ (S : Subgroup G).map (MulAut.conj g).toMonoidHom = pCore 2 G) :
      NumericalPairAt (Nat.card F) (S : Subgroup G)
        ((S : Subgroup G).map (MulAut.conj g).toMonoidHom)
        (twistedConjugacy (S : Subgroup G) α g) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    change e.toMonoidHom.ker.comap (QuotientGroup.mk' (pCore 2 G)) = _
    rw [e.toMonoidHom.ker_eq_bot e.injective,MonoidHom.comap_bot,QuotientGroup.ker_mk']
  let T := S.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have hC := sl2_core_omega_centralizer e hn hF S hfit hno.noCharacteristicNormal
  let : (omegaCenterIn (pCore 2 G)).Normal := omegaCenterIn_normal_of_normal _
  have hlower (A : Subgroup G) (hA : IsPGroup 2 A) (hout : ¬ A ≤ pCore 2 G) :
      Nat.card F ≤ (omegaCenterIn (pCore 2 G) ⊓ centralizer (A : Set G)).relIndex
        (omegaCenterIn (pCore 2 G)) := by
    rw [inf_relIndex_left]
    exact Representation.SL2.normal_two_subgroup_fixed_index_lower _ f hf
      (hk.trans hC.symm) hn hF A hA (hk.symm ▸ hout)
  refine ⟨?_,S.isPGroup',?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hF]
    exact Nat.one_lt_pow (by omega) (by decide)
  · intro A hA hfix
    let _ := hA
    exact twistedConjugacy_no_fixed_normal (S : Subgroup G) α g hno hgen A hfix
  · change _ ≤ normalizer (((S : Subgroup G) ⊓
      (S : Subgroup G).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)
    rw [hinter]
    exact le_normalizer_of_normal
  · change _ ≤ normalizer (((S : Subgroup G) ⊓
      (S : Subgroup G).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)
    rw [hinter]
    exact le_normalizer_of_normal
  · rw [hinter]
    exact Matrix.SpecialLinearGroup.sylow_core_relIndex f hf hk S
  · rw [hinter]
    exact Matrix.SpecialLinearGroup.sylow_core_relIndex f hf hk T
  · intro B hB hout
    rw [hinter] at hout ⊢
    exact hlower B (S.isPGroup'.to_le hB) hout
  · intro B hB hout
    rw [hinter] at hout ⊢
    exact hlower B (T.isPGroup'.to_le hB) hout

@[expose] def NilesTwoStepDiagram (q : ℕ) (S : Subgroup G) (α : MulAut S) (g : G) : Prop :=
  let T := S.map (MulAut.conj g).toMonoidHom
  let φ := twistedConjugacy S α g
  NumericalPairAt q S T φ ∧
    IsElementaryAbelian 2 (intervalCell φ 1 2) ∧
    centerIn S = intervalCell φ 2 3 ∧ centerIn T = intervalCell φ 3 2 ∧
    centerIn (pCore 2 G) = intervalCell φ 2 2

/-- A marked central-omega subgroup escaping after two twists forces the
class-three diagram parameter to be exactly two, for that same twist. -/
theorem sl2_two_step_class_three_diagram
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) (g : G)
    (hgen : (S : Subgroup G) ⊔ (S : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤)
    (hinter : (S : Subgroup G) ⊓ (S : Subgroup G).map (MulAut.conj g).toMonoidHom = pCore 2 G)
    (hclass : Group.nilpotencyClass ((S : Subgroup G).map (MulAut.conj g).toMonoidHom) = 3)
    (Z : Subgroup G) (hZ : Z ≤ omegaCenterIn (pCore 2 G))
    (hescape : ¬ (image (twistedConjugacy (S : Subgroup G) α g))^[2] Z ≤ pCore 2 G) :
    NilesTwoStepDiagram (Nat.card F) (S : Subgroup G) α g := by
  let T := (S : Subgroup G).map (MulAut.conj g).toMonoidHom
  let φ := twistedConjugacy (S : Subgroup G) α g
  have hnum := sl2_numerical_pair_of_generating_conjugate e hn hF S α hfit hno g hgen hinter
  let pair : IntersectionPair G := ⟨S,T,φ⟩
  obtain ⟨v,hv,hE,hmaxS,hmaxT,hj,hzS,hzT,hzQ⟩ := pair.exists_double_lattice_center_cells_at hnum
  change centerIn ((S : Subgroup G) ⊓ T) = intervalCell φ v v at hzQ
  rw [hinter] at hzQ
  have hZv : Z ≤ intervalCell φ v v := by
    rw [←hzQ]
    intro z hz
    obtain ⟨hQ,hC,_⟩ := (mem_omegaCenterIn_iff _ _).mp (hZ hz)
    exact ⟨hQ,hC⟩
  have hle : v ≤ 2 := by
    by_contra hv'
    have hshift : (image φ)^[2] (intervalCell φ v v) = intervalCell φ (v+2) (v-2) := by
      change image φ (image φ (intervalCell φ v v)) = _
      rw [show v=(v-1)+1 by omega,image_intervalCell,
        show v-1=(v-2)+1 by omega,image_intervalCell]
      congr 1
    have hh : (image φ)^[2] Z ≤ (image φ)^[2] (intervalCell φ v v) :=
      image_mono φ (image_mono φ hZv)
    rw [hshift] at hh
    apply hescape
    rw [←hinter,←intervalCell_intersection φ]
    exact hh.trans (intervalCell_antitone φ (by omega) (by omega))
  have hne : v ≠ 1 := by
    intro hv1
    have hQe : IsElementaryAbelian 2 (pCore 2 G) := by
      rw [←hinter,←intervalCell_intersection φ]
      rw [hv1] at hE
      exact hE
    let _ := hQe
    have hc := class_le_two_of_abelian_core_numerical_pair S T φ hnum hinter
      hno.noCharacteristicNormal inferInstance
    let _ := S.isPGroup'.isNilpotent
    have he := (MulAut.conj g).subgroupMap (S : Subgroup G)
    have hh := Group.nilpotencyClass_le_of_surjective he.toMonoidHom he.surjective
    have h3 : 3 ≤ Group.nilpotencyClass S := hclass ▸ hh
    omega
  have hv2 : v = 2 := by omega
  subst v
  exact ⟨hnum,hE,hzS,hzT,hzQ⟩
end Glauberman
