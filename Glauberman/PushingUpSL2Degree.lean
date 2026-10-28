module
public import Theory.Representation.SL2.TwoSubgroupFixedIndex
public import Theory.SpecificGroups.SL2.OriginalSylowPair
public import Glauberman.PushingUpNontrivialAction
public import Glauberman.FixedNormalPairDegreeLattice
public import Theory.SpecificGroups.SL2.TwoCore
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# The original-degree Main Hypothesis pair

Characteristic two and the absence of characteristic normal Sylow
subgroups force noncentral core-omega action. The simple SL2 quotient
then identifies its centralizer with the whole two-core. Every outside
two-subgroup has fixed index at least the original field order. Residual
conjugate Sylows and the specified automorphism give the numerical pair
used in Niles descent, without a field-four restriction.

Source: Niles, *Pushing-up in finite groups* (1979), Lemmas 2.3 and 4.2--4.3,
pp.29,44. The actual application is the original F0 central-chief quotient
in NonbinarySymplectic.CriticalReduction.RootProductNilesDiagram.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
open scoped MatrixGroups IsMulCommutative
namespace Glauberman
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

theorem sl2_core_omega_centralizer
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoCharacteristicNormal (S : Subgroup G)) :
    centralizer (omegaCenterIn (pCore 2 G) : Set G) = pCore 2 G := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    change e.toMonoidHom.ker.comap (QuotientGroup.mk' (pCore 2 G)) = _
    rw [e.toMonoidHom.ker_eq_bot e.injective,MonoidHom.comap_bot,QuotientGroup.ker_mk']
  have hlarge : 3 < Nat.card F := by
    rw [hF]
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hh
    omega
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup SL(2,F) :=
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).isSimpleGroup
  let V := omegaCenterIn (pCore 2 G)
  let : V.Normal := omegaCenterIn_normal_of_normal _
  have hQC : pCore 2 G ≤ centralizer (V : Set G) :=
    le_centralizer_iff.mp (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    have hi := Matrix.SpecialLinearGroup.sylow_core_relIndex f hf hk S
    intro he
    rw [he,relIndex_bot_right] at hi
    omega
  have hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
    rw [←hfit]
    exact centralizer_generalizedFitting_le G
  have hfixed := pushingUp_sylow_fixed_ne_ambient_fixed S hSne hc hno
  let C := centralizer (V : Set G)
  let : (C.map f).Normal := Normal.map inferInstance f hf
  apply le_antisymm ?_ hQC
  rcases (inferInstance : (C.map f).Normal).eq_bot_or_eq_top with hb | ht
  · rw [←hk]
    exact (map_eq_bot_iff C).mp hb
  · have htop := congrArg (Subgroup.comap f) ht
    rw [comap_map_eq,hk,sup_eq_left.mpr hQC,comap_top] at htop
    have hz : V ≤ center G := centralizer_eq_top_iff_subset.mp htop
    exact (hfixed (by rw [inf_eq_left.mpr (hz.trans (center_le_centralizer _)),
      inf_eq_left.mpr hz])).elim

theorem original_sl2_numerical_pair
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) :
    ∃ g : G, g ∈ pResidual 2 G ∧
      (S : Subgroup G) ⊔ (S : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤ ∧
      (S : Subgroup G) ⊓ (S : Subgroup G).map (MulAut.conj g).toMonoidHom = pCore 2 G ∧
      NumericalPairAt (Nat.card F) (S : Subgroup G)
        ((S : Subgroup G).map (MulAut.conj g).toMonoidHom)
        (twistedConjugacy (S : Subgroup G) α g) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    change e.toMonoidHom.ker.comap (QuotientGroup.mk' (pCore 2 G)) = _
    rw [e.toMonoidHom.ker_eq_bot e.injective,MonoidHom.comap_bot,QuotientGroup.ker_mk']
  obtain ⟨g,hg,hgen,hinter⟩ := Matrix.SpecialLinearGroup.exists_residual_generating_sylow_pair f hf hk S
  let T := S.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have hC := sl2_core_omega_centralizer e hn hF S hfit hno.noCharacteristicNormal
  let : (omegaCenterIn (pCore 2 G)).Normal := omegaCenterIn_normal_of_normal _
  have hlower (A : Subgroup G) (hA : IsPGroup 2 A) (hout : ¬ A ≤ pCore 2 G) :
      Nat.card F ≤ (omegaCenterIn (pCore 2 G) ⊓ centralizer (A : Set G)).relIndex
        (omegaCenterIn (pCore 2 G)) := by
    rw [inf_relIndex_left]
    exact Representation.SL2.normal_two_subgroup_fixed_index_lower _ f hf
      (hk.trans hC.symm) hn hF A hA (hk.symm ▸ hout)
  refine ⟨g,hg,hgen,hinter,?_,S.isPGroup',?_,?_,?_,?_,?_,?_,?_⟩
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
end Glauberman
