module

public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Theory.SpecificGroups.SymmetricFive.OuterActorCubicSelection
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Excluding outer elementary actors in the rank-one source quotient

Let J be a normal SL₂(2ⁿ) in X, with trivial O₂(X) and two-group quotient
X/J. Its centralizer is trivial, so X embeds faithfully in Aut(J). For n > 2,
an elementary subgroup meeting the outer coset has order at most 2^(n/2+1),
strictly below 2ⁿ. For n = 2, the prescribed J identifies with A₅ and an outer
actor identifies X with S₅. A cubic subgroup normalized but not centralized
by that same actor supplies the obstruction used by the source fixed-space
family. The source consumer is `selected_star_le_residual` in the parent leaf.

This proves the group-theoretic step implicit in Aschbacher--Smith 11.3.7,
first proof paragraph, printed p.773 (combined manuscript, 1 March 2004).
The matrix automorphism and five-point action results are imported from the
existing attributed model development; no new model certificates are assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.SylowPlacement

private theorem centralizer_eq_bot {X : Type*} [Group X] [Finite X]
    (J : Subgroup X) [J.Normal] (hZ : center J = ⊥)
    (hq : IsPGroup 2 (X ⧸ J)) (hcore : pCore 2 X = ⊥) :
    centralizer (J : Set X) = ⊥ := by
  let C := centralizer (J : Set X)
  let f : C →* X ⧸ J := (QuotientGroup.mk' J).comp C.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hxJ : (x : X) ∈ J := (QuotientGroup.eq_one_iff _).mp hx
    have hxZ : (⟨x,hxJ⟩ : J) ∈ center J := by
      rw [mem_center_iff]
      intro j
      exact Subtype.ext ((mem_centralizer_iff.mp x.property) j j.property)
    rw [hZ,mem_bot] at hxZ
    exact Subtype.ext (congrArg (fun j : J => (j : X)) hxZ)
  have hp : IsPGroup 2 C := hq.of_injective f hf
  exact bot_unique ((show C ≤ pCore 2 X from le_sSup ⟨inferInstance,hp⟩).trans hcore.le)

private theorem center_eq_bot_of_equiv {J F : Type*} [Group J] [Field F] [CharP F 2]
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F) : center J = ⊥ := by
  apply bot_unique
  intro j hj
  have he : e j ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [mem_center_iff]
    intro x
    obtain ⟨k,rfl⟩ := e.surjective x
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hj k)
  rw [Theory.PSL2.sl2_center_eq_bot,mem_bot] at he
  exact mem_bot.mpr (e.injective (he.trans e.map_one.symm))

private theorem large_elementary_inner {n : ℕ} (hn : 2 < n)
    (A : Subgroup (MulAut (Theory.PSL2.BinaryGroup n))) [IsElementaryAbelian 2 A]
    (hcard : 2^n ≤ Nat.card A) : A ≤ Theory.PSL2.inner (Theory.PSL2.BinaryField n) := by
  classical
  by_contra hnot
  obtain ⟨a,ha,hout⟩ := SetLike.not_le_iff_exists.mp hnot
  let π := Theory.PSL2.fieldProjection (Theory.PSL2.BinaryField n)
  let f := π.comp A.subtype
  let j : f.ker →* MulAut (Theory.PSL2.BinaryGroup n) := A.subtype.comp f.ker.subtype
  have hj : Function.Injective j := Subtype.coe_injective.comp Subtype.coe_injective
  have hi (x : f.ker) : j x ∈ Theory.PSL2.inner (Theory.PSL2.BinaryField n) := by
    rw [← Theory.PSL2.fieldProjection_ker]
    exact x.property
  have hc (x : f.ker) : Commute (j x) a :=
    congrArg Subtype.val (mul_comm (x : A) ⟨a,ha⟩)
  have hk : Nat.card f.ker ≤ 2^(n/2) :=
    Theory.PSL2.twoGroup_inner_centralizing_outer_card_le (by omega)
      (Theory.PSL2.binary_semilinear_coverage (by omega))
      ((IsElementaryAbelian.isPGroup 2 A).to_subgroup f.ker) j hj hi a
      (elemPow_eq_one_of_isElementaryAbelian a ha) hout hc
  let : IsCyclic (Theory.PSL2.BinaryField n ≃+* Theory.PSL2.BinaryField n) :=
    Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hr : Nat.card f.range ≤ 2 := by
    apply Nat.le_of_dvd (by decide : 0 < 2)
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 f.range
  have hb : Nat.card A ≤ 2^(n/2+1) := calc
    _ = Nat.card f.ker * Nat.card f.range := by
      rw [← Subgroup.index_ker,Subgroup.card_mul_index]
    _ ≤ 2^(n/2)*2 := Nat.mul_le_mul hk hr
    _ = 2^(n/2+1) := (pow_succ _ _).symm
  exact (Nat.not_le_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)))
    (hcard.trans hb)

private theorem inner_preimage {X J : Type*} [Group X] [Group J]
    (K : Subgroup X) [K.Normal] (e : K ≃* J)
    (hC : centralizer (K : Set X) = ⊥) :
    (MulAut.innerSubgroup J).comap
      ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : X →* MulAut K)) = K := by
  rw [← MulAut.map_innerSubgroup_congr e, ← comap_comap,
    comap_map_eq_self_of_injective (MulAut.congr e).injective,
    MulAut.conjNormal_comap_innerSubgroup, hC, sup_bot_eq]

private theorem large_field_containment {X F : Type*} [Group X] [Finite X]
    [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn : 2 < n) (hF : Nat.card F = 2^n)
    (J : Subgroup X) [J.Normal] (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hcore : pCore 2 X = ⊥) (hq : IsPGroup 2 (X ⧸ J))
    (A : Subgroup X) [IsElementaryAbelian 2 A] (hcard : Nat.card F ≤ Nat.card A) :
    A ≤ J := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (Theory.PSL2.BinaryField n) := Fintype.ofFinite _
  let fF : F ≃+* Theory.PSL2.BinaryField n := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hF.trans
      (GaloisField.card 2 n (by omega)).symm)
  let eJ : J ≃* Theory.PSL2.BinaryGroup n :=
    (e.trans (Theory.PSL2.sl2QuotientEquiv F)).trans (Atlas.fieldEquivPSL 2 fF)
  have hC := centralizer_eq_bot J (center_eq_bot_of_equiv e) hq hcore
  let φ : X →* MulAut (Theory.PSL2.BinaryGroup n) :=
    (MulAut.congr eJ).toMonoidHom.comp MulAut.conjNormal
  have hφ : Function.Injective φ := (MulAut.congr eJ).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot J hC)
  let : IsElementaryAbelian 2 (A.map φ) := IsElementaryAbelian.map φ
  have hi := large_elementary_inner hn (A.map φ) (by
    rw [card_map_of_injective hφ,← hF]
    exact hcard)
  have hp := inner_preimage J eJ hC
  intro a ha
  apply hp.le
  exact hi (mem_map_of_mem φ ha)

private theorem four_field_odd_witness {X F : Type*} [Group X] [Finite X]
    [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (J : Subgroup X) [J.Normal] (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hcore : pCore 2 X = ⊥) (hq : IsPGroup 2 (X ⧸ J))
    (A : Subgroup X) [IsElementaryAbelian 2 A] (hout : ¬ A ≤ J) :
    ∃ R : Subgroup X, R ≤ J ∧ Odd (Nat.card R) ∧
      A ≤ normalizer (R : Set X) ∧ ¬ A ≤ centralizer (R : Set X) := by
  obtain ⟨e₀⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let eJ := (e.trans (Theory.PSL2.sl2QuotientEquiv F)).trans e₀
  have hC := centralizer_eq_bot J (center_eq_bot_of_equiv e) hq hcore
  obtain ⟨a,ha,haJ⟩ := SetLike.not_le_iff_exists.mp hout
  have haout : (MulAut.conjNormal a : MulAut J) ∉ MulAut.innerSubgroup J := by
    intro h
    have he := MulAut.conjNormal_comap_innerSubgroup J
    rw [hC,sup_bot_eq] at he
    exact haJ (he.le h)
  obtain ⟨d,hd⟩ := Theory.SpecificGroups.Alternating.FiveExtensionAction.exists_equiv J eJ hC a haout
  let B := A.map d.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map d.toMonoidHom
  have hJ : J.map d.toMonoidHom = alternatingGroup (Fin 5) := by
    ext x
    constructor
    · rintro ⟨j,hj,rfl⟩
      change d j ∈ alternatingGroup (Fin 5)
      rw [show d j = (eJ ⟨j,hj⟩ : Equiv.Perm (Fin 5)) from hd ⟨j,hj⟩]
      exact (eJ ⟨j,hj⟩).property
    · intro hx
      obtain ⟨j,hj⟩ := eJ.surjective ⟨x,hx⟩
      exact ⟨j,j.property,(hd j).trans (congrArg Subtype.val hj)⟩
  have hB : ¬ B ≤ alternatingGroup (Fin 5) := by
    intro h
    apply hout
    intro x hx
    have hh : d x ∈ J.map d.toMonoidHom := by
      rw [hJ]
      exact h (mem_map_of_mem _ hx)
    obtain ⟨y,hy,he⟩ := hh
    exact d.injective he ▸ hy
  obtain ⟨P,hBP⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_le_sylow
  obtain ⟨C,_,hcard,hCJ,_,_,_,_,hn,hcomm,_⟩ :=
    Theory.SpecificGroups.SymmetricFive.CubicSelection.exists_outer_actor_selection P B hBP hB
  have hBback : B.map d.symm.toMonoidHom = A := by
    change (A.map d.toMonoidHom).map d.symm.toMonoidHom = A
    rw [map_map]; simp
  refine ⟨C.map d.symm.toMonoidHom,?_,?_,?_,?_⟩
  · have hh := map_mono (f := d.symm.toMonoidHom) hCJ
    rw [← hJ,map_map] at hh
    simpa using hh
  · rw [card_map_of_injective d.symm.injective,hcard]
    decide
  · have hh := map_mono (f := d.symm.toMonoidHom) hn
    rwa [hBback,map_equiv_normalizer_eq] at hh
  · intro hc
    have hCb : C = ⊥ := by
      rw [hcomm]
      apply commutator_eq_bot_iff_le_centralizer.mpr
      apply le_centralizer_iff.mpr
      rintro b ⟨x,hx,rfl⟩ c hcC
      have hh := hc hx (d.symm c) (mem_map_of_mem _ hcC)
      have he := congrArg d hh
      simpa only [map_mul, d.apply_symm_apply, d.symm_apply_apply,
        MulEquiv.coe_toMonoidHom] using he
    simp [hCb] at hcard

/-- An elementary actor of order at least the field, if outside the normal
rank-one group, acts nontrivially on an odd subgroup that it normalizes. -/
theorem rankOne_odd_witness {X F : Type*} [Group X] [Finite X]
    [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (J : Subgroup X) [J.Normal] (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hcore : pCore 2 X = ⊥) (hq : IsPGroup 2 (X ⧸ J))
    (A : Subgroup X) [IsElementaryAbelian 2 A]
    (hcard : Nat.card F ≤ Nat.card A) (hout : ¬ A ≤ J) :
    ∃ R : Subgroup X, R ≤ J ∧ Odd (Nat.card R) ∧
      A ≤ normalizer (R : Set X) ∧ ¬ A ≤ centralizer (R : Set X) := by
  by_cases htwo : n = 2
  · exact four_field_odd_witness (by simpa [htwo] using hF) J e hcore hq A hout
  · exact (hout (large_field_containment (by omega) hF J e hcore hq A hcard)).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.SylowPlacement
