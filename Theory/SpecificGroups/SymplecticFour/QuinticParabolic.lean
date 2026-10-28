module
public import Theory.GroupAction.SolvableLocalQuotient
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Reduction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearLocalKernel
public import Theory.SpecificGroups.SymplecticFour.SuzukiFixer
public import Theory.SpecificGroups.PSL2.BinaryOuter

/-!
# No solvable quintic actor normalized by a symplectic parabolic

A solvable automorphism subgroup preserving a full parabolic and normalized
by that parabolic acts trivially on its local SL₂ quotient. For a quintic
actor the actual inner--field decomposition has trivial field part, detected
by the quotient action. Its conjugating element lies in the same parabolic.
At odd binary field degree that parabolic has order prime to five.

The result includes transport through a specified component isomorphism.
Source application: Aschbacher--Smith 14.6.15, printed p.1035.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace Theory.SpecificGroups.SymplecticFour.QuinticParabolic
open DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) (ho : Odd n)

private theorem center_of_simple_perfect {X : Type*} [Group X]
    [IsSimpleGroup X] [Group.IsPerfect X] : center X = ⊥ := by
  rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hcomm := center_eq_top_iff.mp h
    exact (Group.IsPerfect.not_isMulCommutative X hcomm).elim

omit [Finite F] in
include hF hn in
private theorem simple_sl : IsSimpleGroup SL(2,F) := by
  have hq : 3 < Nat.card F := by
    rw [hF]
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
    norm_num at hh
    omega
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hq
  exact (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).isSimpleGroup

include hF ho in
private theorem no_inner_five_in_parabolic (P : Subgroup (Sp F))
    (hP : P = pointParabolic ∨ P = planeParabolic)
    (g : Sp F) (hg : g ∈ P) (ha : orderOf (MulAut.conj g) = 5) : False := by
  obtain ⟨m,hm⟩ := ho
  have hpar : InvolutionTypes.IsParabolic P := by
    refine ⟨1,?_⟩
    have hi : (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id (Sp F) := by
      ext x : 1
      simp
    simpa only [hi,map_id] using hP
  apply SuzukiFixer.parabolic_five_free m (hm ▸ hF) P hpar
  have hi := MulAut.conj_injective_of_center_eq_bot (EvenProjective.center_eq_bot (F := F))
  have hg5 : orderOf (⟨g,hg⟩ : P) = 5 :=
    (Subgroup.orderOf_mk _ _).trans ((orderOf_injective MulAut.conj hi g).symm.trans ha)
  exact hg5 ▸ orderOf_dvd_natCard (⟨g,hg⟩ : P)

include hF hn ho in
/-- A solvable actor normalized by a full parabolic cannot have order five
when the binary field degree is odd. -/
theorem no_solvable_quintic_actor
    (P : Subgroup (Sp F)) (hP : P = pointParabolic ∨ P = planeParabolic)
    (A : Subgroup (MulAut (Sp F))) [Group.IsSolvable A]
    (hfix : ∀ a ∈ A, P.map a.toMonoidHom = P)
    (hN : P.map (MulAut.conj : Sp F →* MulAut (Sp F)) ≤ normalizer (A : Set _))
    (a : MulAut (Sp F)) (ha : a ∈ A) (ha5 : orderOf a = 5) : False := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_eq_of_lt (by decide : 2=2^1) (Nat.pow_lt_pow_right (by decide) hn)
  obtain ⟨g,σ,he,_⟩ := OddFieldActors.inner_field_of_primePower hq
    (by decide : Odd 5) a (m := 1) (by simpa [ha5] using pow_orderOf_eq_one a)
  let := simple_sl hF hn
  rcases hP with rfl | rfl
  · have hL : ∀ b ∈ A, pointLocal.map b.toMonoidHom = pointLocal :=
      fun b hb => pointLocal_map hF hn b (hfix b hb)
    let := pointLocal_perfect hF hn
    let : IsSimpleGroup (pointLocal (F := F) ⧸ pCore 2 pointLocal) :=
      (pointLocalCoreQuotientEquiv hF hn).isSimpleGroup
    have hz := center_of_simple_perfect (X := pointLocal (F := F) ⧸ pCore 2 pointLocal)
    have hh := MulAut.solvable_subgroupStabilizerCoreAction_eq_one 2 pointLocal hz A
      (fun b hb => hL b hb) ((map_mono pointLocal_le).trans hN) ⟨a,hL a ha⟩ ha
    have hact : pointSL2Action hF hn a (hL a ha) = 1 := by
      apply MulEquiv.ext
      intro y
      obtain ⟨l,rfl⟩ := pointQuotient_surjective y
      rw [pointSL2Action_quotient]
      have hh' := congrArg (fun b : MulAut (pointLocal (F := F) ⧸ pCore 2 pointLocal) =>
        b (QuotientGroup.mk' (pCore 2 pointLocal) l)) hh
      change quotientAut (pCore 2 pointLocal)
        (MulAut.subgroupStabilizerAction pointLocal ⟨a,hL a ha⟩)
          (QuotientGroup.mk' (pCore 2 pointLocal) l) = QuotientGroup.mk' (pCore 2 pointLocal) l at hh'
      rw [quotientAut_apply_mk] at hh'
      have heq := congrArg (pointLocalCoreQuotientEquiv hF hn) hh'
      change pointLocalCoreQuotientEquiv hF hn (QuotientGroup.mk
        (restrict a pointLocal (hL a ha) l)) =
          pointLocalCoreQuotientEquiv hF hn (QuotientGroup.mk l) at heq
      rw [pointLocalCoreQuotientEquiv_mk,pointLocalCoreQuotientEquiv_mk] at heq
      exact heq
    have hσ : σ = RingEquiv.refl F := by
      apply pointSL2Action_semilinear_field_eq_refl hF hn g σ (he ▸ hL a ha)
      subst a
      exact hact
    have hae : a = MulAut.conj g := by
      rw [he,hσ]
      have hf : fieldAutomorphism (RingEquiv.refl F) = 1 := by ext x; rfl
      rw [hf,mul_one]
    have hg := point_semilinear_mem_parabolic hF hn g σ (he ▸ hL a ha)
    exact no_inner_five_in_parabolic hF ho pointParabolic (Or.inl rfl) g hg (hae ▸ ha5)
  · have hL : ∀ b ∈ A, planeLocal.map b.toMonoidHom = planeLocal :=
      fun b hb => planeLocal_map hF hn b (hfix b hb)
    let := planeLocal_perfect hF hn
    let : IsSimpleGroup (planeLocal (F := F) ⧸ pCore 2 planeLocal) :=
      (planeLocalCoreQuotientEquiv hF hn).isSimpleGroup
    have hz := center_of_simple_perfect (X := planeLocal (F := F) ⧸ pCore 2 planeLocal)
    have hh := MulAut.solvable_subgroupStabilizerCoreAction_eq_one 2 planeLocal hz A
      (fun b hb => hL b hb) ((map_mono planeLocal_le).trans hN) ⟨a,hL a ha⟩ ha
    have hact : planeSL2Action hF hn a (hL a ha) = 1 := by
      apply MulEquiv.ext
      intro y
      obtain ⟨l,rfl⟩ := Plane.quotientMap_surjective y
      rw [planeSL2Action_quotient]
      have hh' := congrArg (fun b : MulAut (planeLocal (F := F) ⧸ pCore 2 planeLocal) =>
        b (QuotientGroup.mk' (pCore 2 planeLocal) l)) hh
      change quotientAut (pCore 2 planeLocal)
        (MulAut.subgroupStabilizerAction planeLocal ⟨a,hL a ha⟩)
          (QuotientGroup.mk' (pCore 2 planeLocal) l) = QuotientGroup.mk' (pCore 2 planeLocal) l at hh'
      rw [quotientAut_apply_mk] at hh'
      have heq := congrArg (planeLocalCoreQuotientEquiv hF hn) hh'
      change planeLocalCoreQuotientEquiv hF hn (QuotientGroup.mk
        (restrict a planeLocal (hL a ha) l)) =
          planeLocalCoreQuotientEquiv hF hn (QuotientGroup.mk l) at heq
      rw [planeLocalCoreQuotientEquiv_mk,planeLocalCoreQuotientEquiv_mk] at heq
      exact heq
    have hσ : σ = RingEquiv.refl F := by
      apply planeSL2Action_semilinear_field_eq_refl hF hn g σ (he ▸ hL a ha)
      subst a
      exact hact
    have hae : a = MulAut.conj g := by
      rw [he,hσ]
      have hf : fieldAutomorphism (RingEquiv.refl F) = 1 := by ext x; rfl
      rw [hf,mul_one]
    have hg := plane_semilinear_mem_parabolic hF hn g σ (he ▸ hL a ha)
    exact no_inner_five_in_parabolic hF ho planeParabolic (Or.inr rfl) g hg (hae ▸ ha5)
include hF hn ho in
/-- The same obstruction in the specified component coordinates. -/
theorem no_solvable_quintic_actor_of_equiv
    {C : Type*} [Group C] [Finite C] (e : C ≃* Sp F)
    (P : Subgroup C)
    (hP : P.map e.toMonoidHom = pointParabolic ∨ P.map e.toMonoidHom = planeParabolic)
    (A : Subgroup (MulAut C)) [Group.IsSolvable A]
    (hfix : ∀ a ∈ A, P.map a.toMonoidHom = P)
    (hN : P.map (MulAut.conj : C →* MulAut C) ≤ normalizer (A : Set _))
    (a : MulAut C) (ha : a ∈ A) (ha5 : orderOf a = 5) : False := by
  let f := (MulAut.congr e).toMonoidHom
  let B := A.map f
  let : Group.IsSolvable B := Group.isSolvable_of_surjective (f.subgroupMap_surjective A)
  apply no_solvable_quintic_actor hF hn ho (P.map e.toMonoidHom) hP B ?_ ?_
    (MulAut.congr e a) (mem_map_of_mem f ha) ((MulAut.congr e).orderOf_eq a |>.trans ha5)
  · rintro _ ⟨b,hb,rfl⟩
    have he : (f b).toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp b.toMonoidHom := by
      ext x : 1
      change e (b (e.symm (e x))) = e (b x)
      rw [e.symm_apply_apply]
    rw [map_map,he,←map_map,hfix b hb]
  · have hh := (map_mono (f := f) hN).trans (le_normalizer_map f)
    have he : f.comp (MulAut.conj : C →* MulAut C) =
        (MulAut.conj : Sp F →* MulAut (Sp F)).comp e.toMonoidHom := by
      ext x : 1
      exact MulAut.congr_conj e x
    rwa [map_map,he,←map_map] at hh

end Theory.SpecificGroups.SymplecticFour.QuinticParabolic
