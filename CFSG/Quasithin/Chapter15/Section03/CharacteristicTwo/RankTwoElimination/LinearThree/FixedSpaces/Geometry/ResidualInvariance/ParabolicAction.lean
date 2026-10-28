module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.ResidualInvariance.LocalActions
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.SymmetricModels
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Mathlib.GroupTheory.Perm.Fin

/-!
# The moved residual in the actual component parabolic

Local normalization by S_L = S ∩ L and two-perfectness identify Y_L with
O²(Y_L S_L). Its image under the actual quotient L → L/O₂(L) is therefore
the two-residual of the marked parabolic. The concrete point and line
parabolics are S₄, including after an arbitrary inner conjugation.

In S₄, every supplement to A₄ contains an odd permutation t. A finite
kernel check expresses every even permutation as a product of two
commutators with t, proving [A₄,T] = A₄. Finally D = [Y_L,S_L] is normal
inside Y_L. Equality of their quotient images makes Y_L/D a two-group;
two-perfectness gives D = Y_L. Neither S-invariance of L or Y_L nor
two-perfectness of D is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.23, printed p.1128, with the local S_L action from 15.3.17,
printed p.1126, and the actual minimal parabolic M_L = Y_L S_L.
-/

public section
open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.ResidualInvariance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem symmetric_four_commutator_factorization : ∀ t : Equiv.Perm (Fin 4), t ∉ alternatingGroup (Fin 4) →
    ∀ a : Equiv.Perm (Fin 4), a ∈ alternatingGroup (Fin 4) →
    ∃ u v : Equiv.Perm (Fin 4), u ∈ alternatingGroup (Fin 4) ∧
      v ∈ alternatingGroup (Fin 4) ∧ a = ⁅u,t⁆ * ⁅v,t⁆ := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel


private theorem alternating_commutator_supplement (T : Subgroup (Equiv.Perm (Fin 4)))
    (hT : alternatingGroup (Fin 4) ⊔ T = ⊤) :
    ⁅alternatingGroup (Fin 4), T⁆ = alternatingGroup (Fin 4) := by
  have hout : ¬ T ≤ alternatingGroup (Fin 4) := by
    intro h
    have ht : alternatingGroup (Fin 4) = ⊤ := (sup_eq_left.mpr h).symm.trans hT
    have hs : Equiv.swap (0 : Fin 4) 1 ∈ alternatingGroup (Fin 4) := by rw [ht]; trivial
    have hns : Equiv.swap (0 : Fin 4) 1 ∉ alternatingGroup (Fin 4) := by
      simp [Equiv.Perm.mem_alternatingGroup]
    exact hns hs
  obtain ⟨t, ht, hta⟩ := SetLike.not_le_iff_exists.mp hout
  refine le_antisymm (commutator_le_left _ _) ?_
  intro a ha
  obtain ⟨u, v, hu, hv, rfl⟩ := symmetric_four_commutator_factorization t hta a ha
  exact mul_mem (commutator_mem_commutator hu ht) (commutator_mem_commutator hv ht)


private theorem symmetric_residual_commutator (P B : Subgroup SL)
    (e : P ≃* Equiv.Perm (Fin 4)) (hBP : B ≤ P)
    (hgen : residual P ⊔ B = P) : ⁅residual P, B⁆ = residual P := by
  have hg : pResidual 2 P ⊔ B.subgroupOf P = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hBP,
      ← MonoidHom.range_eq_map, range_subtype]
    exact hgen
  have hm : (pResidual 2 P).map e.toMonoidHom = alternatingGroup (Fin 4) := by
    rw [map_pResidual 2 e, Equiv.Perm.twoResidual_eq_alternating]
  have hgm := congrArg (fun A : Subgroup P => A.map e.toMonoidHom) hg
  rw [Subgroup.map_sup, hm, map_top_of_surjective _ e.surjective] at hgm
  have hc : ⁅pResidual 2 P, B.subgroupOf P⁆ = pResidual 2 P := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_commutator, hm]
    exact alternating_commutator_supplement _ hgm
  have hcm := congrArg (fun A : Subgroup P => A.map P.subtype) hc
  rw [map_commutator, map_subgroupOf_eq_of_le hBP] at hcm
  exact hcm

private theorem parabolic_residual_commutator (P B : Subgroup SL)
    (hP : P = pointParabolicSL ∨ P = lineParabolicSL) (g : SL)
    (hB : B ≤ P.conjBy g) (hgen : residual (P.conjBy g) ⊔ B = P.conjBy g) :
    ⁅residual (P.conjBy g), B⁆ = residual (P.conjBy g) := by
  have e : Nonempty (P ≃* Equiv.Perm (Fin 4)) := by
    rcases hP with rfl | rfl
    · exact ⟨pointEquivSymmetric⟩
    · exact ⟨lineEquivSymmetric⟩
  obtain ⟨e⟩ := e
  exact symmetric_residual_commutator (P.conjBy g) B
    (((MulAut.conj g).subgroupMap P).symm.trans e) hB hgen

private theorem lift_commutator {H K : Type*} [Group H] [Group K]
    (A B : Subgroup H) (f : H →* K) (hf : IsPGroup 2 f.ker)
    (hA : IsPPerfect 2 A) (hn : B ≤ normalizer (A : Set H))
    (hm : (⁅A,B⁆).map f = A.map f) : ⁅A,B⁆ = A := by
  let D := ⁅A,B⁆
  have hDA : D ≤ A := le_normalizer_iff_commutator_le_left.mp hn
  let N := D.subgroupOf A
  let _ : N.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left A B)
  let q := f.comp A.subtype
  have hq : IsPGroup 2 q.ker := hf.comap_subtype
  have hgen : N ⊔ q.ker = ⊤ := by
    apply top_unique
    intro a ha
    obtain ⟨d, hd, he⟩ := hm.ge (mem_map_of_mem f a.property)
    let d' : A := ⟨d, hDA hd⟩
    have hdk : d'⁻¹ * a ∈ q.ker := by
      change f (d⁻¹ * (a : H)) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    have hdn : d' ∈ N := hd
    simpa only [mul_inv_cancel_left] using mul_mem_sup hdn hdk
  have hN : N = ⊤ := hA N inferInstance (isPGroup_quotient_of_sup_eq_top N q.ker hq hgen)
  apply le_antisymm hDA
  intro a ha
  exact (show (⟨a,ha⟩ : A) ∈ N by rw [hN]; trivial)

variable {G : Type*} [Group G] [Finite G]

/-- Local normalization by S ∩ L identifies the actual quotient image of Y_L
with the intrinsic two-residual of the image parabolic. -/
theorem YL_image_of_component_parabolic (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL) (M : Subgroup SL)
    (hM : ((YL d L ⊔ (d.S ⊓ L)).subgroupOf L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) = M) :
    ((YL d L).subgroupOf L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) = residual M := by
  have hAL : YL d L ≤ L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hp := ComponentIntersection.intersectionResidual_isPPerfect d.Yplus L
  have hA : IsPPerfect 2 ((YL d L).subgroupOf L) :=
    hp.of_surjective (subgroupOfEquivOfLe hAL).symm.toMonoidHom
      (subgroupOfEquivOfLe hAL).symm.surjective
  have hB : IsPGroup 2 (d.S ⊓ L : Subgroup G) :=
    d.T.isPGroup'.to_le (inf_le_left.trans (show d.S ≤ (d.T : Subgroup G) from inf_le_left))
  have hn : (d.S ⊓ L).subgroupOf L ≤ normalizer (((YL d L).subgroupOf L : Subgroup L) : Set L) :=
    (comap_mono (componentSylow_normalizes_YL d L)).trans (le_normalizer_comap L.subtype)
  have hr := embedded_pResidual_join_pGroup ((YL d L).subgroupOf L)
    ((d.S ⊓ L).subgroupOf L) hA hB.comap_subtype hn
  rw [← subgroupOf_sup hAL inf_le_right] at hr
  have ht := map_embedded_pResidual 2 ((YL d L ⊔ (d.S ⊓ L)).subgroupOf L)
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  rw [hr, hM] at ht
  exact ht

/-- The actual marked point or line parabolic forces Y_L = [Y_L,S ∩ L].
The marking may be any inner conjugate, and no normalization by all of S
is assumed. -/
theorem YL_componentSylow_commutator_eq_of_parabolic (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL) (P : Subgroup SL)
    (hP : P = pointParabolicSL ∨ P = lineParabolicSL) (g : SL)
    (hM : ((YL d L ⊔ (d.S ⊓ L)).subgroupOf L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) = P.conjBy g) :
    ⁅YL d L, d.S ⊓ L⁆ = YL d L := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let A := (YL d L).subgroupOf L
  let B := (d.S ⊓ L).subgroupOf L
  have hAL : YL d L ≤ L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hA : IsPPerfect 2 A :=
    (ComponentIntersection.intersectionResidual_isPPerfect d.Yplus L).of_surjective
      (subgroupOfEquivOfLe hAL).symm.toMonoidHom (subgroupOfEquivOfLe hAL).symm.surjective
  have hn : B ≤ normalizer (A : Set L) :=
    (comap_mono (componentSylow_normalizes_YL d L)).trans (le_normalizer_comap L.subtype)
  have hf : IsPGroup 2 f.ker := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hAm : A.map f = residual (P.conjBy g) := YL_image_of_component_parabolic d L e _ hM
  have hgen : residual (P.conjBy g) ⊔ B.map f = P.conjBy g := by
    rw [← hAm, ← Subgroup.map_sup]
    change (A ⊔ B).map f = P.conjBy g
    simpa only [A, B, ← subgroupOf_sup hAL inf_le_right] using hM
  have hcomm : (⁅A,B⁆).map f = A.map f := by
    rw [map_commutator, hAm]
    exact parabolic_residual_commutator P (B.map f) hP g
      (le_sup_right.trans hgen.le) hgen
  have hc := congrArg (fun X : Subgroup L => X.map L.subtype)
    (lift_commutator A B f hf hA hn hcomm)
  simpa only [map_commutator, A, B, map_subgroupOf_eq_of_le hAL,
    map_subgroupOf_eq_of_le (show d.S ⊓ L ≤ L from inf_le_right)] using hc

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.ResidualInvariance
end
