module
public import Theory.Mathieu.M24.LocalGeometry.SextetCore
public import Theory.Mathieu.M24.ChapterHStabilizers.Involutions
public import Theory.GroupTheory.DoubleCoverInvolutionLifting
public import Mathlib.GroupTheory.Sylow

/-!
# Genuine involutions above the native M24 sextet core

Both native involution classes meet the elementary order-64 sextet core.
The certified generators have respectively eight and zero fixed points,
so the existing two-class theorem proves the fusion. An elementary preimage
of this core therefore lifts every quotient involution through an arbitrary
surjective covering map. If the full kernel is a two-group, an involution
whose image lies in a given Sylow two-subgroup lifts into that same Sylow.

Source: Aschbacher--Smith 8.2.8(6), printed p.719, using H.14--H.16,
refs/quasithin.pdf. Native catalogue attribution: LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup
namespace MathieuCode.NormalizedShadowRows.CodeInvolutions
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers Sporadic.Mathieu.M24InvolutionCentralizers

private theorem generator_order (i : Fin 6) : orderOf (EvenCandidates.generator 1 i) = 2 := by
  apply orderOf_eq_prime (EvenCandidates.generator_square 1 i)
  intro h
  have hh : (fun p => EvenCandidates.generatorPoint 1 i p) = id := by
    funext p
    have hp := congrArg (fun g : M24 => g.val p) h
    change (EvenCandidates.generator 1 i).val p = p at hp
    rw [EvenCandidates.generator_apply] at hp
    exact hp
  have hn : ∀ i : Fin 6, (fun p => EvenCandidates.generatorPoint 1 i p) ≠ id := by
    decide +kernel
  exact hn i hh

private theorem generator_fixed (i : Fin 6) :
    fixedPoints (EvenCandidates.generator 1 i) =
      Finset.univ.filter (fun p => EvenCandidates.generatorPoint 1 i p = p) := by
  classical
  ext p
  simp only [mem_fixedPoints, Finset.mem_filter, Finset.mem_univ, true_and]
  change (EvenCandidates.generator 1 i).val p = p ↔ _
  rw [EvenCandidates.generator_apply]

private theorem generator_zero_class : IsConj involution2A (EvenCandidates.generator 1 0) := by
  rcases involution_classes _ (generator_order 0) with h | h
  · exact h
  · have he := class2B_fixed_empty h
    have hc : (fixedPoints (EvenCandidates.generator 1 0)).card = 8 := by
      rw [generator_fixed]
      decide +kernel
    rw [he, Finset.card_empty] at hc
    omega

private theorem generator_three_class : IsConj involution2B (EvenCandidates.generator 1 3) := by
  rcases involution_classes _ (generator_order 3) with h | h
  · have hc := m24Blocks_card _ (class2A_fixed_octad h)
    have he : (fixedPoints (EvenCandidates.generator 1 3)).card = 0 := by
      rw [generator_fixed]
      decide +kernel
    omega
  · exact h

theorem involution_fused_into_sextet_core (x : M24) (hx : orderOf x = 2) :
    ∃ y ∈ SextetCore.core, orderOf y = 2 ∧ IsConj y x := by
  have h (i : Fin 6) :
      MulAut.conj SextetCore.transport (EvenCandidates.generator 1 i) ∈ SextetCore.core := by
    rw [← SextetCore.candidate_conjugate_core]
    exact mem_map_of_mem _ (EvenCandidates.generator_mem 1 i)
  have hc (i : Fin 6) : IsConj (EvenCandidates.generator 1 i)
      (MulAut.conj SextetCore.transport (EvenCandidates.generator 1 i)) :=
    isConj_iff.mpr ⟨SextetCore.transport, rfl⟩
  rcases involution_classes x hx with hA | hB
  · refine ⟨_,h 0,(MulAut.conj SextetCore.transport).orderOf_eq _ |>.trans (generator_order 0),?_⟩
    exact (hc 0).symm.trans (generator_zero_class.symm.trans hA)
  · refine ⟨_,h 3,(MulAut.conj SextetCore.transport).orderOf_eq _ |>.trans (generator_order 3),?_⟩
    exact (hc 3).symm.trans (generator_three_class.symm.trans hB)

/-- An elementary preimage of the sextet core lifts both involution classes,
without any restriction on the full covering kernel. -/
theorem involution_lift_of_elementary_sextet
    {P : Type*} [Group P] (f : P →* M24) (hf : Function.Surjective f)
    (A : Subgroup P) [IsElementaryAbelian 2 A] (c : M24)
    (hA : (A.map f).map (MulAut.conj c).toMonoidHom = SextetCore.core)
    (x : M24) (hx : orderOf x = 2) :
    ∃ t : P, f t = x ∧ orderOf t = 2 := by
  obtain ⟨y,hy,hy2,hyx⟩ := involution_fused_into_sextet_core x hx
  rw [←hA] at hy
  obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
  obtain ⟨t,ht,rfl⟩ := mem_map.mp hb
  have ht2 : orderOf t = 2 := by
    apply orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t ht)
    intro ht1
    simp only [ht1,map_one,orderOf_one] at hy2
    omega
  have hconj : IsConj (f t) x :=
    (isConj_iff.mpr ⟨c,rfl⟩).trans hyx
  exact Theory.GroupTheory.DoubleCoverInvolutionLifting.involution_lift_of_isConj f hf ht2 hconj

/-- For a two-group kernel, these genuine involutions lie in the original
Sylow subgroup whenever their images do. -/
theorem involution_lift_in_sylow
    {P : Type*} [Group P] [Finite P] (f : P →* M24)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (A : Subgroup P) [IsElementaryAbelian 2 A] (c : M24)
    (hA : (A.map f).map (MulAut.conj c).toMonoidHom = SextetCore.core)
    (T : Sylow 2 P) (x : M24) (hx : orderOf x = 2)
    (hxT : x ∈ (T : Subgroup P).map f) :
    ∃ t : T, f t = x ∧ orderOf t = 2 := by
  obtain ⟨t,ht,ht2⟩ := involution_lift_of_elementary_sextet f hf A c hA x hx
  have hpre : ((T : Subgroup P).map f).comap f = (T : Subgroup P) :=
    comap_map_eq_self (hk.le_sylow_of_normal T)
  have htT : t ∈ (T : Subgroup P) := by
    rw [←hpre]
    change f t ∈ (T : Subgroup P).map f
    rw [ht]
    exact hxT
  exact ⟨⟨t,htT⟩,ht,(Subgroup.orderOf_coe (⟨t,htT⟩ : (T : Subgroup P))).symm.trans ht2⟩

end MathieuCode.NormalizedShadowRows.CodeInvolutions
