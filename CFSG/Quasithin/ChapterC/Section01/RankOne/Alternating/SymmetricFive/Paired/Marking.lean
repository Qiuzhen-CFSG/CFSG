module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.Exchange
import Mathlib.Tactic
/-!
# Transposition-product markings in the prescribed paired Sylow

Stable offenders split on the two axes, so their subgroup inside an arbitrary
product Sylow is the product of the two individual stable-family subgroups.
The genuine five-letter Sylow marking therefore identifies both factors
simultaneously, without changing the original Sylow subgroup.

Source: Aschbacher–Smith E.2.3(3), pp.216–217.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.SymmetricFive.Paired
open BinaryPermutation ChapterB.Offenders

private theorem axis_offender {A : Subgroup Sym}
    (hA : IsOffender (coreRepresentation (Fin 5)) A) :
    IsBestOffender (coreRepresentation (Fin 5)) A := by
  exact (isBestOffender_iff_of_not_strong _ core_not_strong A).mpr
    ⟨hA.1,le_antisymm hA.2 (Nat.le_of_not_gt (fun h => core_not_strong ⟨A,hA.1,h⟩))⟩

private theorem first_projection_mem {P : Set (Subgroup (Sym × Sym))}
    (hP : IsStable action P) {A : Subgroup (Sym × Sym)} (hA : A ∈ P)
    (hne : A.map (MonoidHom.fst Sym Sym) ≠ ⊥) :
    (A.map (MonoidHom.fst Sym Sym)).map (MonoidHom.inl Sym Sym) ∈ P := by
  obtain ⟨he,h₁,_⟩ := offender_product_of_not_strong _ _ core_not_strong core_not_strong
    ((hP.2.1 A hA).isOffender action)
  have hb := (axis_offender (h₁.resolve_left hne)).map_of_fixedCodim
    (coreRepresentation (Fin 5)) action (MonoidHom.inl Sym Sym)
    (fun _ _ h => congrArg Prod.fst h) (fun B => (fixedCodim_axis_left B).symm)
  apply stable_downward hP hA hb
  rintro _ ⟨a,ha,rfl⟩
  rw [he]
  exact ⟨ha,one_mem _⟩

private theorem second_projection_mem {P : Set (Subgroup (Sym × Sym))}
    (hP : IsStable action P) {A : Subgroup (Sym × Sym)} (hA : A ∈ P)
    (hne : A.map (MonoidHom.snd Sym Sym) ≠ ⊥) :
    (A.map (MonoidHom.snd Sym Sym)).map (MonoidHom.inr Sym Sym) ∈ P := by
  obtain ⟨he,_,h₂⟩ := offender_product_of_not_strong _ _ core_not_strong core_not_strong
    ((hP.2.1 A hA).isOffender action)
  have hb := (axis_offender (h₂.resolve_left hne)).map_of_fixedCodim
    (coreRepresentation (Fin 5)) action (MonoidHom.inr Sym Sym)
    (fun _ _ h => congrArg Prod.snd h) (fun B => (fixedCodim_axis_right B).symm)
  apply stable_downward hP hA hb
  rintro _ ⟨a,ha,rfl⟩
  rw [he]
  exact ⟨one_mem _,ha⟩

theorem generatedBy_product {P : Set (Subgroup (Sym × Sym))} (hP : IsStable action P)
    (R S : Subgroup Sym) :
    generatedBy P (R.prod S) =
      (generatedBy {B : Subgroup Sym | B.map (MonoidHom.inl Sym Sym) ∈ P} R).prod
        (generatedBy {B : Subgroup Sym | B.map (MonoidHom.inr Sym Sym) ∈ P} S) := by
  apply le_antisymm
  · apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA,hARS⟩
    obtain ⟨he,_,_⟩ := offender_factors ((hP.2.1 A hA).isOffender action)
    rw [he]
    apply Subgroup.prod_mono
    · by_cases hz : A.map (MonoidHom.fst Sym Sym) = ⊥
      · rw [hz]; exact bot_le
      · refine le_iSup_of_le _ (le_iSup_of_le ⟨first_projection_mem hP hA hz,?_⟩ le_rfl)
        rintro _ ⟨a,ha,rfl⟩
        exact (hARS ha).1
    · by_cases hz : A.map (MonoidHom.snd Sym Sym) = ⊥
      · rw [hz]; exact bot_le
      · refine le_iSup_of_le _ (le_iSup_of_le ⟨second_projection_mem hP hA hz,?_⟩ le_rfl)
        rintro _ ⟨a,ha,rfl⟩
        exact (hARS ha).2
  · have hl : (generatedBy {B : Subgroup Sym | B.map (MonoidHom.inl Sym Sym) ∈ P} R).map
        (MonoidHom.inl Sym Sym) ≤ generatedBy P (R.prod S) := by
      rw [map_le_iff_le_comap]
      apply iSup_le
      intro A
      apply iSup_le
      rintro ⟨hA,hAR⟩
      apply map_le_iff_le_comap.mp
      refine le_iSup_of_le (A.map (MonoidHom.inl Sym Sym)) (le_iSup_of_le ⟨hA,?_⟩ le_rfl)
      rintro _ ⟨a,ha,rfl⟩
      exact ⟨hAR ha,one_mem _⟩
    have hr : (generatedBy {B : Subgroup Sym | B.map (MonoidHom.inr Sym Sym) ∈ P} S).map
        (MonoidHom.inr Sym Sym) ≤ generatedBy P (R.prod S) := by
      rw [map_le_iff_le_comap]
      apply iSup_le
      intro A
      apply iSup_le
      rintro ⟨hA,hAS⟩
      apply map_le_iff_le_comap.mp
      refine le_iSup_of_le (A.map (MonoidHom.inr Sym Sym)) (le_iSup_of_le ⟨hA,?_⟩ le_rfl)
      rintro _ ⟨a,ha,rfl⟩
      exact ⟨one_mem _,hAS ha⟩
    intro x hx
    have he : x = (x.1,1) * (1,x.2) := by ext <;> simp
    rw [he]
    exact mul_mem (hl (mem_map.mpr ⟨x.1,hx.1,rfl⟩)) (hr (mem_map.mpr ⟨x.2,hx.2,rfl⟩))

private theorem pair_sylow (R : Sylow 2 (Sym × Sym)) :
    ∃ P Q : Sylow 2 Sym, (R : Subgroup (Sym × Sym)) = (P : Subgroup Sym).prod Q := by
  let P := R.mapSurjective (f := MonoidHom.fst Sym Sym) (fun g => ⟨(g,1),rfl⟩)
  let Q := R.mapSurjective (f := MonoidHom.snd Sym Sym) (fun g => ⟨(1,g),rfl⟩)
  have hp : IsPGroup 2 (P × Q) := by
    obtain ⟨m,hm⟩ := P.isPGroup'.exists_card_eq
    obtain ⟨n,hn⟩ := Q.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := m+n) (by rw [Nat.card_prod,hm,hn,pow_add])
  refine ⟨P,Q,(R.is_maximal' (hp.of_equiv ((P : Subgroup Sym).prodEquiv (Q : Subgroup Sym)).symm) ?_).symm⟩
  intro x hx
  exact ⟨mem_map_of_mem (MonoidHom.fst Sym Sym) hx,mem_map_of_mem (MonoidHom.snd Sym Sym) hx⟩

private theorem inverse_conjugate (A B : Subgroup Sym) (g : Sym)
    (he : A.map (MulAut.conj g).toMonoidHom = B) :
    A = B.map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [←he,map_map]
  have hh : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id Sym := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [hh,Subgroup.map_id]

theorem exists_sylow_marking {P : Set (Subgroup (Sym × Sym))} (hP : IsStable action P)
    (hn₁ : ∃ A ∈ P, A.map (MonoidHom.fst Sym Sym) ≠ ⊥)
    (hn₂ : ∃ A ∈ P, A.map (MonoidHom.snd Sym Sym) ≠ ⊥)
    (R : Sylow 2 (Sym × Sym)) :
    ∃ a b : Sym, generatedBy P (R : Subgroup (Sym × Sym)) =
      ((D 5).map (MulAut.conj a).toMonoidHom).prod
        ((D 5).map (MulAut.conj b).toMonoidHom) := by
  obtain ⟨R₁,R₂,hR⟩ := pair_sylow R
  obtain ⟨a,ha⟩ := exists_generatedBy_marking (stable_left_axis hP hn₁) R₁
  obtain ⟨b,hb⟩ := exists_generatedBy_marking (stable_right_axis hP hn₂) R₂
  exact ⟨a⁻¹,b⁻¹,by rw [hR,generatedBy_product hP,inverse_conjugate _ _ a ha,inverse_conjugate _ _ b hb]⟩
end CFSG.Quasithin.ChapterC.SymmetricFive.Paired
