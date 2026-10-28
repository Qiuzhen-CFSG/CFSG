module
public import Theory.GroupTheory.SymmetricThreeCubicNormality
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.NormalizedSupplement

/-!
# Lifting the odd intersection of a normal Thompson span

Every Sylow-invariant subgroup of the odd residual of a normal S₃ or
S₃ × S₃ span is normal: its order is one, three or nine, and the cubic
case is the two-direction orbit argument. Through a two-group kernel,
the two-residual of its full preimage is therefore normal and maps onto
that intersection. A Sylow-invariant original actor contains this lift.

Chapter13's CoveredResidual applies the lift to the actual L₁ and then
uses the earlier 13.3.9 classification of normal two-perfect subgroups.
This avoids assuming that the whole covered L₁ normalizes R₁.
Source: Aschbacher–Smith 13.4.8, printed p.905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.SymmetricThreeCubicNormality
variable {G : Type*} [Group G] [Finite G]
local notation "S3" => Equiv.Perm (Fin 3)

/-- Every Sylow-invariant subgroup of the specified odd residual is normal. -/
theorem residual_subgroup_normal_of_sylow_normalizes (I B : Subgroup G) [I.Normal]
    (hm : Nonempty (I ≃* S3) ∨ Nonempty (I ≃* (S3 × S3)))
    (S : Sylow 2 G) (hB : B ≤ (pResidual 2 I).map I.subtype)
    (hS : (S : Subgroup G) ≤ normalizer (B : Set G)) : B.Normal := by
  let R := (pResidual 2 I).map I.subtype
  have hc : Nat.card R = 3 ∨ Nat.card R = 9 := by
    rw [card_map_of_injective I.subtype_injective]
    rcases hm with he | he
    · obtain ⟨e⟩ := he
      left
      rw [← card_map_of_injective (K := pResidual 2 I) (f := e.toMonoidHom) e.injective,
        map_pResidual,Equiv.Perm.twoResidual_eq_alternating,nat_card_alternatingGroup,Nat.card_fin]
      rfl
    · obtain ⟨e⟩ := he
      right
      rw [← card_map_of_injective (K := pResidual 2 I) (f := e.toMonoidHom) e.injective,
        map_pResidual]
      exact SymmetricThreeProductResidual.residual_card
  have hdiv : Nat.card B ∣ 9 := (card_dvd_of_le hB).trans (hc.elim (fun h => by rw [h]; decide)
    (fun h => h ▸ dvd_rfl))
  have hb := Nat.mem_divisors.mpr ⟨hdiv,by decide⟩
  have hn : (9 : ℕ).divisors = {1,3,9} := by decide
  rw [hn,Finset.mem_insert,Finset.mem_insert,Finset.mem_singleton] at hb
  rcases hb with hb | hb | hb
  · rw [card_eq_one.mp hb]
    infer_instance
  · exact cubic_normal_of_sylow_normalizes I B hm S hB hb hS
  · have he : B = R := eq_of_le_of_card_ge hB (by rcases hc with hc | hc <;> omega)
    rw [he]
    infer_instance

/-- The intersection has a normal two-perfect lift inside the original actor. -/
theorem residual_intersection_lift {K : Type*} [Group K] [Finite K]
    (f : G →* K) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (I : Subgroup K) [I.Normal]
    (hm : Nonempty (I ≃* S3) ∨ Nonempty (I ≃* (S3 × S3)))
    (S : Sylow 2 G) (A : Subgroup G)
    (hSA : (S : Subgroup G) ≤ normalizer (A : Set G)) :
    ∃ Y : Subgroup G, Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ A ∧
      Y.map f = ((pResidual 2 I).map I.subtype) ⊓ A.map f := by
  let R := (pResidual 2 I).map I.subtype
  let B := A.map f
  let C := R ⊓ B
  let P := C.comap f
  let Y := (pResidual 2 P).map P.subtype
  have hnB : (S.mapSurjective hf : Subgroup K) ≤ normalizer (B : Set K) :=
    (map_mono hSA).trans (A.le_normalizer_map f)
  let : R.Normal := inferInstanceAs ((pResidual 2 I).map I.subtype).Normal
  have hnC : (S.mapSurjective hf : Subgroup K) ≤ normalizer (C : Set K) :=
    (le_inf le_normalizer_of_normal hnB).trans inf_normalizer_le_normalizer_inf
  let : C.Normal := residual_subgroup_normal_of_sylow_normalizes I C hm
    (S.mapSurjective hf) inf_le_left hnC
  let : P.Normal := inferInstanceAs (C.comap f).Normal
  have hY : IsPPerfect 2 Y := isPPerfect_embedded_pResidual 2 P
  have hC : IsPGroup 3 C := ((SymmetricThreeSylowNormalizer.residual_threeGroup_of_models hm).map
    I.subtype).to_le inf_le_left
  have hCperfect : IsPPerfect 2 C := by
    apply (pResidual_eq_top_iff 2 C).mp
    apply top_unique
    intro c _
    obtain ⟨n,hn⟩ := hC.exists_orderOf_dvd_pow c
    exact mem_pResidual_of_orderOf_coprime (((by decide : Nat.Coprime 2 3).pow_right n).of_dvd_right hn)
  have him : Y.map f = C := by
    rw [map_embedded_pResidual]
    rw [show P.map f = C from map_comap_eq_self_of_surjective hf C,
      (pResidual_eq_top_iff 2 C).mpr hCperfect,← MonoidHom.range_eq_map,range_subtype]
  refine ⟨Y,inferInstance,hY,?_,him⟩
  apply le_of_isPPerfect_of_le_sup_of_normalizes Y A f.ker hY hk
    ((hk.le_sylow_of_normal S).trans hSA)
  rw [← comap_map_eq]
  exact map_le_iff_le_comap.mp (him ▸ inf_le_right)
end Theory.GroupTheory.SymmetricThreeCubicNormality
