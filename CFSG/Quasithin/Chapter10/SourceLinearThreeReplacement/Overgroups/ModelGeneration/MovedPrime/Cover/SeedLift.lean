module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Cover.Inputs
public import Theory.GroupTheory.NormalizerAction.Simple
public import Theory.GroupTheory.ComponentLocalOrbitSolvable

/-!
# Solvable seeds lifted from the literal component automizer

Pull a Sylow-invariant solvable subgroup of the component image back to K
along the injective map K → N(K)/C(K). Joining that seed with the full
ambient Sylow is solvable: its conjugates in distinct components commute.
A generating family of seeds therefore gives the required selected cover.
The equalities here use the actual normalizer quotient and component map.

Source: Aschbacher--Smith E.1.11--12 and the component-pair reduction in
E.2.2, printed pp.212--216; reused in 10.3.3, printed p.756.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover
universe u
variable {H : Type u} [Group H] [Finite H]

theorem cover_of_component_seeds (S : Sylow 2 H) {K : Subgroup H}
    (hK : IsComponent H K) (hgen : K ⊔ (S : Subgroup H) = ⊤)
    (hcover : HasSolvableNormalizedCover K
      ((S : Subgroup H) ⊓ normalizer (K : Set H))) :
    HasPrimeParabolicCover S := by
  obtain ⟨Δ, hΔ, hspan⟩ := hcover
  let Γ := (fun B : Subgroup H => B ⊔ (S : Subgroup H)) '' Δ
  refine ⟨Γ, ?_, ?_⟩
  · rintro P ⟨B, hB, rfl⟩
    exact ⟨le_sup_right, Or.inl (hK.local_adjoin_isSolvable
      (hΔ B hB).1 S.isPGroup' (hΔ B hB).2.2 (hΔ B hB).2.1)⟩
  · apply top_unique
    rw [← hgen, ← hspan]
    apply sup_le
    · apply sSup_le
      intro B hB
      have hh : B ⊔ (S : Subgroup H) ≤ sSup Γ :=
        le_sSup (Set.mem_image_of_mem _ hB)
      exact (show B ≤ sSup Γ from le_sup_left.trans hh).trans le_sup_left
    · exact S.toSubgroup.le_normalizer.trans le_sup_right

def automizerSeed (K : Subgroup H) (B : Subgroup (NormalizerAction.Star K)) :
    Subgroup H := (B.comap (NormalizerAction.componentMap K)).map K.subtype

omit [Finite H] in
theorem automizerSeed_le (K : Subgroup H) (B : Subgroup (NormalizerAction.Star K)) :
    automizerSeed K B ≤ K := map_subtype_le _

omit [Finite H] in
private theorem componentMap_conj (K : Subgroup H)
    (s : normalizer (K : Set H)) (k : K) :
    NormalizerAction.componentMap K (K.normalizerMonoidHom s k) =
      NormalizerAction.quotient K s * NormalizerAction.componentMap K k *
        (NormalizerAction.quotient K s)⁻¹ := by
  change NormalizerAction.quotient K _ = NormalizerAction.quotient K s *
    NormalizerAction.quotient K (inclusion K.le_normalizer k) *
      (NormalizerAction.quotient K s)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

omit [Finite H] in
theorem automizerSeed_normalized (S : Sylow 2 H) (K : Subgroup H)
    (B : Subgroup (NormalizerAction.Star K))
    (hB : NormalizerAction.sylowImage K S ≤ normalizer (B : Set _)) :
    (S : Subgroup H) ⊓ normalizer (K : Set H) ≤
      normalizer (automizerSeed K B : Set H) := by
  intro s hs
  have hconj (s : H) (hs : s ∈ (S : Subgroup H) ⊓ normalizer (K : Set H))
      (b : H) (hb : b ∈ automizerSeed K B) : s * b * s⁻¹ ∈ automizerSeed K B := by
    obtain ⟨k, hk, rfl⟩ := hb
    let sN : normalizer (K : Set H) := ⟨s, hs.2⟩
    have hsB := hB (mem_map_of_mem (NormalizerAction.quotient K)
      (show sN ∈ (S : Subgroup H).subgroupOf (normalizer (K : Set H)) from hs.1))
    refine ⟨K.normalizerMonoidHom sN k, ?_, rfl⟩
    change NormalizerAction.componentMap K _ ∈ B
    rw [componentMap_conj]
    exact (mem_normalizer_iff.mp hsB _).mp hk
  apply mem_normalizer_iff.mpr
  intro b
  constructor
  · exact hconj s hs b
  · intro hb
    have hh := hconj s⁻¹ (inv_mem hs) (s * b * s⁻¹) hb
    simpa only [inv_inv, ← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel_right] using hh

omit [Finite H] in
theorem automizerSeed_isSolvable (K : Subgroup H) (hz : center K = ⊥)
    (B : Subgroup (NormalizerAction.Star K)) (hB : Group.IsSolvable B) :
    Group.IsSolvable (automizerSeed K B) := by
  let := hB
  let c := NormalizerAction.componentMap K
  let f : B.comap c →* B := c.subgroupComap B
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact NormalizerAction.componentMap_injective_of_center_eq_bot K hz
      (congrArg Subtype.val hxy)
  let : Group.IsSolvable (B.comap c) :=
    Group.isSolvable_of_isSolvable_injective hf
  exact Group.isSolvable_of_surjective (K.subtype.subgroupMap_surjective (B.comap c))

omit [Finite H] in
theorem automizer_normalized_cover_lift (S : Sylow 2 H) (K : Subgroup H)
    (hz : center K = ⊥)
    (hc : HasSolvableNormalizedCover (NormalizerAction.componentImage K)
      (NormalizerAction.sylowImage K S)) :
    HasSolvableNormalizedCover K ((S : Subgroup H) ⊓ normalizer (K : Set H)) := by
  obtain ⟨Δ, hΔ, hgen⟩ := hc
  refine ⟨automizerSeed K '' Δ, ?_, ?_⟩
  · rintro B ⟨Q, hQ, rfl⟩
    exact ⟨automizerSeed_le K Q, automizerSeed_isSolvable K hz Q (hΔ Q hQ).2.1,
      automizerSeed_normalized S K Q (hΔ Q hQ).2.2⟩
  · let c := NormalizerAction.componentMap K
    have hc : Function.Injective c := NormalizerAction.componentMap_injective_of_center_eq_bot K hz
    have he : sSup ((fun B : Subgroup (NormalizerAction.Star K) => B.comap c) '' Δ) = ⊤ := by
      apply map_injective hc
      rw [show (sSup ((fun B : Subgroup (NormalizerAction.Star K) => B.comap c) '' Δ)).map c =
        sSup (map c '' (comap c '' Δ)) from
        ((gc_map_comap c).isLUB_l_image (isLUB_sSup _)).sSup_eq.symm,
        ← MonoidHom.range_eq_map, NormalizerAction.componentMap_range]
      calc
        sSup (map c '' (comap c '' Δ)) = sSup Δ := by
          congr 1
          rw [Set.image_image]
          calc
            (fun B => map c (comap c B)) '' Δ = id '' Δ := by
              apply Set.image_congr
              intro B hB
              rw [map_comap_eq, NormalizerAction.componentMap_range,
                inf_eq_right.mpr (hΔ B hB).1]
              rfl
            _ = Δ := Set.image_id _
        _ = NormalizerAction.componentImage K := hgen
    have hh := congrArg (map K.subtype) he
    rw [show (sSup ((fun B : Subgroup (NormalizerAction.Star K) => B.comap c) '' Δ)).map K.subtype =
      sSup (map K.subtype '' (comap c '' Δ)) from
      ((gc_map_comap K.subtype).isLUB_l_image (isLUB_sSup _)).sSup_eq.symm,
      ← MonoidHom.range_eq_map, K.range_subtype] at hh
    change sSup ((fun Q => map K.subtype (comap c Q)) '' Δ) = K
    simpa only [Set.image_image] using hh

theorem cover_of_automizer_seeds (S : Sylow 2 H) {K : Subgroup H}
    (hK : IsComponent H K) (hz : center K = ⊥)
    (hgen : K ⊔ (S : Subgroup H) = ⊤)
    (hc : HasSolvableNormalizedCover (NormalizerAction.componentImage K)
      (NormalizerAction.sylowImage K S)) : HasPrimeParabolicCover S :=
  cover_of_component_seeds S hK hgen (automizer_normalized_cover_lift S K hz hc)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover
