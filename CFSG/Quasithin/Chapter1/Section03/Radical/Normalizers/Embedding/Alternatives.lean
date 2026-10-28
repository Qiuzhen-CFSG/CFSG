module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Setup

/-!
# The surviving A.3.12 embedding for the characteristic normalizer

Let X = Ξ_p(L), R = O₂(XT), Y = N_L(R)^∞, and N = N_G(C), where
C is nontrivial and characteristic in R. For the actual containing
C-component K, the previously established strictness Y < K and the
obstruction X ≰ O∞(K) force the A.3.12 embedding to be case (10).

The proof transports strictness and nonquasisimplicity through the actual
two-core quotient, transports the marked X with its relative normality,
solvability and two-perfectness, and applies the complete elimination.
The odd-core structure of the image of K is obtained by applying the
universal source A.3.6 statement to N/O₂(N). The source residual outputs
and that universal earlier theorem remain explicit inputs for the parent
embedding assembly; no branch-exclusion input is needed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.6, printed p.43; A.3.12, printed pp.47–48; proof of 1.3.8, p.513.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.Chapter1.RadicalNormalizers
open CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding
open CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Selection of case (10) for the actual characteristic-normalizer quotient. -/
theorem exists_case_ten
    {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA36 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ K : Subgroup A,
      K.IsCComponent → A36Conclusion K)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (L : Subgroup G) (T : Sylow 2 G)
    (C : Subgroup (radicalCore p L T)) [C.Characteristic] (hC : C ≠ ⊥)
    (K : Subgroup G)
    (hK : K ∈ cComponentsIn (normalizer (C.map (radicalCore p L T).subtype : Set G)))
    (hYK : normalizerResidual L (radicalCore p L T) < K)
    (hY : normalizerResidual L (radicalCore p L T) ∈ Chapter1.L G T)
    (hXY : XiP p L ≤ normalizerResidual L (radicalCore p L T))
    (hYq : ¬ IsQuasisimple (XiQuotient (normalizerResidual L (radicalCore p L T))))
    (hXrad : ¬ XiP p L ≤ (solvableRadical K).map K.subtype)
    (hemb :
      let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
      A312Embedding
        ((normalizerResidual L (radicalCore p L T)).subgroupOf N |>.map
          (QuotientGroup.mk' (pCore 2 N)))
        ((K.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)))) :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    let B := (normalizerResidual L (radicalCore p L T)).subgroupOf N |>.map
      (QuotientGroup.mk' (pCore 2 N))
    let Kbar := (K.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
    ∃ s : ℕ, s.Prime ∧ Odd s ∧ 3 < s ∧
      HasExtension B (ElementaryModel s 2) (fun U _ => IsSL U 2 s) ∧
      (ClassicalGroup.IsPSL Kbar 3 s ∨ IsSL Kbar 3 s) := by
  let R := radicalCore p L T
  let N := normalizer (C.map R.subtype : Set G)
  let Y := normalizerResidual L R
  let X := XiP p L
  let q := QuotientGroup.mk' (pCore 2 N)
  let B := (Y.subgroupOf N).map q
  let Kbar := (K.subgroupOf N).map q
  let Xbar := (X.subgroupOf N).map q
  have hTN : (T : Subgroup G) ≤ N :=
    (t_le_normalizer_radicalCore p L T).trans
      (normalizer_le_normalizer_characteristic_image R C)
  have hYN : Y ≤ N := hYK.le.trans hK.1
  have hXN : X ≤ N := hXY.trans hYN
  have hYP : Group.IsPerfect (Y.subgroupOf N) := by
    let := mem_L_isPerfect hY
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hYN).symm.toMonoidHom)
      (subgroupOfEquivOfLe hYN).symm.surjective
  let := hYP
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := q.subgroupMap (Y.subgroupOf N)) (q.subgroupMap_surjective _)
  have hXYN : Y.subgroupOf N ≤ normalizer (X.subgroupOf N : Set N) := by
    rw [← subgroupOf_normalizer_eq hXN]
    exact comap_mono ((normalizerResidual_le L R).trans
      (L.le_normalizer.trans (normalizer_le_normalizer_XiP p L)))
  have hXnormal : (Xbar.subgroupOf B).Normal := normal_subgroupOf_of_le_normalizer
    ((map_mono (f := q) hXYN).trans ((X.subgroupOf N).le_normalizer_map q))
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsSolvable X := XiP_solvable p ho L
  let : Group.IsSolvable (X.subgroupOf N) := Group.isSolvable_of_surjective
    (f := (subgroupOfEquivOfLe hXN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXN).symm.surjective
  let : Group.IsSolvable Xbar := Group.isSolvable_of_surjective
    (f := q.subgroupMap (X.subgroupOf N)) (q.subgroupMap_surjective _)
  have hXp : IsPPerfect 2 Xbar :=
    ((XiP_isPPerfect p L).of_surjective
      (subgroupOfEquivOfLe hXN).symm.toMonoidHom
      (subgroupOfEquivOfLe hXN).symm.surjective).of_surjective
        (q.subgroupMap (X.subgroupOf N)) (q.subgroupMap_surjective _)
  have hcommon : A36Common Kbar :=
    (proposition_1_2_1_four_earlier_conclusion hA36
      (characteristic_normalizer_quotient_sqtk hG p L T C hC) hK.2).2
  obtain ⟨hstrict, hnonq⟩ := actual_image_strict_and_not_quasisimple
    T hTN hY hK.1 hK.2 hYK hYq
  exact case_ten_of_embedding (X := Xbar) (B := B) (K := Kbar) hstrict (map_mono (comap_mono hXY)) hXnormal hXp
    (actual_image_not_le_radical (hXY.trans hYK.le) hK.1 hXrad) hnonq hcommon hemb
end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
