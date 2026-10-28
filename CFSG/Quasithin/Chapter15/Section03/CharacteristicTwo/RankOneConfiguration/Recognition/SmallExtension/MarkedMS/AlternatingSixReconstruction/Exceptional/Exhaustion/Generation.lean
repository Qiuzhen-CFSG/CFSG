module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Kernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Source
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.PResidual.NormalizedGenerators
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.FiniteParabolicTransfer

/-!
# Lifting the source rank-one generators through the cubic kernel

Surjections preserve the ordered residual O²(O^{2′}(P)). The two lifted
residuals and a common Sylow therefore generate modulo E. Source (A)'s
no-supplement clause lifts this to generation in M, retaining the odd part
of E. The normalized-generators criterion then identifies their join with
the original relative component K = O²(M).

The Sylow lift contains the original radical; it does not identify that
radical with a Sylow. Source: Meierfrankenfeld--Stellmacher (1993),
hypotheses (A), (B), (P) and the definition of L, pp.828--829.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion

variable {A B : Type*} [Group A] [Finite A] [Group B]

private theorem rankOne_eq_residual (P : Subgroup A) :
    rankOne P = (pResidual 2 ((primeToResidual 2 P).map P.subtype)).map
      ((primeToResidual 2 P).map P.subtype).subtype := by
  exact map_embedded_pResidual 2 (primeToResidual 2 P) P.subtype

private theorem rankOne_map [Finite B] (P : Subgroup A) (f : A →* B) :
    (rankOne P).map f = rankOne (P.map f) := by
  rw [rankOne_eq_residual, map_embedded_pResidual,
    map_embedded_primeToResidual_of_hom, ← rankOne_eq_residual]

private theorem rankOne_perfect (P : Subgroup A) : IsPPerfect 2 (rankOne P) := by
  rw [rankOne_eq_residual]
  exact isPPerfect_embedded_pResidual 2 _

omit [Finite A] in
private theorem rankOne_normalized (P : Subgroup A) :
    P ≤ normalizer (rankOne P : Set A) := by
  let D := (pResidual 2 (primeToResidual 2 P)).map (primeToResidual 2 P).subtype
  have : D.Characteristic := inferInstance
  exact P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P D)

omit [Finite A] in
private theorem rankOne_of_primeToResidual (P : Subgroup A)
    (hP : primeToResidual 2 P = ⊤) :
    rankOne P = (pResidual 2 P).map P.subtype := by
  rw [rankOne, hP]
  congr 1
  exact map_pResidual 2 (topEquiv : (⊤ : Subgroup P) ≃* _)

private theorem residual_sup_sylow (P : Subgroup A) (S : Sylow 2 A)
    (hSP : (S : Subgroup A) ≤ P) :
    (pResidual 2 P).map P.subtype ⊔ (S : Subgroup A) = P := by
  have h := congrArg (fun K : Subgroup P => K.map P.subtype)
    (pResidual_sup_sylow_eq_top (S.subtype hSP))
  rwa [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hSP,
    ← MonoidHom.range_eq_map, P.range_subtype] at h

/-- The lifted source generators recover the full component. The odd part
of E is removed by source (A), rather than silently treated as a two-group. -/
theorem rankOne_generation_of_extension
    {G : Type*} [Group G] [Finite G] {κ : GroupClass} {L R : Subgroup G}
    (h : SmallMSPair κ L R)
    (P₀ P₁ : Subgroup ((L ⊔ R : Subgroup G) ⧸ extensionKernel h))
    (S : Sylow 2 (L ⊔ R : Subgroup G))
    (hS₀ : (S : Subgroup (L ⊔ R : Subgroup G)) ≤
      P₀.comap (QuotientGroup.mk' (extensionKernel h)))
    (hS₁ : (S : Subgroup (L ⊔ R : Subgroup G)) ≤
      P₁.comap (QuotientGroup.mk' (extensionKernel h)))
    (hgen : P₀ ⊔ P₁ = ⊤)
    (h₀ : primeToResidual 2 P₀ = ⊤) (h₁ : primeToResidual 2 P₁ = ⊤) :
    rankOne (P₀.comap (QuotientGroup.mk' (extensionKernel h))) ⊔
      rankOne (P₁.comap (QuotientGroup.mk' (extensionKernel h))) =
        L.subgroupOf (L ⊔ R) := by
  let M := (L ⊔ R : Subgroup G)
  let π := QuotientGroup.mk' (extensionKernel h)
  let A₀ := P₀.comap π
  let A₁ := P₁.comap π
  let F := rankOne A₀ ⊔ rankOne A₁
  let T := (S : Subgroup M)
  have hπ := QuotientGroup.mk'_surjective (extensionKernel h)
  have hmap (P : Subgroup (M ⧸ extensionKernel h)) :
      (P.comap π).map π = P := map_comap_eq_self_of_surjective hπ P
  have hSi (P : Subgroup (M ⧸ extensionKernel h))
      (hSP : T ≤ P.comap π) (hP : primeToResidual 2 P = ⊤) :
      ((rankOne (P.comap π)) ⊔ T).map π = P := by
    rw [Subgroup.map_sup, rankOne_map, hmap, rankOne_of_primeToResidual P hP]
    exact residual_sup_sylow P (S.mapSurjective hπ) (map_le_iff_le_comap.mpr hSP)
  have hFmap : (F ⊔ T).map π = ⊤ := by
    calc
      _ = ((rankOne A₀ ⊔ T).map π) ⊔ ((rankOne A₁ ⊔ T).map π) := by
        rw [← Subgroup.map_sup, sup_sup_sup_comm, sup_idem]
      _ = P₀ ⊔ P₁ := by rw [hSi P₀ hS₀ h₀, hSi P₁ hS₁ h₁]
      _ = ⊤ := hgen
  have hFE : (F ⊔ T) ⊔ extensionKernel h = ⊤ := by
    have he := congrArg (fun H : Subgroup (M ⧸ extensionKernel h) => H.comap π) hFmap
    simpa only [comap_map_eq, π, QuotientGroup.ker_mk', comap_top] using he
  have hE : extensionKernel h ≤ F ⊔ T := by
    have hs := extensionKernel_no_supplement h (F ⊔ T) (by rw [hFE]; exact le_top)
    rw [extensionKernel_twoCore h] at hs
    exact hs.trans (sup_le le_rfl ((pCore_isPGroup.le_sylow_of_normal S).trans le_sup_right))
  have hFT : F ⊔ T = ⊤ := by simpa only [sup_of_le_left hE] using hFE
  rw [← h.relative_residual]
  exact (pResidual_eq_sup_of_normalized_generators _ _ T
    (rankOne_perfect A₀) (rankOne_perfect A₁) S.isPGroup'
    (hS₀.trans (rankOne_normalized A₀)) (hS₁.trans (rankOne_normalized A₁)) hFT).symm

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion

/-- A two-subgroup whose image lies in a quotient Sylow is contained in an
ambient Sylow above that same quotient Sylow, even when the kernel is odd. -/
theorem exists_sylow_over_quotient
    {M H : Type*} [Group M] [Finite M] [Group H] [Finite H]
    (π : M →* H) (hπ : Function.Surjective π) (B : Sylow 2 H)
    (T : Subgroup M) (hT : IsPGroup 2 T) (hTB : T.map π ≤ (B : Subgroup H)) :
    ∃ S : Sylow 2 M, T ≤ (S : Subgroup M) ∧
      (S : Subgroup M) ≤ (B : Subgroup H).comap π := by
  let C := (B : Subgroup H).comap π
  have hTC : T ≤ C := map_le_iff_le_comap.mp hTB
  obtain ⟨S₀, hS₀⟩ := (show IsPGroup 2 (T.subgroupOf C) from hT.comap_subtype).exists_le_sylow
  have hi : ¬ 2 ∣ ((S₀ : Subgroup C).map C.subtype).index := by
    rw [index_map_subtype]
    apply Nat.Prime.not_dvd_mul (by decide : Nat.Prime 2)
    · exact S₀.not_dvd_index
    · change ¬ 2 ∣ ((B : Subgroup H).comap π).index
      rw [index_comap_of_surjective _ hπ]
      exact B.not_dvd_index
  let S := (S₀.isPGroup'.map C.subtype).toSylow hi
  refine ⟨S, ?_, map_subtype_le _⟩
  change T ≤ (S₀ : Subgroup C).map C.subtype
  rw [← map_subgroupOf_eq_of_le hTC]
  exact map_mono hS₀

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
