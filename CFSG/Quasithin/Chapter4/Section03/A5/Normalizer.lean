module
public import CFSG.Quasithin.Chapter4.Section03.A5.NormalizerStep
public import Theory.GroupTheory.NormalFourCentralizerSeparation
/-!
# Original 4.3.1 and the 4.3.3 Sylow promotion in the A₅ branch

Induct up the finite lattice of local Sylow subgroups. A larger Sylow
subgroup in the local normalizer inherits uniqueness, and the induction
hypothesis controls the previous normalizer. If it cannot enlarge, its
odd local index and the original ambient Sylow make it Sylow globally.
In both cases the normalizer-index criterion constructs the same Sylow
subgroup in the full normalizer, allowing the preceding C.5.6 argument.

The final source consumer applies this to the strict-extension uniqueness
of 4.3.3(a). It promotes the original S, already Sylow in H∩M, to Sylow in
H. That earlier maximality assertion remains explicit here; no uniqueness
over L or full Sylow conclusion is inserted as an assumption.

Source: Aschbacher–Smith 4.3.1 and 4.3.3(a)–(b), printed pp.613–614.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem normalizer_le_of_local_sylow
    (hblock : ChapterC.IsAlternatingBlock L 5)
    (U : Subgroup G) : ∀ (R : Subgroup G), IsPGroup 2 R →
      R ≤ normalizer (L : Set G) →
      (∃ Q : Sylow 2 L, (Q : Subgroup L).map L.subtype ≤ R) →
      IsPGroup 2 U → U ≤ normalizer (L : Set G) ⊓ normalizer (R : Set G) →
      ¬ 2 ∣ U.relIndex (normalizer (L : Set G) ⊓ normalizer (R : Set G)) →
      Chapter4.UniqueMaximalOvergroup (L ⊔ U) (normalizer (L : Set G)) →
      normalizer (R : Set G) ≤ normalizer (L : Set G) := by
  classical
  induction U using WellFoundedGT.induction with
  | ind U ih =>
    intro R hR hRM hQR hU hUM hUi hu
    let M := normalizer (L : Set G)
    let N := M ⊓ normalizer (R : Set G)
    have hRN : R ≤ N := le_inf hRM R.le_normalizer
    let PU := (hU.comap_subtype (K := N)).toSylow hUi
    have hPU : (PU : Subgroup N).map N.subtype = U := map_subgroupOf_eq_of_le hUM
    have hRU : R ≤ U := by
      let : (R.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hRN).mpr inf_le_right
      have hp : IsPGroup 2 (R.subgroupOf N) := hR.comap_subtype
      have hh := map_mono (f := N.subtype) (hp.le_sylow_of_normal PU)
      rwa [map_subgroupOf_eq_of_le hRN,hPU] at hh
    obtain ⟨Q,hQ⟩ := hQR
    have finish (hindex : ¬ 2 ∣ U.relIndex (normalizer (R : Set G))) :
        normalizer (R : Set G) ≤ M := by
      let P := (hU.comap_subtype (K := normalizer (R : Set G))).toSylow hindex
      have hP : (P : Subgroup (normalizer (R : Set G))).map
          (normalizer (R : Set G)).subtype = U := map_subgroupOf_eq_of_le (hUM.trans inf_le_right)
      apply d.normalizer_le_of_source_sylow hblock R hR hRM Q hQ P
      · rw [hP]; exact hUM.trans inf_le_left
      · simpa only [hP] using hu
    let D := M ⊓ normalizer (U : Set G)
    let P : Sylow 2 D := Classical.choice inferInstance
    let W := (P : Subgroup D).map D.subtype
    have hUW : U ≤ W := by
      have hUD : U ≤ D := le_inf (hUM.trans inf_le_left) U.le_normalizer
      let : (U.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hUD).mpr inf_le_right
      have hp : IsPGroup 2 (U.subgroupOf D) := hU.comap_subtype
      have hh := map_mono (f := D.subtype) (hp.le_sylow_of_normal P)
      rwa [map_subgroupOf_eq_of_le hUD] at hh
    have hW : IsPGroup 2 W := P.isPGroup'.map D.subtype
    have hWD : W ≤ D := map_subtype_le _
    have hWi : ¬ 2 ∣ W.relIndex D := by
      have he := relIndex_map_map_of_injective (P : Subgroup D) ⊤ D.subtype_injective
      simp only [← MonoidHom.range_eq_map,D.range_subtype,relIndex_top_right] at he
      rw [he]
      exact P.not_dvd_index
    by_cases he : U = W
    · have hUN : ¬ 2 ∣ U.relIndex D := he ▸ hWi
      have hUMi : ¬ 2 ∣ U.relIndex M :=
        not_dvd_relIndex_of_normalizer_inf_le U D M hU (hUM.trans inf_le_left) hUN
          (by rw [inf_comm])
      have hMi : ¬ 2 ∣ M.index := fun hd => T.not_dvd_index
        (hd.trans (index_dvd_of_le d.normalizes_L))
      have hUiG : ¬ 2 ∣ U.index := by
        rw [← relIndex_mul_index (hUM.trans inf_le_left)]
        exact fun hd => (Nat.prime_two.dvd_mul.mp hd).elim hUMi hMi
      exact finish (fun hd => hUiG (hd.trans
        (relIndex_dvd_index_of_le (hUM.trans inf_le_right))))
    · have hult : U < W := lt_of_le_of_ne hUW he
      have huniq : Chapter4.UniqueMaximalOvergroup (L ⊔ W) M := by
        refine ⟨hu.1,sup_le L.le_normalizer (hWD.trans inf_le_left),?_⟩
        intro J hJ hWJ
        exact hu.2.2 J hJ ((sup_le_sup_left hUW L).trans hWJ)
      have hNU := ih W hult U hU (hUM.trans inf_le_left) ⟨Q,hQ.trans hRU⟩ hW hWD hWi huniq
      exact finish (not_dvd_relIndex_of_normalizer_inf_le U N
        (normalizer (R : Set G)) hU (hUM.trans inf_le_right) hUi
          (inf_le_inf hNU le_rfl))

/-- Original 4.3.1 for the literal A5 block and a Sylow subgroup of N_M(R). -/
theorem normalizer_le_of_uniqueness_over_local_sylow
    (hblock : ChapterC.IsAlternatingBlock L 5)
    (R : Subgroup G) (hR : IsPGroup 2 R) (hRM : R ≤ normalizer (L : Set G))
    (Q : Sylow 2 L) (hQ : (Q : Subgroup L).map L.subtype ≤ R)
    (P : Sylow 2 (normalizer (L : Set G) ⊓ normalizer (R : Set G) : Subgroup G))
    (hu : Chapter4.UniqueMaximalOvergroup
      (L ⊔ (P : Subgroup (normalizer (L : Set G) ⊓ normalizer (R : Set G) : Subgroup G)).map
        (normalizer (L : Set G) ⊓ normalizer (R : Set G)).subtype)
      (normalizer (L : Set G))) :
    normalizer (R : Set G) ≤ normalizer (L : Set G) := by
  apply d.normalizer_le_of_local_sylow hblock _ R hR hRM ⟨Q,hQ⟩
    (P.isPGroup'.map _) (map_subtype_le _) _ hu
  have he := relIndex_map_map_of_injective (P : Subgroup _) ⊤
    (normalizer (L : Set G) ⊓ normalizer (R : Set G)).subtype_injective
  simp only [← MonoidHom.range_eq_map,range_subtype,relIndex_top_right] at he
  rw [he]
  exact P.not_dvd_index
/-- Source 4.3.3(b): strict Sylow extensions force the actual intersection to be Sylow in H. -/
theorem source_sylow_promotion
    (hblock : ChapterC.IsAlternatingBlock L 5)
    (H S : Subgroup G) (hST : S < (T : Subgroup G))
    (Q : Sylow 2 L) (hQS : (Q : Subgroup L).map L.subtype ≤ S)
    (hSH : S ≤ H) (hindex : ¬ 2 ∣ S.relIndex (H ⊓ normalizer (L : Set G)))
    (hunique : ∀ X : Subgroup G, S < X → X ≤ (T : Subgroup G) →
      Chapter4.UniqueMaximalOvergroup (L ⊔ X) (normalizer (L : Set G))) :
    normalizer (S : Set G) ≤ normalizer (L : Set G) ∧
      ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = S := by
  let U := (normalizer (S.subgroupOf (T : Subgroup G) : Set (T : Subgroup G))).map
    (T : Subgroup G).subtype
  have hUT : U ≤ (T : Subgroup G) := map_subtype_le _
  have hUS : U ≤ normalizer (S : Set G) := by
    have hn := (S.subgroupOf (T : Subgroup G)).le_normalizer_map (T : Subgroup G).subtype
    rwa [map_subgroupOf_eq_of_le hST.le] at hn
  have hSU : S < U := by
    let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
    have hp : S.subgroupOf (T : Subgroup G) < ⊤ := by
      apply lt_top_iff_ne_top.mpr
      intro he
      have hh := congrArg (map (T : Subgroup G).subtype) he
      rw [map_subgroupOf_eq_of_le hST.le,← MonoidHom.range_eq_map,range_subtype] at hh
      exact hST.ne hh
    have hn := Group.normalizerCondition_of_isNilpotent _ hp
    have hl : S ≤ U := by
      rw [← map_subgroupOf_eq_of_le hST.le]
      exact map_mono hn.le
    apply lt_of_le_of_ne hl
    intro he
    have hm : S.subgroupOf (T : Subgroup G) =
        normalizer (S.subgroupOf (T : Subgroup G) : Set (T : Subgroup G)) :=
      (map_injective (T : Subgroup G).subtype_injective) (by
        rw [map_subgroupOf_eq_of_le hST.le]; exact he)
    exact hn.ne hm
  let N := normalizer (L : Set G) ⊓ normalizer (S : Set G)
  have hUN : U ≤ N := le_inf (hUT.trans d.normalizes_L) hUS
  obtain ⟨P,hUP⟩ := ((T.isPGroup'.to_le hUT).comap_subtype (K := N)).exists_le_sylow
  have hUP' : U ≤ (P : Subgroup N).map N.subtype := by
    intro x hx
    exact mem_map_of_mem N.subtype (hUP (show (⟨x,hUN hx⟩ : N) ∈ U.subgroupOf N from hx))
  have hu : Chapter4.UniqueMaximalOvergroup (L ⊔ (P : Subgroup N).map N.subtype)
      (normalizer (L : Set G)) := by
    obtain ⟨hm,_,hu⟩ := hunique U hSU hUT
    refine ⟨hm,sup_le L.le_normalizer ((map_subtype_le _).trans inf_le_left),?_⟩
    intro J hJ hPJ
    exact hu J hJ ((sup_le_sup_left hUP' L).trans hPJ)
  have hn := d.normalizer_le_of_uniqueness_over_local_sylow hblock S
    (T.isPGroup'.to_le hST.le) (hST.le.trans d.normalizes_L) Q hQS P hu
  refine ⟨hn,?_⟩
  have hi : ¬ 2 ∣ S.relIndex H := not_dvd_relIndex_of_normalizer_inf_le S
    (H ⊓ normalizer (L : Set G)) H (T.isPGroup'.to_le hST.le) hSH hindex
      (by rw [inf_comm]; exact inf_le_inf_left H hn)
  exact ⟨((T.isPGroup'.to_le hST.le).comap_subtype (K := H)).toSylow hi,
    map_subgroupOf_eq_of_le hSH⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
