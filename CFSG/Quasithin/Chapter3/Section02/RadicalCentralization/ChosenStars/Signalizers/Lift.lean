module
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ChosenStars.Signalizers.Extension
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Parabolic
/-!
# The actual residual supplement lies in the join's two-core

Transport the defining plane through K/O₂(K) to its literal image in
KR/O₂(KR). Normality of K and the two-group supplement give the required
normal extension. The complete model signalizer theorem kills the image
of R, yielding R ≤ O₂(KR), without assuming K normalizes R.
The reverse inclusion for canonical radicals is proved in Normalizers.Basic.

Source: Aschbacher--Smith, proof of 1.3.8, printed p.513.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars
open Chapter1 Chapter1.RadicalNormalizers Chapter1.RadicalNormalizers.Embedding Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A defining plane kills the actual two-group supplement modulo its core. -/
theorem radical_le_join_core_of_linearThree
    (hp : 3 < p) (K R N P : Subgroup G) (hK : K ∈ cComponentsIn N)
    (hKn : (K.subgroupOf N).Normal) (hRN : R ≤ N)
    (hR : IsPGroup 2 R) (hPK : P ≤ K) (hP : IsPGroup p P)
    (hcard : Nat.card P = p ^ 2) (hPR : P ≤ normalizer (R : Set G))
    (hm : LinearThreeModel p (XiQuotient K)) :
    R ≤ (K ⊔ R).pCoreIn 2 := by
  let H := K ⊔ R
  let q := QuotientGroup.mk' (pCore 2 H)
  let Kbar := (K.subgroupOf H).map q
  let Rbar := (R.subgroupOf H).map q
  have hHN : H ≤ N := sup_le hK.1 hRN
  have hcomp : (K.subgroupOf H).IsCComponent :=
    hK.2.subgroupOf_of_le le_sup_left hHN
  have hHK : H ≤ normalizer (K : Set G) :=
    hHN.trans ((normal_subgroupOf_iff_le_normalizer hK.1).mp hKn)
  let : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHK
  let : Kbar.Normal := (inferInstance : (K.subgroupOf H).Normal).map q
    (QuotientGroup.mk'_surjective _)
  let e := componentQuotientEquiv (show K ≤ H from le_sup_left) hcomp
  let Q := (((P.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)))).map e.toMonoidHom
  have hQmap : Q.map Kbar.subtype = ((P.subgroupOf H).map q) :=
    componentQuotientEquiv_map_subgroup hPK le_sup_left hcomp
  have hRbar : IsPGroup 2 Rbar := hR.comap_subtype.map q
  have hsup : Rbar ⊔ Kbar = ⊤ := by
    rw [← Subgroup.map_sup]
    have hs : R.subgroupOf H ⊔ K.subgroupOf H = ⊤ := by
      apply map_injective H.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show R ≤ H from le_sup_right),
        map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
        ← MonoidHom.range_eq_map, range_subtype]
      exact sup_comm R K
    rw [hs, map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hquot : IsPGroup 2 (XiQuotient H ⧸ Kbar) :=
    quotient_isPGroup_of_sup_eq_top Rbar Kbar hRbar hsup
  have hnorm : Q.map Kbar.subtype ≤ normalizer (Rbar : Set (XiQuotient H)) := by
    rw [hQmap]
    apply le_trans (map_mono (show P.subgroupOf H ≤
      normalizer (R.subgroupOf H : Set H) from ?_))
      ((R.subgroupOf H).le_normalizer_map q)
    rw [← subgroupOf_normalizer_eq (show R ≤ H from le_sup_right)]
    exact comap_mono hPR
  have hQ : IsPGroup p Q := (hP.comap_subtype.map _).map _
  let eQ : P ≃* Q := (oddImageEquiv
    ((Fact.out : p.Prime).odd_of_ne_two (by omega)) hPK hP).trans
      (e.subgroupMap ((P.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))))
  have hQcard : Nat.card Q = p ^ 2 := (Nat.card_congr eQ.toEquiv.symm).trans hcard
  have hm' : LinearThreeModel p Kbar := by
    rcases hm with ⟨F,_,_,hF,⟨f⟩⟩ | ⟨F,_,_,hF,⟨f⟩⟩
    · exact Or.inl ⟨F,inferInstance,inferInstance,hF,⟨e.symm.trans f⟩⟩
    · exact Or.inr ⟨F,inferInstance,inferInstance,hF,⟨e.symm.trans f⟩⟩
  have hbot : Rbar = ⊥ := Signalizers.extension_two_eq_bot hp Kbar hm' hquot
    (pCore_quotient_pCore_eq_bot 2) Q hQ hQcard Rbar hRbar hnorm
  have hle : R.subgroupOf H ≤ pCore 2 H := by
    have hh := (Subgroup.map_eq_bot_iff (R.subgroupOf H)).mp hbot
    simpa only [q, QuotientGroup.ker_mk'] using hh
  have hh := map_mono (f := H.subtype) hle
  change R ≤ (pCore 2 H).map H.subtype
  simpa only [map_subgroupOf_eq_of_le (show R ≤ H from le_sup_right)] using hh

end CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars
