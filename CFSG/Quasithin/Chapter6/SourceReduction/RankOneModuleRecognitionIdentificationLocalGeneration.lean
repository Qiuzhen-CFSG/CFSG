module
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.Bounds
public import Theory.GroupTheory.RankOneSylowExtension
public import Theory.GroupTheory.SolvableRadical.Transport
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal
/-!
# E-generation obstructed by the original elementary Sylow lift

Let a quotient have a normal nonsolvable simple rank-one subgroup B.
Suppose an elementary subgroup of the original group maps onto a full
Sylow subgroup Q of B. Take all elementary subgroups whose images have
that order in B. In a Sylow containing the lift, all such images equal Q.
Thus their weak-closure normalizer maps into the proper normalizer of Q.
An E-member escaping that normalizer contains B in its image. Its actor
therefore retains at least the rank of Q modulo either intrinsic solvable
kernel. This contradicts rank-one E-generation when Q has rank above one.

This keeps the actual elementary lift; quotient isomorphism alone does
not suffice. Source application: Aschbacher--Smith, 6.2.11, p.686, the
E.2.2 generation contradiction for the original H-star subgroup.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction

private theorem rank_map_le_solvable_quotient
    {E D : Type*} [Group E] [Group D] [Finite E] [Finite D]
    (f : E →* D) (hf : Function.Surjective f)
    (B : Subgroup D) [IsSimpleGroup B] (hB : ¬ Group.IsSolvable B)
    (A : Subgroup E) (hAB : A.map f ≤ B)
    (N : Subgroup E) [N.Normal] [Group.IsSolvable N] :
    Group.rank (A.map f) ≤ Group.rank (A.map (QuotientGroup.mk' N)) := by
  let R := solvableRadical D
  have hNR : N ≤ R.comap f := map_le_iff_le_comap.mp
    (le_solvableRadical _ (Subgroup.Normal.map inferInstance f hf)
      (Group.isSolvable_of_surjective (f.subgroupMap_surjective N)))
  let q := QuotientGroup.map N R f hNR
  have hinj : Function.Injective ((QuotientGroup.mk' R).comp (A.map f).subtype) := by
    have hb := Subgroup.RankOneSylowExtension.simple_quotient_injective
      hB B.subtype B.subtype_injective R
    intro a b hab
    exact Subtype.ext (congrArg (fun b : B => (b : D))
      (hb (a₁ := ⟨a,hAB a.property⟩) (a₂ := ⟨b,hAB b.property⟩) hab))
  have he : Group.rank ((A.map f).map (QuotientGroup.mk' R)) = Group.rank (A.map f) := by
    have hr : ((QuotientGroup.mk' R).comp (A.map f).subtype).range =
        (A.map f).map (QuotientGroup.mk' R) := by rw [MonoidHom.range_comp,range_subtype]
    exact (Group.rank_congr ((MonoidHom.ofInjective hinj).trans
      (MulEquiv.subgroupCongr hr))).symm
  have hmap : (A.map (QuotientGroup.mk' N)).map q =
      (A.map f).map (QuotientGroup.mk' R) := by
    rw [map_map,map_map]
    rfl
  have hh := Group.rank_le_of_surjective (q.subgroupMap (A.map (QuotientGroup.mk' N)))
    (q.subgroupMap_surjective _)
  rw [hmap,he] at hh
  exact hh



/-- A lifted elementary Sylow of a normal rank-one simple image obstructs
rank-one E-generation in the original group, retaining the actual lift. -/
theorem not_generation_one_of_elementary_sylow_lift
    {E D : Type*} [Group E] [Group D] [Finite E] [Finite D]
    (f : E →* D) (hf : Function.Surjective f)
    (B : Subgroup D) [B.Normal] [IsSimpleGroup B] (hB : ¬ Group.IsSolvable B)
    (Q : Sylow 2 B) (hQrank : 1 < Group.rank Q)
    (hproper : ∀ H : Subgroup B, (Q : Subgroup B) ≤ H → H ≠ ⊤ →
      H ≤ normalizer (Q : Set B))
    (hn : normalizer (Q : Set B) ≠ ⊤)
    (A : Subgroup E) [IsElementaryAbelian 2 A]
    (hA : A.map f = (Q : Subgroup B).map B.subtype) :
    ChapterE.generationParameter E ≠ 1 := by
  let C := (Q : Subgroup B).map B.subtype
  obtain ⟨T,hAT⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  let S := T.mapSurjective hf
  have hCS : C ≤ S := by change (Q : Subgroup B).map B.subtype ≤ S; rw [← hA]; exact map_mono hAT
  have hCB : C ≤ B := map_subtype_le _
  have hCeq : C = (S : Subgroup D) ⊓ B := by
    have hh := Q.is_maximal' S.isPGroup'.comap_subtype (map_le_iff_le_comap.mp hCS)
    have hm := congrArg (Subgroup.map B.subtype) hh
    change ((S : Subgroup D).subgroupOf B).map B.subtype = C at hm
    rw [subgroupOf_map_subtype,inf_comm] at hm
    exact hm.symm.trans (inf_comm _ _)
  let Ω : Set (Subgroup E) := {J | IsElementaryAbelian 2 J ∧
    J.map f ≤ B ∧ Nat.card (J.map f) = Nat.card C}
  have hΩ : ChapterE.IsElementaryFamily Ω := by
    refine ⟨fun J hJ => hJ.1,?_⟩
    intro g J hJ
    let := hJ.1
    have he : (J.map (MulAut.conj g).toMonoidHom).map f =
        (J.map f).map (MulAut.conj (f g)).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      ext x
      simp
    refine ⟨IsElementaryAbelian.map _,?_,?_⟩
    · rw [he]
      rintro _ ⟨x,hx,rfl⟩
      exact (inferInstance : B.Normal).conj_mem x (hJ.2.1 hx) (f g)
    · rw [he,card_map_of_injective (MulAut.conj (f g)).injective]
      exact hJ.2.2
  have hAΩ : A ∈ Ω := ⟨inferInstance,hA ▸ hCB,by rw [hA]⟩
  have huniq : ∀ J ∈ Ω, J ≤ (T : Subgroup E) → J.map f = C := by
    intro J hJ hJT
    apply eq_of_le_of_card_ge
    · rw [hCeq]
      exact le_inf (map_mono hJT) hJ.2.1
    · exact hJ.2.2.ge
  let W := ChapterE.weakClosure (T : Subgroup E) Ω
  have hW : W.map f = C := by
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply sSup_le
      intro J hJ
      exact map_le_iff_le_comap.mp (huniq J hJ.1 hJ.2).le
    · change (Q : Subgroup B).map B.subtype ≤ W.map f
      rw [← hA]
      exact map_mono (le_sSup ⟨hAΩ,hAT⟩)
  let N := (normalizer (C : Set D)).comap f
  have hN : N ≠ ⊤ := by
    intro he
    have hNtop : normalizer (C : Set D) = ⊤ := by
      have hh := congrArg (Subgroup.map f) he
      change ((normalizer (C : Set D)).comap f).map f = (⊤ : Subgroup E).map f at hh
      rwa [map_comap_eq_self_of_surjective hf,map_top_of_surjective f hf] at hh
    have hh := congrArg (Subgroup.comap B.subtype) hNtop
    rw [comap_normalizer_eq_of_le_range (by simpa using hCB),
      comap_map_eq_self_of_injective B.subtype_injective,comap_top] at hh
    exact hn hh
  have hWN : normalizer (W : Set E) ≤ N := by
    apply map_le_iff_le_comap.mp
    rw [← hW]
    exact W.le_normalizer_map f
  intro hgen
  obtain ⟨J,hJ,hJT,K,hK,hKN⟩ :=
    ChapterE.exists_rankOne_member_of_parameter_eq_one hgen T Ω hΩ N hN hWN
  have hJmap := huniq J hJ hJT
  have hCJ : C ≤ K.map f := hJmap ▸ map_mono hK.1.2.2.1
  rcases Subgroup.RankOneSylowExtension.le_or_le_normalizer B Q hproper
    (K.map f) hCJ with hBK | hKN'
  · let D' := K.map f
    let B' := B.subgroupOf D'
    let eB : B' ≃* B := subgroupOfEquivOfLe hBK
    let : IsSimpleGroup B' := eB.isSimpleGroup
    have hBs : ¬ Group.IsSolvable B' := fun hs =>
      hB (by let := hs; exact Group.isSolvable_of_surjective (f := eB.toMonoidHom) eB.surjective)
    let k : K →* D' := f.subgroupMap K
    have hk : Function.Surjective k := f.subgroupMap_surjective K
    let J' := J.subgroupOf K
    have hJimage : (J'.map k).map D'.subtype = C := by
      rw [map_map]
      change J'.map (f.comp K.subtype) = C
      rw [← map_map,map_subgroupOf_eq_of_le hK.1.2.2.1]
      exact hJmap
    have hJB : J'.map k ≤ B' := map_le_iff_le_comap.mp (hJimage ▸ hCB)
    have hrank : 1 < Group.rank (J'.map k) := by
      have he := Group.rank_congr ((J'.map k).equivMapOfInjective D'.subtype D'.subtype_injective)
      have heQ := Group.rank_congr ((Q : Subgroup B).equivMapOfInjective B.subtype B.subtype_injective)
      rw [hJimage] at he
      exact he.symm ▸ (heQ ▸ hQrank)
    rcases hK.2 with hodd | hcomp
    · let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
      exact (Nat.not_le_of_gt hrank)
        ((rank_map_le_solvable_quotient k hk B' hBs J' hJB (pCore 2 K)).trans hodd.2)
    · exact (Nat.not_le_of_gt hrank)
        ((rank_map_le_solvable_quotient k hk B' hBs J' hJB (solvableRadical K)).trans hcomp.2)
  · exact hKN (map_le_iff_le_comap.mp hKN')

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
