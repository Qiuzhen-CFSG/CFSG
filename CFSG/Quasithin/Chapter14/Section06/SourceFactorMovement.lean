module
public import CFSG.Quasithin.Chapter14.Section06.SourceRatioDecomposition
public import Theory.GroupTheory.PResidual.NormalizerCore
/-!
# The central line in each lifted odd factor

A nonzero subgroup B of the primitive odd residual lifts through O₂(J).
The two-residual of that preimage is nontrivial, lies in O₂,F*(J), and is
normalized by O₂(J). Thus original 14.6.2 puts the actual Sylow central line
inside its commutator on the original elementary span.

Source: Aschbacher--Smith 14.6.12(3), printed p.1031, using 14.6.2.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hu hmany hcard e hab


theorem source_point_le_lifted_odd_factor
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    (B : Subgroup (J ⧸ pCore 2 J)) (hB : B ≤ pResidual 2 (J ⧸ pCore 2 J))
    (hne : B ≠ ⊥) :
    let A := B.comap (QuotientGroup.mk' (pCore 2 J))
    centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) J,
      ((pResidual 2 A).map A.subtype).map J.subtype⁆ := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let A := B.comap q
  let X₀ := (pResidual 2 A).map A.subtype
  let X := X₀.map J.subtype
  obtain ⟨p,hp,hE,_hb,_hne,_hm⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  let : IsElementaryAbelian p (pResidual 2 (J ⧸ pCore 2 J)) := hE
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  have hBp : IsPGroup p B := (IsElementaryAbelian.isPGroup p _).to_le hB
  have hXne : X ≠ ⊥ := by
    intro hz
    have hz₀ : X₀ = ⊥ := (map_eq_bot_iff_of_injective _ J.subtype_injective).mp hz
    have hr : pResidual 2 A = ⊥ := (map_eq_bot_iff_of_injective _ A.subtype_injective).mp hz₀
    have hA2 : IsPGroup 2 A := (isPGroup_quotient_pResidual (G := A) 2).of_injective
      (QuotientGroup.mk' (pResidual 2 A)) (by
        apply (MonoidHom.ker_eq_bot_iff _).mp
        rw [QuotientGroup.ker_mk',hr])
    have hB2 : IsPGroup 2 B := by
      have hh := hA2.map q
      change IsPGroup 2 ((B.comap q).map q) at hh
      rwa [map_comap_eq,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),top_inf_eq] at hh
    have hd := IsPGroup.disjoint_of_ne p 2
      (by rcases hp with rfl | rfl <;> decide) B B hBp hB2
    exact hne ((disjoint_self.mp hd))
  have hPf : pResidual 2 (J ⧸ pCore 2 J) ≤ generalizedFitting (J ⧸ pCore 2 J) :=
    (show pResidual 2 (J ⧸ pCore 2 J) ≤ fittingSubgroup (J ⧸ pCore 2 J) from
      le_sSup ⟨inferInstance,inferInstance⟩).trans le_sup_left
  have hXf : X ≤ ChapterA.Section04.twoGeneralizedFittingPreimage J := by
    apply map_mono
    exact (map_subtype_le _).trans (comap_mono (hB.trans hPf))
  have hXp : IsPPerfect 2 X :=
    (isPPerfect_embedded_pResidual 2 A).of_surjective
      (equivMapOfInjective X₀ J.subtype J.subtype_injective).toMonoidHom
      (equivMapOfInjective X₀ J.subtype J.subtype_injective).surjective
  have hQA : J.pCoreIn 2 ≤ A.map J.subtype := by
    apply map_mono
    intro x hx
    change q x ∈ B
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact B.one_mem
  have hQX : J.pCoreIn 2 ≤ normalizer (X : Set G) := by
    apply hQA.trans
    exact (map_mono (le_normalizer_embedded_pResidual 2 A)).trans (X₀.le_normalizer_map J.subtype)
  exact source_lemma_14_6_2 hG T hempty hM hu hmany hcard e hab
    J hJ.1 X hXf hXp hXne hQX


/-- Every literal actor supplied by the source splitting has the movement
assertion needed in 14.6.12(3). The two-core kernel is retained in the lift. -/
theorem source_ratio_factor_point
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (i : d.Index) :
    let A := (((d.factor i).actor.map (ChapterD.Jhat a.representation).subtype).comap
      (QuotientGroup.mk' (pCore 2 J)))
    centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) J,
      ((pResidual 2 A).map A.subtype).map J.subtype⁆ := by
  let K := ChapterD.Jhat a.representation
  let P := pResidual 2 (J ⧸ pCore 2 J)
  let A := (d.factor i).actor
  let B := A.map K.subtype ⊓ P
  have hPK : P ≤ K := source_solvable_minimal_residual_le_Jhat
    hG T hempty hM hu hmany hcard e hab J hJ hs a
  let : A.Normal := ChapterD.RatioDecomposition.Decomposition.actor_normal f.representation d f.faithful i
  have hAne : A ≠ ⊥ := by
    intro hz
    obtain ⟨x,hx⟩ := exists_ne (1 : (d.factor i).Carrier)
    have hh : (d.factor i).embedding.groupMap x = 1 :=
      mem_bot.mp (hz ▸ show (d.factor i).embedding.groupMap x ∈ A from ⟨x,rfl⟩)
    exact hx ((d.factor i).embedding.group_injective (by simpa using hh))
  have hBne : B ≠ ⊥ := by
    intro hz
    have hd : Disjoint A (P.subgroupOf K) := by
      apply disjoint_iff.mpr
      apply eq_bot_iff.mpr
      intro x hx
      have hb : (x : J ⧸ pCore 2 J) ∈ B := ⟨mem_map_of_mem K.subtype hx.1,hx.2⟩
      have he := mem_bot.mp (hz ▸ hb)
      exact Subtype.ext he
    have hc := commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
    have hAC : A.map K.subtype ≤ centralizer (P : Set (J ⧸ pCore 2 J)) := by
      rintro _ ⟨x,hx,rfl⟩ p hp
      exact congrArg Subtype.val (hc hx ⟨p,hPK hp⟩ hp)
    have hAP : A.map K.subtype ≤ P := hAC.trans
      (centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2))
    have hm : A.map K.subtype = ⊥ := (inf_eq_left.mpr hAP).symm.trans hz
    exact hAne ((map_eq_bot_iff_of_injective _ K.subtype_injective).mp hm)
  have hZ := source_point_le_lifted_odd_factor hG T hempty hM hu hmany hcard e hab
    J hJ hs B inf_le_right hBne
  apply hZ.trans
  apply commutator_mono le_rfl
  apply map_mono
  exact embedded_pResidual_mono 2 (comap_mono inf_le_left)

end CFSG.Quasithin.Chapter14.Section06
