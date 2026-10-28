module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PairedQuotient
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.BorelJoin
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree
public import Theory.SpecificGroups.SymmetricFive.SylowNormalizer
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.CubicSylowJoin
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.SpecificGroups.SymmetricThree.CubicSelection

/-!
# The original single-factor Borel amalgam

The actual Borel residual has cubic two-core quotient, so adjoining the
prescribed Sylow subgroup gives index three. In a moving configuration
the full local action is S₅. Its self-normalizing Sylow image lifts through
the actual two-core kernel, excluding a normal Sylow in the Borel
supplement and identifying its two-core quotient with S₃.

When H/O₂(H) is S₃, prime index and the outside condition show that
L₁T intersects H in exactly T. The contrary trivial core of H₀ = ⟨H,L₁⟩
would force the paired quotient of order72; hence O₂(H₀) is nontrivial
and H₀ is SQTK. The original pair is a Goldschmidt triple. With the
explicit earlier13.2.13 premise, F.6.11 excludes collapse after quotienting
by O₃′(H₀), preserving the Sylow intersection and the compatible amalgam.

Baumann control is needed only for the nontrivial join core; neither it
nor13.2.13 is proved here. Their discharge and the remaining paired and
single-factor exclusions stay with qt-d-1367-assembly. The literal terminal
application is SourceAssembly/SingleAmalgam. This does not assert13.2.7.

Source: Aschbacher--Smith13.2.11--14 and the completion of13.2.7,
printed pp.881--884; F.6.1 and F.6.11, pp.304,306--307.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The original Borel supplement has Sylow index three. -/
theorem borel_sylow_index_three :
    (T : Subgroup G).relIndex (borelResidual T L ⊔ (T : Subgroup G)) = 3 := by
  let A := borelResidual T L
  have hc := borelResidual_quotient_card d
  change Nat.card (A ⧸ pCore 2 A) = 3 at hc
  apply normalized_cubic_join_index_of_card_dvd T A (sylow_normalizes_borelResidual d)
  · obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
    refine ⟨n, ?_⟩
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A),hc,hn]
  · intro hp
    have hq := hp.of_surjective (QuotientGroup.mk' (pCore 2 A))
      (QuotientGroup.mk'_surjective (pCore 2 A))
    rcases hq.card_eq_or_dvd with h | h <;> rw [hc] at h <;> norm_num at h

/-- In the moving branch the prescribed Sylow is self-normalizing inside LT. -/
theorem local_sylow_self_normalizing_of_omega_movement
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    let S := T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)
    normalizer (S : Set (L ⊔ (T : Subgroup G) : Subgroup G)) = S := by
  let K := L ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
  let q := d.localActor
  have hq : Function.Surjective q := localActor_surjective_of_omega_movement d hH hZ
  have hk : q.ker ≤ (S : Subgroup K) := by
    rw [d.localActor_kernel_eq_core d.normalizes_L]
    exact pCore_isPGroup.le_sylow_of_normal S
  have hp : ((S : Subgroup K).map q).comap q = S := comap_map_eq_self hk
  let P := S.mapSurjective hq
  change normalizer (S : Set K) = S
  calc
    normalizer (S : Set K) = normalizer (((S : Subgroup K).map q).comap q : Set K) := by
      rw [hp,Sylow.coe_coe]
    _ = (normalizer ((S : Subgroup K).map q : Set (Equiv.Perm (Fin 5)))).comap q :=
      (comap_normalizer_eq_of_surjective _ hq).symm
    _ = (S : Subgroup K) := by
      have hn := Theory.SpecificGroups.SymmetricFive.SylowNormalizer.sylow_normalizer_eq_self P
      rw [←Sylow.coe_coe,Sylow.coe_mapSurjective] at hn
      rw [hn,hp]

/-- The literal Borel supplement has two-core quotient S₃, without Baumann control. -/
theorem borel_sylow_core_quotient
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    let P := borelResidual T L ⊔ (T : Subgroup G)
    Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) := by
  let K := L ⊔ (T : Subgroup G)
  let P := borelResidual T L ⊔ (T : Subgroup G)
  have hAL : borelResidual T L ≤ L := by
    rw [borelResidual_eq_point_residual d]
    exact Section05.A5Source.ThirdSpace.residual_le_centralizer.trans inf_le_left
  have hPK : P ≤ K := sup_le_sup hAL le_rfl
  have hTP : (T : Subgroup G) ≤ P := le_sup_right
  let R := T.subtype (show (T : Subgroup G) ≤ P from le_sup_right)
  let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
  have hi : (R : Subgroup P).index = 3 := borel_sylow_index_three d
  apply sylow_index_three_core_quotient R hi
  apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal R)
  intro he
  have hn : (R : Subgroup P).Normal := he ▸ inferInstance
  have hPT : P ≤ (T : Subgroup G) := by
    intro p hp
    have hpK : (⟨p,hPK hp⟩ : K) ∈ normalizer (S : Set K) := by
      apply mem_normalizer_iff.mpr
      intro t
      constructor
      · intro ht
        have htP : (t : G) ∈ P := hTP ht
        exact hn.conj_mem ⟨t,htP⟩ ht ⟨p,hp⟩
      · intro ht
        have htP : p * (t : G) * p⁻¹ ∈ P := hTP ht
        have hh := hn.conj_mem ⟨p * (t : G) * p⁻¹,htP⟩ ht (⟨p,hp⟩ : P)⁻¹
        change p⁻¹ * (p * (t : G) * p⁻¹) * p⁻¹⁻¹ ∈ (T : Subgroup G) at hh
        change (t : G) ∈ (T : Subgroup G)
        simpa [mul_assoc] using hh
    rw [local_sylow_self_normalizing_of_omega_movement d hH hZ] at hpK
    exact hpK
  have hPT' : P = (T : Subgroup G) := le_antisymm hPT le_sup_right
  have hi' := borel_sylow_index_three d
  rw [show borelResidual T L ⊔ (T : Subgroup G) = (T : Subgroup G) from hPT',relIndex_self] at hi'
  contradiction

/-- Source13.2.12 in the single-factor case: the core-free alternative would give order72 instead of6. -/
theorem single_borel_join_core_ne_bot
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    (H ⊔ borelResidual T L).pCoreIn 2 ≠ ⊥ := by
  intro hz
  obtain ⟨e⟩ := he
  have hs := SymmetricThreeTwoCore.solvable e
  obtain ⟨⟨f⟩,_⟩ := coreFree_borel_join_paired_models d hH hB hZ hs hz
  have hec : Nat.card (H ⧸ pCore 2 H) = 6 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hfc : Nat.card (H ⧸ pCore 2 H) = 72 := by
    rw [Nat.card_congr f.toEquiv,RegularWreathProduct.card]
    obtain ⟨e3⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    rw [Nat.card_congr e3.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  omega

/-- The actual Borel supplement and the outside group intersect in the original Sylow subgroup. -/
theorem single_borel_intersection
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    (borelResidual T L ⊔ (T : Subgroup G)) ⊓ H = (T : Subgroup G) := by
  let P := borelResidual T L ⊔ (T : Subgroup G)
  have hPM : P ≤ normalizer (L : Set G) := by
    apply sup_le ?_ d.normalizes_L
    rw [borelResidual_eq_point_residual d]
    exact (Section05.A5Source.ThirdSpace.residual_le_centralizer.trans inf_le_left).trans L.le_normalizer
  let S := T.subtype hH.1.1.2
  let D := (P ⊓ H).subgroupOf H
  have hTP : (T : Subgroup G) ≤ P := le_sup_right
  have hSD : (S : Subgroup H) ≤ D := fun x hx => ⟨hTP hx,x.property⟩
  have hproper : D ≠ ⊤ := by
    intro ht
    apply hH.1.2
    intro x hx
    exact hPM ((show (⟨x,hx⟩ : H) ∈ D from ht ▸ mem_top _).1)
  have hi := SymmetricThreeTwoCore.sylow_index_three he.some S
  have hh := relIndex_mul_index hSD
  rw [hi] at hh
  have hp : ((S : Subgroup H).relIndex D * D.index).Prime := hh ▸ Nat.prime_three
  have heq : D = (S : Subgroup H) := by
    rcases Nat.prime_mul_iff.mp hp with ⟨_,hD⟩ | ⟨_,hS⟩
    · exact (hproper (index_eq_one.mp hD)).elim
    · exact le_antisymm (relIndex_eq_one.mp hS) hSD
  have hm := congrArg (map H.subtype) heq
  change ((P ⊓ H).subgroupOf H).map H.subtype =
    ((T : Subgroup G).subgroupOf H).map H.subtype at hm
  rw [map_subgroupOf_eq_of_le (show P ⊓ H ≤ H from inf_le_right),
    map_subgroupOf_eq_of_le hH.1.1.2] at hm
  exact hm

/-- Construct the actual triple (H₀,L₁T,H), including the literal Sylow intersection. -/
theorem single_borel_goldschmidt_triple
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    let J := H ⊔ borelResidual T L
    ChapterF.IsGoldschmidtTriple
      ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J) (H.subgroupOf J) := by
  let P := borelResidual T L ⊔ (T : Subgroup G)
  let J := H ⊔ borelResidual T L
  have hHJ : H ≤ J := le_sup_left
  have hPJ : P ≤ J := sup_le le_sup_right (hH.1.1.2.trans hHJ)
  have hTJ : (T : Subgroup G) ≤ J := hH.1.1.2.trans hHJ
  have hquot (X : Subgroup G) (hX : X ≤ J)
      (he : Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3))) :
      Nonempty ((X.subgroupOf J ⧸ pCore 2 (X.subgroupOf J)) ≃* Equiv.Perm (Fin 3)) := by
    let e := subgroupOfEquivOfLe hX
    exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans he.some⟩
  refine ⟨?_, hquot P hPJ (borel_sylow_core_quotient d hH hZ), hquot H hHJ he, ?_⟩
  · apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hPJ,map_subgroupOf_eq_of_le hHJ,
      ←MonoidHom.range_eq_map,range_subtype]
    apply le_antisymm (sup_le hPJ hHJ)
    exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
  · refine ⟨T.subtype hTJ, ?_⟩
    change (P ⊓ H).subgroupOf J = (T : Subgroup G).subgroupOf J
    rw [single_borel_intersection d hH he]

/-- The nontrivial core puts the original single-factor join in the SQTK family. -/
theorem single_borel_join_sqtk
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    IsSQTK KnownSimple.IsKnownSimple (H ⊔ borelResidual T L : Subgroup G) :=
  Chapter3.sqtk_of_mem_H d.hypothesis.qtke (single_borel_join_core_ne_bot d hH hB hZ he)

/-- Source13.2.13 selects the faithful F.6.11 quotient with its original maps and compatible amalgam. -/
theorem single_borel_quotient_amalgam
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)))
    (hnot : let J := H ⊔ borelResidual T L
      ¬ IsPGroup 3 (pResidual 2 (J ⧸ pPrimeCore 3 J))) :
    let J := H ⊔ borelResidual T L
    let P := (borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J
    let Q := H.subgroupOf J
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    P.map q ⊓ Q.map q = ((T : Subgroup G).subgroupOf J).map q ∧
      ChapterF.IsGoldschmidtTriple (P.map q) (Q.map q) ∧
      pCore 2 (J ⧸ pPrimeCore 3 J) = ⊥ ∧
      Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroupQuotients (QuotientGroup.mk' (pCore 2 J))
          P (P ⊓ Q) Q inf_le_left inf_le_right)
        (RankTwoAmalgam.ofSubgroups (P.map q) ((P ⊓ Q).map q) (Q.map q)
          (map_mono inf_le_left) (map_mono inf_le_right))) := by
  let J := H ⊔ borelResidual T L
  have h := single_borel_goldschmidt_triple d hH hZ he
  rcases h.primeToThreeCore_dichotomy with hh | hh
  · have hi : ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J) ⊓
        H.subgroupOf J = (T : Subgroup G).subgroupOf J := by
      change ((borelResidual T L ⊔ (T : Subgroup G)) ⊓ H).subgroupOf J = _
      rw [single_borel_intersection d hH he]
    exact ⟨hh.1.trans (congrArg (map (QuotientGroup.mk' (pPrimeCore 3 J))) hi),hh.2⟩
  · obtain ⟨e⟩ := hh.2.2.1
    let eR := ((pResidual 2 (J ⧸ pPrimeCore 3 J)).equivMapOfInjective
      e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2 e.toMonoidHom e.surjective))
    exact (hnot (IsPGroup.of_card (n := 1) ((Nat.card_congr eR.toEquiv).trans
      Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_card))).elim

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
