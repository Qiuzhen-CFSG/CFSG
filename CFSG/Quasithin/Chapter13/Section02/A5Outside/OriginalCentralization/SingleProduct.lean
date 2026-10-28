module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SingleComponents
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.BorelQuotient
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity.Noncyclic
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity.Complete
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.SourceComponent
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentProduct.PrimeSource
public import Theory.GroupTheory.SymmetricThreeTwoCoreResidual
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.PResidual.PermutingNormalPrimeLift

/-!
# The original single-factor product and its cubic lift

The quotient's noncyclic three-core would make its two-residual a three-group,
contrary to the proved original 13.2.13. F.6.17 then supplies an oriented
component or a quasisimple two-residual. The latter has already been excluded.
Containment of the H residual in a component lifts through the actual 3′
kernel, contradicting the component's centralization of the whole omega-center.
Thus the Borel residual is the contained vertex.

The proved component sieve and product theorem now give the actual PSL₂(p)
factor, p congruent to 11 or 13 modulo 24, its cubic complement, the ordered
D₂₄ and S₄ vertices, multiplication, and both outer actions by the same Sylow
element. A cubic lift of the complement permutes with the prescribed Sylow
subgroup; the 3′ kernel makes this lift have order exactly three.

These are the source data for the final cubic-product exclusion. That exclusion,
the nonsolvable generation bound and earlier-source discharge remain with the
assembly owner. Source: Aschbacher--Smith 13.2.7, printed pp.883--884;
F.6.16--18, printed pp.308--310.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

private theorem residual_le_of_coprime_image
    {M : Type*} [Group M] [Finite M]
    (N K B : Subgroup M) [N.Normal] [K.Normal]
    (hN : Nat.Coprime 3 (Nat.card N))
    (hB : pResidual 2 B = primeToResidual 3 B)
    (hm : ((pResidual 2 B).map B.subtype).map (QuotientGroup.mk' N) ≤
      K.map (QuotientGroup.mk' N)) :
    (pResidual 2 B).map B.subtype ≤ K := by
  rw [hB] at hm ⊢
  let X := (primeToResidual 3 B).map B.subtype
  let U := K ⊔ N
  have hX : X ≤ U := by
    have hh := comap_mono (f := QuotientGroup.mk' N) hm
    rw [comap_map_eq,comap_map_eq,QuotientGroup.ker_mk'] at hh
    exact le_sup_left.trans hh
  have hself : (primeToResidual 3 X).map X.subtype = X := by
    dsimp only [X]
    rw [←map_embedded_primeToResidual_of_hom,
      embedded_primeToResidual_eq_of_normal 3 (primeToResidual 3 B) le_rfl]
  have hindex : Nat.Coprime 3 (K.subgroupOf U).index := by
    change Nat.Coprime 3 (K.relIndex (K ⊔ N))
    rw [relIndex_sup_left]
    exact hN.coprime_dvd_right (relIndex_dvd_card _ _)
  have hc := map_mono (f := U.subtype) (primeToResidual_le (K.subgroupOf U) hindex)
  rw [map_subgroupOf_eq_of_le (show K ≤ U from le_sup_left)] at hc
  have hh := embedded_primeToResidual_mono 3 hX
  rw [hself] at hh
  exact hh.trans hc

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The H vertex escapes every ordinary component in the actual quotient. -/
theorem single_right_residual_escapes_component
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    let J := H ⊔ borelResidual T L
    let A := (borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J
    let B := H.subgroupOf J
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    IsSQTK KnownSimple.IsKnownSimple J →
    ChapterF.IsGoldschmidtTriple A B →
    ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) →
    ∀ E : Subgroup (J ⧸ pPrimeCore 3 J), IsComponent (J ⧸ pPrimeCore 3 J) E →
      ¬ (pResidual 2 (B.map q)).map (B.map q).subtype ≤ E := by
  intro J A B q hSQ hg hqg E hE hle
  obtain ⟨K,hK,hKn,hmap,hcent⟩ := single_quotient_component_lift_centralizes
    d hH hB hZ hSQ hg hqg E hE
  let : K.Normal := hKn
  have hr : (pResidual 2 B).map B.subtype ≤ K := by
    apply residual_le_of_coprime_image (pPrimeCore 3 J) K B pPrimeCore_coprime_card
      (SymmetricThreeTwoCore.twoResidual_eq_primeToThree hg.quotient_right.some)
    rw [map_embedded_pResidual,hmap]
    exact hle
  have hrG := (map_mono (f := J.subtype) hr).trans hcent
  rw [map_embedded_pResidual,map_subgroupOf_eq_of_le (show H ≤ J from le_sup_left)] at hrG
  exact residual_moves_omegaCenter T hH.1.1.2 hZ hrG

/-- The original quotient has the correctly oriented component: its Borel
residual is contained, whereas the H residual escapes. -/
theorem single_quotient_oriented_component
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    let J := H ⊔ borelResidual T L
    let A := (borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J
    let B := H.subgroupOf J
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    IsSQTK KnownSimple.IsKnownSimple J →
    ChapterF.IsGoldschmidtTriple A B →
    ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) →
    Nonempty (ChapterF.SourceAssembly.SingleResidualComponent (A.map q) (B.map q)) := by
  intro J A B q hSQ hg hqg
  let : Group.IsSolvable B := hg.symm.local_solvable
  have hs : Group.IsSolvable H := Group.isSolvable_of_surjective
    (f := (subgroupOfEquivOfLe (show H ≤ J from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show H ≤ J from le_sup_left)).surjective
  have hn := not_three_borel_quotient d hH hB hZ hs
  have hcyc : IsCyclic (pCore 3 (J ⧸ pPrimeCore 3 J)) := by
    by_contra hnc
    exact hn (ChapterF.SourceAssembly.residual_isThreeGroup_of_cover hSQ
      (MulEquiv.refl _) hqg hnc)
  rcases ChapterF.SourceAssembly.source_F_6_17_reduction
    ChapterA.Section02.theoremA_knownSimple hSQ (MulEquiv.refl _) hqg hcyc with
    hquasi | hrest
  · exact (single_quotient_residual_not_quasisimple d hH hB hZ hSQ hg hqg hquasi.2).elim
  · rcases hrest with hleft | hright
    · exact hleft
    obtain ⟨hright⟩ := hright
    exact (single_right_residual_escapes_component d hH hB hZ hSQ hg hqg
      hright.component hright.isComponent hright.left_contains).elim

omit d [Group G] [Finite G] in
private theorem exists_cubic_lift
    {M : Type*} [Group M] [Finite M] (S : Sylow 2 M)
    (D : Subgroup (M ⧸ pPrimeCore 3 M)) [D.Normal] (hD : Nat.card D = 3) :
    ∃ Y : Subgroup M, Nat.card Y = 3 ∧
      Y.map (QuotientGroup.mk' (pPrimeCore 3 M)) = D ∧ Y ≤ pResidual 2 M ∧
      (S : Set M) * (Y : Set M) = (Y : Set M) * (S : Set M) := by
  let q := QuotientGroup.mk' (pPrimeCore 3 M)
  obtain ⟨Y,hY,_,hperm,hmap,hle⟩ := exists_permuting_normal_prime_lift q
    (QuotientGroup.mk'_surjective _) S (p := 3) (by decide) D hD
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card (pPrimeCore 3 M)) := by
    obtain ⟨n,hn⟩ := hY.exists_card_eq
    rw [hn]
    exact pPrimeCore_coprime_card.pow_left n
  have hdis : Y ⊓ pPrimeCore 3 M = ⊥ := (disjoint_of_coprime_natCard hcop).eq_bot
  have hinj : Function.Injective (q.subgroupMap Y) := by
    apply (injective_iff_map_eq_one _).mpr
    intro y hy
    have hk : (y : M) ∈ pPrimeCore 3 M :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hy)
    have hb : (y : M) ∈ (⊥ : Subgroup M) := hdis ▸ ⟨y.property,hk⟩
    exact Subtype.ext (mem_bot.mp hb)
  let e : Y ≃* Y.map q := MulEquiv.ofBijective (q.subgroupMap Y)
    ⟨hinj,q.subgroupMap_surjective Y⟩
  have hc : Nat.card Y = 3 := (Nat.card_congr e.toEquiv).trans (hmap.symm ▸ hD)
  exact ⟨Y,hc,hmap,hle,hperm⟩

/-- The final single-factor row, with the original ordered vertices, the
normal component lift, actual prime-field model, cubic complement and
multiplication, and both actions of the same Sylow element. -/
structure SingleQuotientProduct
    (T : Sylow 2 G) (L H : Subgroup G) where
  selected : ChapterF.SourceAssembly.SingleResidualComponent
    (((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf (H ⊔ borelResidual T L)).map
      (QuotientGroup.mk' (pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G))))
    ((H.subgroupOf (H ⊔ borelResidual T L)).map
      (QuotientGroup.mk' (pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G))))
  lift : Subgroup (H ⊔ borelResidual T L : Subgroup G)
  lift_component : lift.IsCComponent
  lift_normal : lift.Normal
  lift_image : lift.map (QuotientGroup.mk' (pPrimeCore 3
    (H ⊔ borelResidual T L : Subgroup G))) = selected.component
  lift_centralizes : lift.map (H ⊔ borelResidual T L).subtype ≤
    centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)
  prime : ℕ
  prime_isPrime : prime.Prime
  prime_odd : Odd prime
  prime_congruence : prime % 24 = 11 ∨ prime % 24 = 13
  first_model : letI : Fact prime.Prime := ⟨prime_isPrime⟩
    Nonempty (selected.component ≃* PSL(2,ZMod prime))
  left_model : Nonempty
    ((((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf (H ⊔ borelResidual T L)).map
      (QuotientGroup.mk' (pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G)))) ≃*
      DihedralGroup 12)
  right_model : Nonempty
    (((H.subgroupOf (H ⊔ borelResidual T L)).map
      (QuotientGroup.mk' (pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G)))) ≃*
      Equiv.Perm (Fin 4))
  intersection_model : Nonempty
    (((((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf (H ⊔ borelResidual T L)).map
      (QuotientGroup.mk' (pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G)))) ⊓
      ((H.subgroupOf (H ⊔ borelResidual T L)).map
      (QuotientGroup.mk' (pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G)))) :
      Subgroup ((H ⊔ borelResidual T L : Subgroup G) ⧸
        pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G))) ≃* DihedralGroup 4)
  second_normal : (pResidual 2 ((H ⊔ borelResidual T L : Subgroup G) ⧸
      pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G)) ⊓
      centralizer (selected.component : Set _)).Normal
  second_card : Nat.card (pResidual 2 ((H ⊔ borelResidual T L : Subgroup G) ⧸
      pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G)) ⊓
      centralizer (selected.component : Set _) : Subgroup _) = 3
  generates : selected.component ⊔ (pResidual 2 ((H ⊔ borelResidual T L : Subgroup G) ⧸
      pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G)) ⊓
      centralizer (selected.component : Set _)) = pResidual 2 _
  disjoint : Disjoint selected.component (pResidual 2 ((H ⊔ borelResidual T L : Subgroup G) ⧸ pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G)) ⊓
    centralizer (selected.component : Set ((H ⊔ borelResidual T L : Subgroup G) ⧸ pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G))))
  multiplication :
    let J := H ⊔ borelResidual T L
    let Q := J ⧸ pPrimeCore 3 J
    let D := pResidual 2 Q ⊓ centralizer (selected.component : Set Q)
    ∃ f : selected.component × D ≃* pResidual 2 Q,
      ∀ k a, (f (k,a) : Q) = (k : Q) * (a : Q)
  outer_actions :
    let J := H ⊔ borelResidual T L
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    let A := (borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J
    let B := H.subgroupOf J
    let D := pResidual 2 (J ⧸ pPrimeCore 3 J) ⊓ centralizer (selected.component : Set _)
    ∀ t : J ⧸ pPrimeCore 3 J, t ∈ A.map q ⊓ B.map q → t ∉ selected.component →
      (∃ α : MulAut selected.component,
        (∀ a : selected.component, (α a : J ⧸ pPrimeCore 3 J) = t * (a : J ⧸ pPrimeCore 3 J) * t⁻¹) ∧
        α ∉ MulAut.innerSubgroup selected.component) ∧
      (∃ β : MulAut D, (∀ a : D, (β a : J ⧸ pPrimeCore 3 J) = t * (a : J ⧸ pPrimeCore 3 J) * t⁻¹) ∧
        β ∉ MulAut.innerSubgroup D)
  outer_element :
    let J := H ⊔ borelResidual T L
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    let A := (borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J
    let B := H.subgroupOf J
    ∃ t : J ⧸ pPrimeCore 3 J, t ∈ A.map q ⊓ B.map q ∧ t ∉ selected.component

  cubic_lift : Subgroup (H ⊔ borelResidual T L : Subgroup G)
  cubic_card : Nat.card cubic_lift = 3
  cubic_image :
    let J := H ⊔ borelResidual T L
    cubic_lift.map (QuotientGroup.mk' (pPrimeCore 3 J)) =
      pResidual 2 (J ⧸ pPrimeCore 3 J) ⊓ centralizer (selected.component : Set _)
  cubic_residual : cubic_lift ≤ pResidual 2 (H ⊔ borelResidual T L : Subgroup G)
  cubic_permutes :
    let J := H ⊔ borelResidual T L
    (((T : Subgroup G).subgroupOf J : Subgroup J) : Set J) * (cubic_lift : Set J) =
      (cubic_lift : Set J) * (((T : Subgroup G).subgroupOf J : Subgroup J) : Set J)

/-- All remaining F.6 rows reduce to the literal cubic × PSL₂(p) product,
with the Borel and H vertices in the source order. -/
theorem single_quotient_prime_product
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    let J := H ⊔ borelResidual T L
    let A := (borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J
    let B := H.subgroupOf J
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    IsSQTK KnownSimple.IsKnownSimple J →
    ChapterF.IsGoldschmidtTriple A B →
    ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) →
    pCore 2 (J ⧸ pPrimeCore 3 J) = ⊥ →
    Nonempty (SingleQuotientProduct T L H) := by
  intro J A B q hSQ hg hqg hcore
  obtain ⟨c⟩ := single_quotient_oriented_component d hH hB hZ hSQ hg hqg
  have hbad := c.left_not_characteristic_two hqg hcore
  obtain ⟨p,hp,ho,h8,hm⟩ := c.prime_psl2_of_either_exceptional
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple
    hSQ (MulEquiv.refl _) hqg hcore (Or.inl hbad)
  let : Fact p.Prime := ⟨hp⟩
  have hc := (c.exceptional_component_data (MulEquiv.refl _) hqg hcore (Or.inl hbad)).1
  obtain ⟨h24,hl,hr,ht,hDn,hDc,hs,hd,he,hprod,hall,t,htT,htK,_⟩ :=
    c.source_prime_conclusion (MulEquiv.refl _) hqg ho h8 hm hc
  obtain ⟨K,hK,hKn,hmap,hcent⟩ :=
    single_quotient_component_lift_centralizes d hH hB hZ hSQ hg hqg c.component c.isComponent
  let D := pResidual 2 (J ⧸ pPrimeCore 3 J) ⊓ centralizer (c.component : Set _)
  let : D.Normal := hDn
  let S := T.subtype (hH.1.1.2.trans (show H ≤ J from le_sup_left))
  obtain ⟨Y,hY,hYm,hYR,hYT⟩ := exists_cubic_lift S D hDc
  exact ⟨{ selected := c
           lift := K
           lift_component := hK
           lift_normal := hKn
           lift_image := hmap
           lift_centralizes := hcent
           prime := p
           prime_isPrime := hp
           prime_odd := ho
           prime_congruence := h24
           first_model := he
           left_model := hl
           right_model := hr
           intersection_model := ht
           second_normal := hDn
           second_card := hDc
           generates := hs
           disjoint := hd
           multiplication := hprod
           outer_actions := hall
           outer_element := ⟨t,htT,htK⟩
           cubic_lift := Y
           cubic_card := hY
           cubic_image := hYm
           cubic_residual := hYR
           cubic_permutes := hYT }⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
