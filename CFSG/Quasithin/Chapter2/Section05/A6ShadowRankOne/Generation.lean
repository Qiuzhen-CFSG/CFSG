module

public import Theory.SpecificGroups.AlternatingSix.CommutingLocalRank
public import Theory.GroupTheory.PGroup.UniqueInvolution

/-!
# Centralizer generation in the final A₆ shadow

An A₆ component in an involution centralizer is relatively normal, by the
quasithin obstruction for commuting A₆ subgroups. The two centralizers at
`tˣ` and `iˣ` then normalize `Kˣ`. Maximality of S in H and an element of
C_K(iˣ) outside S show that H normalizes Kˣ. Conjugating this inclusion and
using x²∈S gives mutual normalization. The distinct copies K and Kˣ are
components in their join, so commute, violating quasithinness.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 2.5.26, printed p.569, final paragraph.

The exported rank theorem is conditional on the component claim. The preceding
A₈ elimination must discharge that claim in the source assembly. The remaining
local-model inputs explicitly specify maximality, the centralizer C_H(tˣ),
and C_K(iˣ) not lying in S. Universal component normality is proved here,
not postulated, and is always relative to the involution centralizer.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.A6ShadowRankOne

variable {G : Type*} [Group G] [Finite G]

private theorem centralizer_le_normalizer_of_component
    (hG : IsQuasithin G) (K : Subgroup G) (i : G)
    (eK : K ≃* alternatingGroup (Fin 6))
    (hKi : K ≤ centralizer {i})
    (hi : Theory.GroupTheory.IsComponent (centralizer ({i} : Set G))
      (K.subgroupOf (centralizer {i}))) : centralizer ({i} : Set G) ≤ normalizer K := by
  have hn := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.subgroup (centralizer {i})) _ ((subgroupOfEquivOfLe hKi).trans eK) hi
  exact (normal_subgroupOf_iff_le_normalizer hKi).mp hn

omit [Finite G] in
private theorem centralizer_conjugate_normalizes (K : Subgroup G) (i x : G)
    (h : centralizer ({i} : Set G) ≤ normalizer K) :
    centralizer ({MulAut.conj x i} : Set G) ≤ normalizer (K.map (MulAut.conj x).toMonoidHom) := by
  intro a ha
  rw [← map_equiv_normalizer_eq K (MulAut.conj x)]
  apply mem_map_equiv.mpr
  apply h
  rw [mem_centralizer_singleton_iff] at ha ⊢
  apply (MulAut.conj x).injective
  simpa only [map_mul, MulEquiv.apply_symm_apply] using ha

/-- The centralizer-generation step on p.569. The model inputs are maximality
of S in H, C_H(tˣ)=S, and the precise failure C_K(iˣ)≤S. -/
theorem false_of_component_centralizers_of_outside_involution
    (hG : IsQuasithin G) (K H S SC : Subgroup G) (t x i : G)
    (eK : K ≃* alternatingGroup (Fin 6))
    (hKH : K ≤ H) (hSH : S ≤ H)
    (hSC : SC ≤ centralizer (K : Set G))
    (ht : t ∈ SC) (ht2 : orderOf t = 2)
    (hi : i ∈ SC) (hi2 : orderOf i = 2)
    (hcomponents : ∀ j : G, j ∈ SC → orderOf j = 2 →
      Theory.GroupTheory.IsComponent (centralizer ({j} : Set G))
        (K.subgroupOf (centralizer {j})))
    (hmax : IsCoatom (S.subgroupOf H))
    (hCt : H ⊓ centralizer ({MulAut.conj x t} : Set G) = S)
    (hout : ¬ K ⊓ centralizer ({MulAut.conj x i} : Set G) ≤ S)
    (htxK : MulAut.conj x t ∈ K)
    (hxx : (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom = K) :
    False := by
  let a := MulAut.conj x
  let L := K.map a.toMonoidHom
  have hKj (j : G) (hj : j ∈ SC) : K ≤ centralizer ({j} : Set G) := by
    intro k hk
    rw [mem_centralizer_singleton_iff]
    exact hSC hj k hk
  have hNt := centralizer_le_normalizer_of_component hG K t eK (hKj t ht)
    (hcomponents t ht ht2)
  have hNi := centralizer_le_normalizer_of_component hG K i eK (hKj i hi)
    (hcomponents i hi hi2)
  have hS : S ≤ normalizer L := by
    rw [← hCt]
    exact inf_le_right.trans (centralizer_conjugate_normalizes K t x hNt)
  have hC : K ⊓ centralizer ({a i} : Set G) ≤ normalizer L :=
    inf_le_right.trans (centralizer_conjugate_normalizes K i x hNi)
  let R := S ⊔ (K ⊓ centralizer ({a i} : Set G))
  have hRH : R ≤ H := sup_le hSH (inf_le_left.trans hKH)
  have hSR : S < R := lt_of_le_not_ge le_sup_left
    (fun hr => hout (le_sup_right.trans hr))
  have hSR' : S.subgroupOf H < R.subgroupOf H := by
    apply lt_of_le_not_ge (subgroupOf_mono H hSR.le)
    intro hr
    have hm := map_mono (f := H.subtype) hr
    rw [map_subgroupOf_eq_of_le hSH, map_subgroupOf_eq_of_le hRH] at hm
    exact hSR.not_ge hm
  have hHR : H ≤ R := subgroupOf_eq_top.mp (hmax.lt_iff.mp hSR')
  have hHN : H ≤ normalizer L := hHR.trans (sup_le hS hC)
  have hKN : K ≤ normalizer L := hKH.trans hHN
  have hLN : L ≤ normalizer K := by
    have hm := map_mono (f := a.toMonoidHom) hKN
    rw [map_equiv_normalizer_eq] at hm
    exact hxx ▸ hm
  have hne : K ≠ L := by
    intro he
    have hac : a t ∈ centralizer (L : Set G) := by
      intro l hl
      obtain ⟨k, hk, rfl⟩ := hl
      change a.toMonoidHom k * a.toMonoidHom t = a.toMonoidHom t * a.toMonoidHom k
      rw [← map_mul, ← map_mul, hSC ht k hk]
    have haz : (⟨a t, htxK⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro k
      apply Subtype.ext
      exact hac k (he ▸ k.property)
    have hez := (centerCongr eK ⟨⟨a t, htxK⟩, haz⟩).property
    change eK ⟨a t, htxK⟩ ∈ center (alternatingGroup (Fin 6)) at hez
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hez
    have hat : a t = 1 := congrArg Subtype.val (eK.injective (hez.trans eK.map_one.symm))
    have ht1 : t = 1 := a.injective (hat.trans a.map_one.symm)
    simp [ht1] at ht2
  let J := K ⊔ L
  have hKJ : K ≤ J := le_sup_left
  have hLJ : L ≤ J := le_sup_right
  have hnK : (K.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer hLN)
  have hnL : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le hKN L.le_normalizer)
  let := hnK
  let := hnL
  have hqK : IsQuasisimple K := by
    let := (hcomponents t ht ht2).2
    exact Theory.GroupTheory.IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (hKj t ht))
  let := hqK
  have hqL : IsQuasisimple L := Theory.GroupTheory.IsQuasisimple.of_mulEquiv (a.subgroupMap K)
  let := hqL
  have hKc : Theory.GroupTheory.IsComponent J (K.subgroupOf J) :=
    ⟨Subgroup.Normal.isSubnormal inferInstance,
      Theory.GroupTheory.IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hKJ).symm⟩
  have hLc : Theory.GroupTheory.IsComponent J (L.subgroupOf J) :=
    ⟨Subgroup.Normal.isSubnormal inferInstance,
      Theory.GroupTheory.IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLJ).symm⟩
  have hn : K.subgroupOf J ≠ L.subgroupOf J := by
    intro he
    apply hne
    have hm := congrArg (Subgroup.map J.subtype) he
    simpa only [map_subgroupOf_eq_of_le hKJ, map_subgroupOf_eq_of_le hLJ] using hm
  have hc := congrArg (Subgroup.map J.subtype) (hKc.commutator_eq_bot_of_ne hLc hn)
  rw [map_commutator, map_subgroupOf_eq_of_le hKJ,
    map_subgroupOf_eq_of_le hLJ, Subgroup.map_bot] at hc
  exact alternatingGroup.not_commuting_a6_of_quasithin hG K L eK
    ((a.subgroupMap K).symm.trans eK) (commutator_eq_bot_iff_le_centralizer.mp hc)

/-- The rank-one conclusion after the exceptional branch has supplied the
component claim. No normality of any involution centralizer is an input. -/
theorem primeRank_eq_one_of_component_centralizers
    (hG : IsQuasithin G) (K H S SC : Subgroup G) (t x : G)
    (eK : K ≃* alternatingGroup (Fin 6))
    (hKH : K ≤ H) (hSH : S ≤ H) (hH : H = centralizer {t})
    (hSC : SC ≤ centralizer (K : Set G)) (hSCp : IsPGroup 2 SC)
    (ht : t ∈ SC) (ht2 : orderOf t = 2)
    (hcomponents : ∀ j : G, j ∈ SC → orderOf j = 2 →
      Theory.GroupTheory.IsComponent (centralizer ({j} : Set G))
        (K.subgroupOf (centralizer {j})))
    (hmax : IsCoatom (S.subgroupOf H))
    (hCt : H ⊓ centralizer ({MulAut.conj x t} : Set G) = S)
    (hout : ∀ i : G, i ∈ SC → orderOf i = 2 → i ≠ t →
      ¬ K ⊓ centralizer ({MulAut.conj x i} : Set G) ≤ S)
    (htxK : MulAut.conj x t ∈ K) (hx2 : x * x ∈ S) :
    primeRank 2 SC = 1 := by
  have hKt : K ≤ centralizer ({t} : Set G) := hH ▸ hKH
  have hN := centralizer_le_normalizer_of_component hG K t eK hKt
    (hcomponents t ht ht2)
  have hxx : (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom = K := by
    have he : (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom =
        K.map (MulAut.conj (x * x)).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext k
      simp [MulAut.conj_apply, mul_assoc]
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp (hN (hH ▸ hSH hx2))
  have hu : ∀ i : G, i ∈ SC → orderOf i = 2 → i = t := by
    intro i hi hi2
    by_contra hit
    exact false_of_component_centralizers_of_outside_involution hG K H S SC t x i
      eK hKH hSH hSC ht ht2 hi hi2 hcomponents hmax hCt
      (hout i hi hi2 hit) htxK hxx
  have huSC : ∃! z : SC, orderOf z = 2 := by
    refine ⟨⟨t, ht⟩, ?_, ?_⟩
    · simpa using ht2
    · intro z hz
      exact Subtype.ext (hu z z.property (by simpa using hz))
  apply le_antisymm
  · apply (primeRank_le_iff 2 1).mpr
    intro A hp hc
    let := hc
    have hcyc := hSCp.isCyclic_abelian_subgroup_of_unique_involution huSC A
    classical
    obtain ⟨a, ha⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := A)).mp hcyc
    have hgen : closure (({a} : Finset A) : Set A) = ⊤ := by
      simpa only [Finset.coe_singleton, ← zpowers_eq_closure] using ha
    simpa only [Finset.card_singleton] using Group.rank_le hgen
  · let C := zpowers (⟨t, ht⟩ : SC)
    let : CommGroup C := IsCyclic.commGroup
    have hc : Nat.card C = 2 := by rw [Nat.card_zpowers]; simpa using ht2
    apply primeRank_ge_of_elementary_embedding (A := C) (f := C.subtype)
    · intro c
      simpa only [hc] using pow_card_eq_one' (x := c)
    · simpa using hc
    · exact C.subtype_injective

end CFSG.Quasithin.Chapter2.A6ShadowRankOne
