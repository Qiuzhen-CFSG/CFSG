module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceBaumannCharacteristicExclusion
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.OddCore
public import Theory.GroupTheory.CComponent.ConstrainedPrimeJoin

/-!
# Reconstructing the source component from its actual natural seven-space

Use C.1.24 on the literal component--Sylow join and its marked natural
module. The crossing element excludes the normal characteristic Baumann
alternative. Consequently the original selected component is a block.
No equality between the initial moved layer and U(K), no shortness, and
no identification of the action kernel with the two-core is assumed.

Source: Aschbacher--Smith C.1.24(a), pp.130--131, and original4.3.3--7,
pp.614--616.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem no_join_characteristic_baumann
    (c : SourceConfiguration T L)
    (P : Sylow 2 (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G))
    (hP : (P : Subgroup _).map
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)).subtype = (T : Subgroup G) ⊓ c.H)
    (A : Subgroup (ChapterB.baumann (P : Subgroup
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G))))
    (hA : A.Characteristic) (hne : A ≠ ⊥)
    (hn : (A.map (ChapterB.baumann (P : Subgroup
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G))).subtype).Normal) : False := by
  let J := c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)
  let B := ChapterB.baumann (P : Subgroup J)
  let B₀ := ChapterB.baumann ((T : Subgroup G) ⊓ c.H)
  have hB : B.map J.subtype = B₀ := by
    have hh := Stellmacher.baumann_map_injective
      J.subtype J.subtype_injective (P : Subgroup J)
    rw [hP] at hh
    exact hh
  let e : B ≃* B₀ := (B.equivMapOfInjective J.subtype J.subtype_injective).trans
    (MulEquiv.subgroupCongr hB)
  let A₀ := A.map e.toMonoidHom
  let : A₀.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨(MulAut.congr e.symm a) y,
      characteristic_iff_le_comap.mp hA (MulAut.congr e.symm a) hy,?_⟩
    exact e.apply_symm_apply (a (e y))
  have he : A₀.map B₀.subtype = (A.map B.subtype).map J.subtype := by
    rw [map_map,map_map]
    rfl
  have hK : c.K.map c.H.subtype ≤ normalizer (A₀.map B₀.subtype : Set G) := by
    rw [he]
    have hh := (A.map B.subtype).le_normalizer_map J.subtype
    rw [@normalizer_eq_top _ _ _ hn,←MonoidHom.range_eq_map,range_subtype] at hh
    exact le_sup_left.trans hh
  exact c.no_component_normalized_characteristic_baumann A₀
    (fun hz => hne ((A.map_eq_bot_iff_of_injective e.injective).mp hz)) hK

/-- A whole natural S7 conjugation chart on a normal elementary subgroup of
the actual component--Sylow join reconstructs the original source block.
The kernel remains the literal module centralizer. -/
theorem SourceConfiguration.block_of_natural_seven_join_action
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (U : Subgroup (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G))
    [U.Normal] [IsElementaryAbelian 2 U]
    (q : (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G) →*
      Equiv.Perm (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set _))
    (hKq : ((c.K.map c.H.subtype).subgroupOf
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map q = alternatingGroup (Fin 7))
    (E : Additive U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 7))
    (he : ∀ g u, E (NormalElementaryQuotient.representation U q hq hk g u) =
      BinaryPermutation.naturalRepresentation (Fin 7) g (E u))
    (hm : ⁅U,(c.K.map c.H.subtype).subgroupOf
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))⁆ ≠ ⊥) : ChapterC.IsBlock c.K := by
  let S := (T : Subgroup G) ⊓ c.H
  let J := c.K.map c.H.subtype ⊔ S
  let K := (c.K.map c.H.subtype).subgroupOf J
  have hJH : J ≤ c.H := sup_le (map_subtype_le _) inf_le_right
  have hc : ((c.K.map c.H.subtype).subgroupOf c.H).IsCComponent := by
    have hh : (c.K.map c.H.subtype).subgroupOf c.H = c.K := by
      ext k
      exact mem_map_iff_mem c.H.subtype_injective
    exact hh.symm ▸ c.component
  have hK : K.IsCComponent := hc.subgroupOf_of_le le_sup_left hJH
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (hJH.trans c.normalizer_component.le)
  let e : K ≃* c.K := (subgroupOfEquivOfLe (show c.K.map c.H.subtype ≤ J from le_sup_left)).trans
    (c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective).symm
  let : IsQuasisimple (c.K ⧸ pCore 2 c.K) := c.quotient
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hfK : generalizedFitting K = pCore 2 K := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,hf]
  obtain ⟨P₀,hP₀⟩ := c.sylow
  have hPJ : (P₀ : Subgroup c.H) ≤ J.subgroupOf c.H := by
    intro p hp
    apply (le_sup_right : S ≤ J)
    change (p : G) ∈ (T : Subgroup G) ⊓ c.H
    rw [←hP₀]
    exact mem_map_of_mem c.H.subtype hp
  let P : Sylow 2 J := (P₀.subtype hPJ).mapSurjective
    (f := (subgroupOfEquivOfLe hJH).toMonoidHom) (subgroupOfEquivOfLe hJH).surjective
  have hP : (P : Subgroup J).map J.subtype = S := by
    change (((P₀ : Subgroup c.H).subgroupOf (J.subgroupOf c.H)).map
      (subgroupOfEquivOfLe hJH).toMonoidHom).map J.subtype = _
    rw [map_map]
    change ((P₀ : Subgroup c.H).subgroupOf (J.subgroupOf c.H)).map
      (c.H.subtype.comp (J.subgroupOf c.H).subtype) = _
    rw [←map_map,map_subgroupOf_eq_of_le hPJ,hP₀]
  have hKP : K ⊔ (P : Subgroup J) = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show c.K.map c.H.subtype ≤ J from le_sup_left),
      hP,←MonoidHom.range_eq_map,range_subtype]
  have hprod : ∀ g : J, ∃ k ∈ K, ∃ t ∈ (P : Subgroup J), k*t=g := by
    intro g
    exact mem_sup_of_normal_left.mp (hKP.symm ▸ mem_top g)
  have hfJ : generalizedFitting J = pCore 2 J := by
    have hc := c.component.constrained_join_characteristicTwo
      (P₀.isPGroup') c.c28.oddCore_eq_bot hf
    have hmap : (c.K ⊔ (P₀ : Subgroup c.H)).map c.H.subtype = J := by
      rw [Subgroup.map_sup,hP₀]
    let a : ↥(c.K ⊔ (P₀ : Subgroup c.H)) ≃* J :=
      ((c.K ⊔ (P₀ : Subgroup c.H)).equivMapOfInjective c.H.subtype c.H.subtype_injective).trans
        (MulEquiv.subgroupCongr hmap)
    apply map_injective (f := a.symm.toMonoidHom) a.symm.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso]
    exact generalizedFitting_eq_pCore_of_selfCentralizing 2 hc
  have hcodim : ∀ A, fixedCodim (NormalElementaryQuotient.representation U q hq hk) A =
      fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) A := by
    intro A
    simpa only [map_id] using fixedCodim_map_equivariant
      (NormalElementaryQuotient.representation U q hq hk)
      (BinaryPermutation.naturalRepresentation (Fin 7)) (MonoidHom.id _) E he A
  have he' : ∀ g v, E.symm (BinaryPermutation.naturalRepresentation (Fin 7) g v) =
      NormalElementaryQuotient.representation U q hq hk g (E.symm v) := by
    intro g v
    apply E.injective
    rw [E.apply_symm_apply,he,E.apply_symm_apply]
  have hb : ChapterC.IsBlock K :=
    (ChapterC.RankOne.SevenSource.Natural.normal_characteristic_or_block_of_natural_seven_linear
      K U hK hfJ hfK P hprod q hq hk hKq hcodim E.symm.toLinearMap E.symm.injective he' hm).resolve_left
        (by rintro ⟨A,hA,hne,hn⟩; exact no_join_characteristic_baumann c P hP A hA hne hn)
  exact ⟨inferInstance,ChapterC.RankOne.Solvable.isShort_of_equiv e hb.short,c.component.subnormal⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
