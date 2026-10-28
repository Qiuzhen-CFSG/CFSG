module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Configuration
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
/-!
# The common crossed-layer obstruction in original 4.3.7

Write S = T ∩ H and embed the intrinsic U(K) through K ≤ H ≤ G.
A nonzero H-invariant subgroup U of S and its crossed copy Uᵗ generate a
nonzero two-subgroup preserved by S and t. If [K,Uᵗ] ≤ U, K preserves this
join too, contradicting the source normalizer control. Two-perfection then
excludes U(K)ᵗ ≤ O₂(KS).

The same maximal-overgroup argument supplies the exact normalizer equality
used in C.6.4(II). Finally, conjugation preserves the literal full module
[Ω₁Z(O₂(LT)),L] and transports a commutator identification with this module.
The chosen Chapter 12 module is never identified with the full module.

These are common reductions for the three block cases. The marked C.4.1
alternatives and their SL₃, Sp₄(4), and A₇ contradictions are still needed
for the complete block exclusion.

Source: Aschbacher–Smith, original 4.3.7, printed pp.615–616;
C.6.2–4, printed pp.166–169.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
private theorem normalizes_join_of_commutators (A U B : Subgroup G)
    (hU : ⁅A,U⁆ ≤ U ⊔ B) (hB : ⁅A,B⁆ ≤ U ⊔ B) :
    A ≤ normalizer ((U ⊔ B : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha x hx
  have hm (D : Subgroup G) (hD : D ≤ U ⊔ B) (hc : ⁅A,D⁆ ≤ U ⊔ B) :
      D.map (MulAut.conj a).toMonoidHom ≤ U ⊔ B := by
    rintro _ ⟨d, hd, rfl⟩
    change a * d * a⁻¹ ∈ U ⊔ B
    have he : a * d * a⁻¹ = ⁅a,d⁆ * d := by simp [commutatorElement_def, mul_assoc]
    rw [he]
    exact (U ⊔ B).mul_mem (hc (commutator_mem_commutator ha hd)) (hD hd)
  have hmap : (U ⊔ B).map (MulAut.conj a).toMonoidHom ≤ U ⊔ B := by
    rw [Subgroup.map_sup]
    exact sup_le (hm U le_sup_left hU) (hm B le_sup_right hB)
  exact hmap (mem_map_of_mem (MulAut.conj a).toMonoidHom hx)

/-- The crossing prevents a nonzero H-normal two-subgroup in S from
absorbing the commutators of its crossed copy with K. -/
theorem SourceConfiguration.crossing_commutator_not_le
    (c : SourceConfiguration T L) {U : Subgroup G}
    (hUS : U ≤ (T : Subgroup G) ⊓ c.H) (hne : U ≠ ⊥)
    (hHU : c.H ≤ normalizer (U : Set G)) :
    ¬ ⁅c.K.map c.H.subtype, U.map (MulAut.conj c.t⁻¹).toMonoidHom⁆ ≤ U := by
  let S : Subgroup G := (T : Subgroup G) ⊓ c.H
  let e := MulAut.conj c.t⁻¹
  let B := U.map e.toMonoidHom
  let A := U ⊔ B
  have hSn : S ≤ normalizer (U : Set G) := inf_le_right.trans hHU
  have hSe : S.map e.toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (S : Set G)).inv_mem c.crossing_normalizes)
  have hBS : B ≤ S := (map_mono (f := e.toMonoidHom) hUS).trans_eq hSe
  have hSnB : S ≤ normalizer (B : Set G) := by
    have hm := (map_mono (f := e.toMonoidHom) hSn).trans (U.le_normalizer_map e.toMonoidHom)
    simpa only [hSe] using hm
  have hSnA : S ≤ normalizer (A : Set G) :=
    (le_inf hSn hSnB).trans (normalizer_inf_normalizer_le_normalizer_sup U B)
  have hee : e.toMonoidHom.comp e.toMonoidHom =
      (MulAut.conj ((c.t ^ 2)⁻¹)).toMonoidHom := by
    ext x
    simp only [e, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      pow_two, mul_inv_rev, inv_inv]
    group
  have hBe : B.map e.toMonoidHom = U := by
    rw [map_map, hee]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (U : Set G)).inv_mem (hSn c.crossing_square))
  have htA : c.t ∈ normalizer (A : Set G) := by
    have hi : c.t⁻¹ ∈ normalizer (A : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      change (U ⊔ B).map e.toMonoidHom = U ⊔ B
      rw [Subgroup.map_sup, hBe]
      exact sup_comm B U
    simpa only [inv_inv] using (normalizer (A : Set G)).inv_mem hi
  intro hc
  have hKnU : c.K.map c.H.subtype ≤ normalizer (U : Set G) :=
    (map_subtype_le _).trans hHU
  have hKnA : c.K.map c.H.subtype ≤ normalizer (A : Set G) :=
    normalizes_join_of_commutators _ U B
      ((le_normalizer_iff_commutator_le_right.mp hKnU).trans le_sup_left)
      (hc.trans le_sup_left)
  have hA : IsPGroup 2 A := T.isPGroup'.to_le ((sup_le hUS hBS).trans inf_le_left)
  have hAne : A ≠ ⊥ := fun hh => hne (bot_unique (hh ▸ (le_sup_left : U ≤ A)))
  exact c.component_outside (hKnA.trans (c.crossing_normalizer_control hA hAne
    (sup_le (c.le_component.trans hKnA) (sup_le hSnA (zpowers_le.mpr htA)))))

/-- The literal U(K), embedded through K ≤ H ≤ G. -/
abbrev SourceConfiguration.blockLayer (c : SourceConfiguration T L) : Subgroup G :=
  ((ChapterC.blockU c.K).map c.K.subtype).map c.H.subtype

omit [Finite G] in
/-- H normalizes the intrinsic characteristic layer of its normal component. -/
theorem SourceConfiguration.blockLayer_normalized (c : SourceConfiguration T L) :
    c.H ≤ normalizer (c.blockLayer : Set G) := by
  exact c.normalizer_component.le.trans
    (normalizer_le_normalizer_characteristic_map c.H.subtype c.H.subtype_injective
      c.K (ChapterC.blockU c.K))

/-- The component layer lies in the literal full Sylow intersection. -/
theorem SourceConfiguration.blockLayer_le_sylow (c : SourceConfiguration T L) :
    c.blockLayer ≤ (T : Subgroup G) ⊓ c.H := by
  obtain ⟨P,hP⟩ := c.sylow
  rw [← hP]
  apply map_mono
  exact ((map_mono ChapterC.blockU_le_core).trans
    (pCoreIn_le_of_subnormal 2 c.component.subnormal)).trans
      (pCore_isPGroup.le_sylow_of_normal P)

/-- The crossed U-layer cannot centralize K modulo U(K). -/
theorem SourceConfiguration.block_crossing_commutator_not_le
    (c : SourceConfiguration T L) (hb : ChapterC.IsBlock c.K) :
    ¬ ⁅c.K.map c.H.subtype,
      c.blockLayer.map (MulAut.conj c.t⁻¹).toMonoidHom⁆ ≤ c.blockLayer := by
  apply c.crossing_commutator_not_le c.blockLayer_le_sylow _ c.blockLayer_normalized
  intro hh
  have hh' : (ChapterC.blockU c.K).map c.K.subtype = ⊥ :=
    (map_injective c.H.subtype_injective) (by simpa only [Subgroup.map_bot] using hh)
  exact hb.short.blockU_ne_bot ((map_injective c.K.subtype_injective)
    (by simpa only [Subgroup.map_bot] using hh'))

/-- The core commutator in the literal join KS lies in U(K). -/
theorem SourceConfiguration.block_core_commutator_le
    (c : SourceConfiguration T L) (hb : ChapterC.IsBlock c.K) :
    ⁅(c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)).pCoreIn 2,
      c.K.map c.H.subtype⁆ ≤ c.blockLayer := by
  let J := c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)
  let Q := J.pCoreIn 2
  have hJH : J ≤ c.H := sup_le (map_subtype_le _) inf_le_right
  have hQH : Q ≤ c.H := (pCoreIn_le 2 J).trans hJH
  have hKnQ : c.K.map c.H.subtype ≤ normalizer (Q : Set G) :=
    (le_sup_left : c.K.map c.H.subtype ≤ J).trans
      (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hKn : c.K ≤ normalizer (Q.subgroupOf c.H : Set c.H) := by
    intro k hk x
    exact hKnQ (mem_map_of_mem c.H.subtype hk) (x : G)
  have hQp : IsPGroup 2 Q := pCore_isPGroup.map J.subtype
  have hc := commutator_le_core_commutator_of_isSubnormal c.K (Q.subgroupOf c.H)
    c.component.subnormal hb.short.twoPerfect hQp.comap_subtype hKn
  have hm := map_mono (f := c.H.subtype) hc
  rw [map_commutator, map_subgroupOf_eq_of_le hQH] at hm
  exact hm

/-- The common first contradiction in 4.3.7: U(K)^t escapes O₂(KS). -/
theorem SourceConfiguration.block_crossing_not_le_core
    (c : SourceConfiguration T L) (hb : ChapterC.IsBlock c.K) :
    ¬ c.blockLayer.map (MulAut.conj c.t⁻¹).toMonoidHom ≤
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)).pCoreIn 2 := by
  intro hc
  apply c.block_crossing_commutator_not_le hb
  rw [commutator_comm]
  exact (commutator_mono hc le_rfl).trans (c.block_core_commutator_le hb)

omit [Finite G] in
/-- The full omega-center commutator module, rather than the originally
chosen module, is invariant under the chosen crossing element. -/
theorem SourceConfiguration.crossing_fullModule {V : Subgroup G}
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V) :
    (Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)).map
      (MulAut.conj c.t⁻¹).toMonoidHom =
        Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  have htL : c.t⁻¹ ∈ normalizer (L : Set G) :=
    D.sylow_normalizes_component ((T : Subgroup G).inv_mem c.crossing_mem)
  have htQ : c.t⁻¹ ∈ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image (L ⊔ (T : Subgroup G))
      (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        ((L ⊔ (T : Subgroup G)).le_normalizer
          (mem_sup_right ((T : Subgroup G).inv_mem c.crossing_mem)))
  have heL : L.map (MulAut.conj c.t⁻¹).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp htL
  have heQ : ((L ⊔ (T : Subgroup G)).pCoreIn 2).map
      (MulAut.conj c.t⁻¹).toMonoidHom = (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp htQ
  rw [Section02.Unitary.fullModule_map,heL,heQ]

/-- The source normalizer calculation used to verify C.6.4(II). -/
theorem SourceConfiguration.sylow_normalizer_eq_of_component_invariant
    (c : SourceConfiguration T L) {A : Subgroup G}
    (hAS : A ≤ (T : Subgroup G) ⊓ c.H) (hne : A ≠ ⊥)
    (hn : c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) ≤
      normalizer (A : Set G)) :
    (T : Subgroup G) ⊓ normalizer (A : Set G) = (T : Subgroup G) ⊓ c.H := by
  let S : Subgroup G := (T : Subgroup G) ⊓ c.H
  let X : Subgroup G := (T : Subgroup G) ⊓ normalizer (A : Set G)
  have hSX : S ≤ X := le_inf inf_le_left (le_sup_right.trans hn)
  apply le_antisymm _ hSX
  by_contra hnot
  have hs : S < X := lt_of_le_of_ne hSX (fun he => hnot he.ge)
  have hu := c.strict_unique X hs inf_le_left
  have hAN := normalizer_le_of_unique_maximalTwoLocal hu.2.2
    (T.isPGroup'.to_le (hAS.trans inf_le_left)) hne
    (sup_le (c.le_component.trans (le_sup_left.trans hn)) inf_le_right)
  exact c.component_outside ((le_sup_left.trans hn).trans hAN)

/-- Intersecting the preceding equality with the actual O₂(LT) gives R,
with precisely the normalizer convention in C.6.4(II). -/
theorem SourceConfiguration.core_normalizer_eq_of_component_invariant
    (c : SourceConfiguration T L) {A : Subgroup G}
    (hAR : A ≤ c.I.pCoreIn 2) (hne : A ≠ ⊥)
    (hn : c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) ≤
      normalizer (A : Set G)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ normalizer (A : Set G) =
      c.I.pCoreIn 2 := by
  have hRT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have he := c.sylow_normalizer_eq_of_component_invariant
    (hAR.trans (c.core_sylow.le.trans inf_le_left)) hne hn
  rw [c.core_sylow, ←he]
  rw [inf_comm ((T : Subgroup G) ⊓ normalizer (A : Set G)), ←inf_assoc,
    inf_eq_left.mpr hRT]

omit [Finite G] in
/-- Transport of the full-module commutator identity to the crossed copy. -/
theorem SourceConfiguration.block_crossing_commutator_fullModule {V : Subgroup G}
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hu : ⁅c.blockLayer,L⁆ =
      Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)) :
    ⁅c.blockLayer.map (MulAut.conj c.t⁻¹).toMonoidHom,L⁆ =
      Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  have htL : L.map (MulAut.conj c.t⁻¹).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp
    (D.sylow_normalizes_component ((T : Subgroup G).inv_mem c.crossing_mem))
  have hm := congrArg (map (MulAut.conj c.t⁻¹).toMonoidHom) hu
  rw [map_commutator,htL,c.crossing_fullModule D] at hm
  exact hm

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
