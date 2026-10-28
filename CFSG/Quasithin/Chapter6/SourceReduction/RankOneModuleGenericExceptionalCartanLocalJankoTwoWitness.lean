module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoTwoResidual
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.CubicInversion
public import Theory.GroupTheory.CoprimeProductIntersection
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRecognition

/-!
# The complete local Cartan witness in the selected Hall--Janko row

The actual escaping cubic is the full intersection of the original Cartan
with the same normal component C. Intersecting the permuting Cartan--Sylow
product with C makes the original Sylow intersection have index three.
The identified perfect residual has literal two-core quotient PSL₂(4).
The native J₂ section-normalizer calculation and perfect quotient lifting
then invert that specified escaping cubic from the original Sylow.

This supplies every field of LocalCartanWitness. Whole-module recognition
returns degree two and CartanExceptionalConclusion for the unchanged W,
including the genuine component relocated to the whole omega centralizer.
Both Hall conditions and the arbitrary Sylow and module choices are kept.
Exhaustive component selection, the remaining Mathieu witness and binary
triality remain duties of the full source theorem.
Source: Aschbacher--Smith 5.1.13, printed pp.636--638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

/-- The original escaping cubic in the J₂ component is inverted by the
original Sylow intersection, retaining the actual two-core and residual. -/
theorem janko_two_cubic_inverted
    {T : Sylow 2 G} {L W H A B Y D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hRX : residual H ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.J2.Carrier))
    (hfour : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4)
    (hDA : D ≤ A) (hDC : D ≤ C.map Y.subtype) (hD : Nat.card D = 3)
    (hDn : ¬ D ≤ normalizer (residual H : Set G)) :
    ∃ t ∈ (T : Subgroup G) ⊓ C.map Y.subtype,
      ∀ d ∈ D, t*d*t⁻¹=d⁻¹ := by
  let AY := A.subgroupOf Y
  let TY := (T : Subgroup G).subgroupOf Y
  let E := AY.subgroupOf C
  let J := (AY ⊔ TY).subgroupOf C
  have hRC : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRX
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have hEc' := (janko_two_cartan_intersection h hH hgen c hY hescape C hC hRC hm).1
  have he : (AY ⊓ C).map Y.subtype = A ⊓ C.map Y.subtype := by
    change (A.subgroupOf Y ⊓ C).map Y.subtype = _
    rw [Subgroup.map_inf _ _ _ Y.subtype_injective,subgroupOf_map_subtype,inf_assoc,
      inf_eq_right.mpr (map_subtype_le C)]
  have hEc : Nat.card E = 3 := by
    rw [←he,card_map_of_injective Y.subtype_injective] at hEc'
    change Nat.card (AY.subgroupOf C) = 3
    rw [←inf_subgroupOf_right AY C,Nat.card_congr
      (subgroupOfEquivOfLe (show AY ⊓ C ≤ C from inf_le_right)).toEquiv]
    exact hEc'
  have hDY : D ≤ Y := hDC.trans (map_subtype_le C)
  have hDYC : D.subgroupOf Y ≤ C := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hDC hx
    exact (show y=x from Subtype.ext he) ▸ hy
  let DC := (D.subgroupOf Y).subgroupOf C
  have hDCc : Nat.card DC = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDYC).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hDY).toEquiv,hD]
  have hDE : DC ≤ E := fun _ hx => hDA hx
  have hTY := hH.1.1.2.trans hY.2
  let S0 := T.subtype hTY
  obtain ⟨S,hS⟩ := S0.exists_subgroupOf_eq_of_normal C
  have hSJ : (S : Subgroup C) ≤ J := by
    rw [hS]
    exact comap_mono le_sup_right
  have hEc' : Nat.card (AY ⊓ C : Subgroup Y) = 3 := by
    rw [←hEc]
    change Nat.card (AY ⊓ C : Subgroup Y) = Nat.card (AY.subgroupOf C)
    rw [←inf_subgroupOf_right AY C]
    exact (Nat.card_congr (subgroupOfEquivOfLe (show AY ⊓ C ≤ C from inf_le_right)).toEquiv).symm
  have hSc : Nat.card S = Nat.card (TY ⊓ C : Subgroup Y) := by
    rw [hS]
    change Nat.card (TY.subgroupOf C) = _
    rw [←inf_subgroupOf_right TY C]
    exact Nat.card_congr (subgroupOfEquivOfLe (show TY ⊓ C ≤ C from inf_le_right)).toEquiv
  have hoAY : Odd (Nat.card AY) := by
    change Odd (Nat.card (A.subgroupOf Y))
    rw [←inf_subgroupOf_right A Y,Nat.card_congr
      (subgroupOfEquivOfLe (show A ⊓ Y ≤ Y from inf_le_right)).toEquiv]
    exact hoA.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hcop : Nat.Coprime (Nat.card AY) (Nat.card TY) := by
    obtain ⟨k,hk⟩ := S0.isPGroup'.exists_card_eq
    change Nat.card TY = 2 ^ k at hk
    rw [hk]
    exact hoAY.coprime_two_right.pow_right k
  have hperm : (AY : Set Y) * (TY : Set Y) = (TY : Set Y) * (AY : Set Y) := by
    simpa using c.image_intersection_permutes_sylow h.sylow_normalizes hTY (MonoidHom.id Y)
  have hJc : Nat.card J = 3 * Nat.card S := by
    rw [card_subgroupOf_sup_of_coprime_permutable AY TY C hcop hperm,hEc',←hSc]
  let R := ((residual H).subgroupOf Y).subgroupOf C
  have hRY : residual H ≤ Y := hRX.trans (map_subtype_le C)
  have hSR : (S : Subgroup C) ≤ normalizer (R : Set C) := by
    rw [hS,←subgroupOf_normalizer_eq hRC,←subgroupOf_normalizer_eq hRY]
    exact comap_mono (comap_mono (hH.1.1.2.trans (le_normalizer_residual H)))
  let a : (pResidual 2 H) ≃* R := ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
    ((subgroupOfEquivOfLe hRY).symm.trans (subgroupOfEquivOfLe hRC).symm)
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hRcard : Nat.card (R ⧸ pCore 2 R) = 60 := by
    rw [←Nat.card_congr aq.toEquiv]
    obtain ⟨F,_,_,hF,⟨b⟩⟩ := hfour
    obtain ⟨b5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
    rw [Nat.card_congr (b.trans b5).toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  let : Group.IsPerfect (residual H) := residual_perfect h.qtke h.sylow_normalizes hH hgen
  let b : residual H ≃* R := (subgroupOfEquivOfLe hRY).symm.trans (subgroupOfEquivOfLe hRC).symm
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective (f := b.toMonoidHom) b.surjective
  let : Group.IsPerfect C := hC.perfect
  have hDCn : ¬ DC ≤ normalizer (R : Set C) := by
    intro hn
    apply hDn
    rw [←subgroupOf_normalizer_eq hRC,←subgroupOf_normalizer_eq hRY] at hn
    intro d hd
    exact hn (show (⟨⟨d,hDY hd⟩,hDYC hd⟩ : C) ∈ DC from hd)
  obtain ⟨t,ht,hinv⟩ := Sporadic.LeechRelated.J2.escaping_cubic_inverted_above_twoCore
    hm.some S R J DC hSR hSJ (hDE.trans (comap_mono le_sup_left)) hJc hDCc hRcard hDCn
  have htT : (t.val : G) ∈ (T : Subgroup G) := by rw [hS] at ht; exact ht
  refine ⟨t.val,⟨htT,mem_map_of_mem Y.subtype t.property⟩,?_⟩
  intro d hd
  let y : Y := ⟨d,hDY hd⟩
  let x : C := ⟨y,hDYC hd⟩
  exact congrArg (fun z : C => (z.val:G)) (hinv x hd)

/-- The same selected J₂ container supplies the complete original local
witness, including an actual cubic inverted by the original Sylow. -/
theorem janko_two_local_witness
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    ∃ D : Subgroup G, LocalCartanWitness T H A Y (C.map Y.subtype) D := by
  obtain ⟨hKR,hR,_⟩ := normal_janko_two_residual_and_hall
    h hH hgen c hKH hK hqs hKT hKL horbit hY hescape C hC hKC hm
  have hRX : residual H ≤ C.map Y.subtype := hKR ▸ hKC
  have hRC : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRX
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  obtain ⟨D,hDC,hD,hes⟩ := janko_two_escaping_cubic h hH hgen c hY hescape C hC hRC hm
  have hc : (C.map Y.subtype).subgroupOf Y = C :=
    comap_map_eq_self_of_injective Y.subtype_injective C
  let e := C.equivMapOfInjective Y.subtype Y.subtype_injective
  have he : Nonempty (((C.map Y.subtype) ⧸ pCore 2 (C.map Y.subtype)) ≃*
      Sporadic.LeechRelated.J2.Carrier) :=
    ⟨(QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)).trans hm.some⟩
  refine ⟨D,⟨map_subtype_le C,?_,?_,hRX,hR,.inr (.inl he),hDC,hD,hes,?_⟩⟩
  · rw [hc]; exact hC
  · rw [hc]; infer_instance
  · exact janko_two_cubic_inverted h hH hgen c hY hescape C hC hRX hm hR
      (hDC.trans inf_le_left) (hDC.trans inf_le_right) hD hes

/-- The selected J₂ row gives the full source conclusion for the unchanged
whole W, with its genuine relative omega-centralizer component. -/
theorem janko_two_cartan_exceptional
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    n = 2 ∧ CartanExceptionalConclusion T L W H := by
  obtain ⟨D,d⟩ := janko_two_local_witness
    h hH hgen c hKH hK hqs hKT hKL horbit hY hescape C hC hKC hm
  exact localCartan_escape_of_witness h hH hgen c hY d

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
