module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalMathieuAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalMathieu
public import Theory.Mathieu.M23.Properties.CubicInversion
public import Theory.GroupTheory.CoprimeProductIntersection
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRecognition

/-!
# The original M₂₃ Cartan witness in the three-group action branch

The lifted cubic is the full original Cartan intersection with the same
selected component. Intersecting the permuting Cartan--Sylow product with
that component makes the original Sylow intersection have index three.
The native M₂₃ Sylow-normalizer theorem, the three-coset quotient and cubic
lifting then give an inverter inside the original Sylow intersection.

The previously identified original residual has literal quotient PSL₂(4).
Together these facts supply every field of LocalCartanWitness. Recognition
returns the whole-module conclusion for the unchanged W and the genuine
component relocated to the omega centralizer. Both Hall conditions and the
arbitrary Sylow and module choices are retained.

The actual Cartan action is assumed to be a three-group, and its order
three is proved. Excluding its other prime divisors, exhaustive component
selection and binary-triality exclusion remain duties of SourceLocalCartanEscape.
Source: Aschbacher--Smith 5.1.13, printed pp.636--638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

/-- The original escaping cubic in the M₂₃ component is inverted by the
original Sylow intersection, retaining the actual two-core and residual. -/
theorem mathieu_twentyThree_cubic_inverted_of_three_action
    {T : Sylow 2 G} {L W H A B Y D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hRX : residual H ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M23))
    (hthree : IsPGroup 3 ((A.subgroupOf Y).map (normalQuotientAction C (pCore 2 C))))
    (hDA : D ≤ A) (hDC : D ≤ C.map Y.subtype) (hD : Nat.card D = 3) :
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
  have hEc' := (mathieu_twentyThree_cartan_intersection_of_three_action h hH hgen c hY hescape C hC hRC hm hthree).1
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
  let f := hm.some.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hf : Function.Surjective f := hm.some.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ hm.some.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨t,ht,hinv⟩ := Sporadic.Mathieu.m23_cubic_inverted_of_two_kernel f hf hk
    S J DC hSJ (hDE.trans (comap_mono le_sup_left)) hJc hDCc
  have htT : (t.val : G) ∈ (T : Subgroup G) := by rw [hS] at ht; exact ht
  refine ⟨t.val,⟨htT,mem_map_of_mem Y.subtype t.property⟩,?_⟩
  intro d hd
  let y : Y := ⟨d,hDY hd⟩
  let x : C := ⟨y,hDYC hd⟩
  exact congrArg (fun z : C => (z.val:G)) (hinv x hd)

/-- The same selected M₂₃ container supplies the complete original local
witness, including an actual cubic inverted by the original Sylow. -/
theorem mathieu_twentyThree_local_witness_of_three_action
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKT : K ⊔ (T : Subgroup G) = H)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M23))
    (hthree : IsPGroup 3 ((A.subgroupOf Y).map (normalQuotientAction C (pCore 2 C)))) :
    ∃ D : Subgroup G, LocalCartanWitness T H A Y (C.map Y.subtype) D := by
  obtain ⟨hKR,hR,_⟩ := normal_mathieu_twentyTwo_twentyThree_residual_and_hall
    h hH hgen c hKL hKT horbit hY hescape C hC hKC (.inr hm)
  have hRX : residual H ≤ C.map Y.subtype := hKR ▸ hKC
  have hRC : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRX
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  obtain ⟨D,hDC,hD,hes⟩ := mathieu_twentyThree_escaping_cubic_of_three_action h hH hgen c hY hescape C hC hRC hm hthree
  have hc : (C.map Y.subtype).subgroupOf Y = C :=
    comap_map_eq_self_of_injective Y.subtype_injective C
  let e := C.equivMapOfInjective Y.subtype Y.subtype_injective
  have he : Nonempty (((C.map Y.subtype) ⧸ pCore 2 (C.map Y.subtype)) ≃*
      Sporadic.Mathieu.M23) :=
    ⟨(QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)).trans hm.some⟩
  refine ⟨D,⟨map_subtype_le C,?_,?_,hRX,hR,.inr (.inr he),hDC,hD,hes,?_⟩⟩
  · rw [hc]; exact hC
  · rw [hc]; infer_instance
  · exact mathieu_twentyThree_cubic_inverted_of_three_action h hH hgen c hY hescape C hC hRX hm hthree
      (hDC.trans inf_le_left) (hDC.trans inf_le_right) hD

/-- The selected M₂₃ row gives the full source conclusion for the unchanged
whole W, with its genuine relative omega-centralizer component. -/
theorem mathieu_twentyThree_cartan_exceptional_of_three_action
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKT : K ⊔ (T : Subgroup G) = H)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M23))
    (hthree : IsPGroup 3 ((A.subgroupOf Y).map (normalQuotientAction C (pCore 2 C)))) :
    n = 2 ∧ CartanExceptionalConclusion T L W H := by
  obtain ⟨D,d⟩ := mathieu_twentyThree_local_witness_of_three_action
    h hH hgen c hKT hKL horbit hY hescape C hC hKC hm hthree
  exact localCartan_escape_of_witness h hH hgen c hY d

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
