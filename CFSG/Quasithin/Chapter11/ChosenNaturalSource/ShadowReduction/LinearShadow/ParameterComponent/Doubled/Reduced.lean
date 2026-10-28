module

public import Theory.GroupTheory.ReducedNormal.Equiv
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SylowNormalizerFrattini
/-!
# Reduced modules in the Sylow-centralizer normalizer

Frattini's argument identifies the conjugation quotient of a reduced normal
elementary subgroup in the whole group with its quotient in the normalizer
of its Sylow centralizer. Reducedness is therefore preserved, and the Sylow
centralizer is exactly the local prime core. This is the group-theoretic
input to the doubled F.7.6 setup.

Source: Aschbacher--Smith, 11.3.6, printed p.772.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
omit [Finite G] in
private theorem reduced_restrict {W : Subgroup G} (hW : IsPReduced p W) (N : Subgroup G)
    (hWN : W ≤ N) (hNC : N ⊔ centralizer (W : Set G) = ⊤) :
    IsPReduced p (W.subgroupOf N) := by
  let := hW.normal
  let := hW.elementary
  let W' := W.subgroupOf N
  let C := centralizer (W : Set G)
  let q := QuotientGroup.mk' C
  let f := q.comp N.subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, N.range_subtype]
    have he := congrArg (fun X : Subgroup G => X.map q) hNC
    rw [Subgroup.map_sup, map_top_of_surjective q (QuotientGroup.mk'_surjective C)] at he
    have hc : C.map q = ⊥ := by
      exact (Subgroup.map_eq_bot_iff C).mpr (by rw [QuotientGroup.ker_mk'])
    rwa [hc,sup_bot_eq] at he
  have hk : centralizer (W' : Set N) = f.ker := by
    ext x
    change (∀ y : N, y ∈ W' → y * x = x * y) ↔ q (x : G) = 1
    change (∀ y : N, y ∈ W' → y * x = x * y) ↔ (↑(x : G) : G ⧸ C) = 1
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hx y hy
      exact congrArg Subtype.val (hx ⟨y,hWN hy⟩ hy)
    · intro hx y hy
      exact Subtype.ext (hx (y : G) hy)
  refine ⟨inferInstance, IsElementaryAbelian.subgroupOf hWN, ?_⟩
  let e := (QuotientGroup.quotientMulEquivOfEq hk).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
  rw [pCore_map_iso]
  exact hW.quotient_pCore_eq_bot

/-- The full reduced action survives in the normalizer of the Sylow centralizer;
its centralizer has exactly the local prime core as Sylow subgroup. -/
theorem reduced_normalizer {W : Subgroup G} (hW : IsPReduced p W) (S : Sylow p G) :
    let N := normalizer (((S : Subgroup G) ⊓ centralizer (W : Set G)) : Set G)
    (S : Subgroup G) ≤ N ∧ W ≤ N ∧ IsPReduced p (W.subgroupOf N) ∧
      (S : Subgroup G).subgroupOf N ⊓ centralizer (W.subgroupOf N : Set N) =
        pCore p N := by
  let := hW.normal
  let := hW.elementary
  let C := centralizer (W : Set G)
  let Q := (S : Subgroup G) ⊓ C
  let N := normalizer (Q : Set G)
  have hSN : (S : Subgroup G) ≤ N :=
    (le_inf S.toSubgroup.le_normalizer (le_top.trans_eq C.normalizer_eq_top.symm)).trans
      inf_normalizer_le_normalizer_inf
  have hWS : W ≤ (S : Subgroup G) := (IsElementaryAbelian.isPGroup p W).le_sylow_of_normal S
  have hWQ : W ≤ Q := le_inf hWS W.le_centralizer
  have hWN : W ≤ N := hWQ.trans Q.le_normalizer
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  have hPQ : (P : Subgroup C).map C.subtype = Q := by
    rw [hP,subgroupOf_map_subtype]
  have hNC : N ⊔ C = ⊤ := by
    rw [show N = normalizer (Q : Set G) from rfl,← hPQ]
    exact P.normalizer_sup_eq_top
  have hr := reduced_restrict hW N hWN hNC
  refine ⟨hSN,hWN,hr,?_⟩
  change (S : Subgroup G).subgroupOf N ⊓ centralizer (W.subgroupOf N : Set N) = pCore p N
  apply map_injective N.subtype_injective
  rw [Subgroup.map_inf _ _ _ N.subtype_injective,map_subgroupOf_eq_of_le hSN]
  have he : (centralizer (W.subgroupOf N : Set N)).map N.subtype = N ⊓ C := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,fun w hw => congrArg Subtype.val (ha ⟨w,hWN hw⟩ hw)⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,fun w hw => Subtype.ext (hc w hw),rfl⟩
  rw [he,← inf_assoc,inf_of_le_left hSN]
  change Q = (pCore p N).map N.subtype
  apply le_antisymm
  · have hq : Q.subgroupOf N ≤ pCore p N := by
      let : (Q.subgroupOf N).Normal := normal_in_normalizer
      exact le_sSup ⟨inferInstance,
        (S.isPGroup'.to_le (show Q ≤ S from inf_le_left)).comap_subtype⟩
    have hh := map_mono (f := N.subtype) hq
    rwa [map_subgroupOf_eq_of_le Q.le_normalizer] at hh
  · rintro x ⟨a,ha,rfl⟩
    refine ⟨(pCore_isPGroup.le_sylow_of_normal (S.subtype hSN)) ha,?_⟩
    have hc := le_centralizer_iff.mp hr.le_centralizer_pCore ha
    intro w hw
    exact congrArg Subtype.val (hc ⟨w,hWN hw⟩ hw)

/-- Relative transport to the literal ambient intersection M ∩ N_G(C_T(W)).
Neither centralizer nor normality is replaced by an ambient-normal hypothesis. -/
theorem reduced_normalizer_local (M W : Subgroup G) (T : Sylow p G)
    (hWM : W ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hr : IsPReduced p (W.subgroupOf M)) :
    let A := M ⊓ normalizer (((T : Subgroup G) ⊓ centralizer (W : Set G)) : Set G)
    (T : Subgroup G) ≤ A ∧ W ≤ A ∧ IsPReduced p (W.subgroupOf A) ∧
      (T : Subgroup G).subgroupOf A ⊓ centralizer (W.subgroupOf A : Set A) =
        pCore p A := by
  let P := T.subtype hTM
  let W' := W.subgroupOf M
  let Q := (T : Subgroup G) ⊓ centralizer (W : Set G)
  let Q' := (P : Subgroup M) ⊓ centralizer (W' : Set M)
  let N := normalizer (Q' : Set M)
  let A := M ⊓ normalizer (Q : Set G)
  have hQ : Q' = Q.subgroupOf M := by
    ext x
    constructor
    · rintro ⟨ht,hc⟩
      exact ⟨ht,fun w hw => congrArg Subtype.val (hc ⟨w,hWM hw⟩ hw)⟩
    · rintro ⟨ht,hc⟩
      exact ⟨ht,fun w hw => Subtype.ext (hc w hw)⟩
  have hN : N = (normalizer (Q : Set G)).subgroupOf M := by
    rw [subgroupOf_normalizer_eq (show Q ≤ M from inf_le_left.trans hTM)]
    change normalizer (Q' : Set M) = _
    rw [hQ]
  have hNm (x : M) : x ∈ N ↔ (x : G) ∈ normalizer (Q : Set G) := by
    rw [hN]
    rfl
  let e : N ≃* A :=
    { toFun x := ⟨x.val,⟨x.val.property, (hNm x.val).mp x.property⟩⟩
      invFun x := ⟨⟨x.val,x.property.1⟩,(hNm ⟨x.val,x.property.1⟩).mpr x.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl }
  obtain ⟨hPN,hWN,hrN,hcN⟩ := reduced_normalizer hr P
  have hTA : (T : Subgroup G) ≤ A := fun x hx => ⟨hTM hx,(hNm ⟨x,hTM hx⟩).mp (hPN hx)⟩
  have hWA : W ≤ A := fun x hx => ⟨hWM hx,(hNm ⟨x,hWM hx⟩).mp (hWN hx)⟩
  have heW : (W'.subgroupOf N).map e.toMonoidHom = W.subgroupOf A := by
    ext x
    rw [mem_map_equiv]
    rfl
  have heT : ((P : Subgroup M).subgroupOf N).map e.toMonoidHom =
      (T : Subgroup G).subgroupOf A := by
    ext x
    rw [mem_map_equiv]
    rfl
  have hrA := hrN.map_equiv e
  change IsPReduced p ((W'.subgroupOf N).map e.toMonoidHom) at hrA
  rw [heW] at hrA
  refine ⟨hTA,hWA,hrA,?_⟩
  have he := congrArg (map e.toMonoidHom) hcN
  change (((P : Subgroup M).subgroupOf N ⊓ centralizer (W'.subgroupOf N : Set N)).map
    e.toMonoidHom) = (pCore p N).map e.toMonoidHom at he
  rw [Subgroup.map_inf _ _ _ e.injective,heT,pCore_map_iso,
    map_centralizer_equiv] at he
  have hw : e '' (W'.subgroupOf N : Set N) = (W.subgroupOf A : Set A) :=
    congrArg SetLike.coe heW
  rwa [hw] at he
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
