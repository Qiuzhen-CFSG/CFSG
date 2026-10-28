module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.OrdinaryModule
public import CFSG.Quasithin.Chapter4.Section02.Unitary.OrdinaryAction
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.InnerRadicalNormalizer
public import Theory.SpecificGroups.Janko4.PerfectCoverActions

/-!
# The original ordinary radical and normal residual in the native J₄ quotient

The two-group center of the component lies in its radical intersection.
Quotienting by that actual kernel transports the full normalizer and radicality.
The whole moved module image lies in the image radical's center and has at least
64 elements. Innerness on the perfect cover then makes the original normalized
seed a normal subgroup of the entire native radical normalizer; its quotient by
its full two-core retains the original G₂(2)' marking.

Source: Aschbacher--Smith C.2.1--2, C.3.2--4 and 4.2.12--13, pp.144,
149--150 and 610--612. Native radical coverage remains a separate input to the
terminal exclusion; no coverage premise is introduced in these transports.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- The actual central quotient carries the original radical and whole module
to a nontrivial radical with center of order at least 64. -/
theorem unitary_ordinary_janko_radical
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Janko4.Model) :
    let Dk := (R.subgroupOf H).subgroupOf K
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let P := Dk.map f
    let E := ((V.subgroupOf H).subgroupOf K).map f
    f.ker = center K ∧ f.ker ≤ Dk ∧ IsPRadical 2 P ∧
      (normalizer (Dk : Set K)).map f = normalizer (P : Set Janko4.Model) ∧
      E ≤ (center P).map P.subtype ∧ 64 ≤ Nat.card (center P) := by
  let Dk := (R.subgroupOf H).subgroupOf K
  let U := (V.subgroupOf H).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  let f := e.toMonoidHom.comp q
  let P := Dk.map f
  let E := U.map f
  have hr := h.ordinary_radical_intersection_isRadical K hK
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  have hk : f.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hker : f.ker ≤ Dk := by
    rw [hk, hz]
    exact pCore_le_of_pCore_normalizer_le Dk hr.isPGroup hr.2.le
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hU : U ≤ Dk := subgroupOf_mono K (subgroupOf_mono H
    (h.module_le_center_radical.trans (map_subtype_le _)))
  have hUC : U ≤ centralizer (Dk : Set K) := by
    intro u hu d hd
    obtain ⟨z,hz,hzu⟩ := h.module_le_center_radical hu
    have hc := congrArg R.subtype (mem_center_iff.mp hz ⟨((d : H) : G),hd⟩)
    change (d : G) * (z : G) = (z : G) * (d : G) at hc
    change (z : G) = (u : G) at hzu
    rw [hzu] at hc
    exact Subtype.ext (Subtype.ext hc)
  have hEP : E ≤ (center P).map P.subtype := by
    rintro _ ⟨u,hu,rfl⟩
    refine ⟨⟨f u,mem_map_of_mem f (hU hu)⟩,mem_center_iff.mpr ?_,rfl⟩
    rintro ⟨d,hd⟩
    obtain ⟨v,hv,rfl⟩ := hd
    apply Subtype.ext
    exact (f.map_mul v u).symm.trans
      ((congrArg f (hUC hu v hv)).trans (f.map_mul u v))
  have hE : 64 ≤ Nat.card E := by
    dsimp only [E, f]
    rw [←map_map,card_map_of_injective e.injective]
    exact (h.unitary_ordinary_module_image a K hK).2.2.2.2.1
  have hlarge : 64 ≤ Nat.card (center P) := by
    have hb := card_le_of_le hEP
    rw [card_map_of_injective P.subtype_injective] at hb
    exact hE.trans hb
  have hne : P ≠ ⊥ := by
    intro hbot
    have hb := hlarge.trans (center P).card_le_card_group
    rw [hbot,card_bot] at hb
    omega
  have hc : (normalizer (P : Set Janko4.Model)).pCoreIn 2 = P :=
    map_normalizer_core_of_p_kernel Dk hr.isPGroup hr.2 f hf hker
  have hn : (normalizer (Dk : Set K)).map f = normalizer (P : Set Janko4.Model) := by
    have he : (normalizer (P : Set Janko4.Model)).comap f = normalizer (Dk : Set K) := by
      rw [comap_normalizer_eq_of_surjective _ hf,comap_map_eq_self hker]
    rw [←he,map_comap_eq_self]
    rw [MonoidHom.range_eq_top_of_surjective _ hf]
    exact le_top
  exact ⟨hk,hker,⟨hne,hc⟩,hn,hEP,hlarge⟩

/-- Relative normality of the original seed gives normality in the whole native
radical normalizer, with the full-core unitary quotient marking preserved. -/
theorem unitary_ordinary_janko_normal_residual
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hn : M ≤ normalizer (L : Set G))
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Janko4.Model) :
    let Dk := (R.subgroupOf H).subgroupOf K
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let P := Dk.map f
    let N := normalizer (P : Set Janko4.Model)
    let B := ((L.subgroupOf H).subgroupOf K).map f
    B ≤ N ∧ (B.subgroupOf N).Normal ∧
      Nonempty ((B.subgroupOf N ⧸ pCore 2 (B.subgroupOf N)) ≃*
        commutator (Atlas.G2.Model (ZMod 2))) := by
  let Dk := (R.subgroupOf H).subgroupOf K
  let A := (L.subgroupOf H).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  let f := e.toMonoidHom.comp q
  let P := Dk.map f
  let N := normalizer (P : Set Janko4.Model)
  let B := A.map f
  obtain ⟨_,_,_,hmap,_,_⟩ := h.unitary_ordinary_janko_radical a K hK e
  change (normalizer (Dk : Set K)).map f = N at hmap
  let := hK.2
  have hi (b : MulAut K) : b ∈ MulAut.innerSubgroup K :=
    Janko4.perfect_cover_conj_surjective e b
  have hNK := h.ordinary_radical_normalizer_le_local_of_inner K hK hi
  have hAN : A ≤ normalizer (Dk : Set K) := by
    intro x hx d
    exact h.span_normalizes_radical (le_conjugateSpanBy L M hx) (d : G)
  have hNA : normalizer (Dk : Set K) ≤ normalizer (A : Set K) := by
    intro x hx d
    exact hn (hNK hx) (d : G)
  have hBN : B ≤ N := by
    rw [←hmap]
    exact map_mono hAN
  have hNB : N ≤ normalizer (B : Set Janko4.Model) := by
    rw [←hmap]
    exact (map_mono hNA).trans (A.le_normalizer_map f)
  have hnormal : (B.subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBN).mpr hNB
  obtain ⟨b,_⟩ := h.unitary_ordinary_seed_quotient a K hK
  change (A.map q) ⧸ pCore 2 (A.map q) ≃* commutator (Atlas.G2.Model (ZMod 2)) at b
  let d : A.map q ≃* B :=
    (e.subgroupMap (A.map q)).trans (MulEquiv.subgroupCongr (map_map A e.toMonoidHom q))
  have hdcore : (pCore 2 B).map d.symm.toMonoidHom = pCore 2 (A.map q) :=
    @pCore_map_iso B (A.map q) inferInstance inferInstance 2 d.symm
  let t : B ⧸ pCore 2 B ≃* (A.map q) ⧸ pCore 2 (A.map q) :=
    QuotientGroup.congr (pCore 2 B) (pCore 2 (A.map q)) d.symm hdcore
  let bB : B ⧸ pCore 2 B ≃* commutator (Atlas.G2.Model (ZMod 2)) := t.trans b
  let c : B.subgroupOf N ≃* B := subgroupOfEquivOfLe hBN
  have hccore : (pCore 2 (B.subgroupOf N)).map c.toMonoidHom = pCore 2 B :=
    @pCore_map_iso (B.subgroupOf N) B inferInstance inferInstance 2 c
  let cq : (B.subgroupOf N) ⧸ pCore 2 (B.subgroupOf N) ≃* B ⧸ pCore 2 B :=
    QuotientGroup.congr (pCore 2 (B.subgroupOf N)) (pCore 2 B) c hccore
  exact ⟨hBN,hnormal,⟨cq.trans bB⟩⟩

end CFSG.Quasithin.ChapterC.HypothesisC28
