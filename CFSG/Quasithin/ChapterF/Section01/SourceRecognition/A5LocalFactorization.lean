module
public import CFSG.Quasithin.ChapterF.Section01.SourceIncidence
public import Theory.GroupTheory.NormalSylowQuotientAction.Local
public import Theory.GroupTheory.PCoreQuotientInnerSupplement
public import Theory.SpecificGroups.PSL2.TorusFixedInner
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import GorensteinWalter.PSL2Center
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# A5 local Sylow factorization for F.1.12

For a genuine F.1.1 pair, if a source Borel normalizes the common two-group,
then an A5 local quotient forces the literal factorization
`S = O₂(Lᵢ S)(S ∩ Lᵢ)`. This is obtained from the actual local Sylow,
relative quotient displacements, and the centerless PSL₂(4) quotient; it does
not assume S is Sylow in the ambient generated group.

Consequently `S ≤ Lᵢ` is equivalent to equality of the local two-core with
`O₂(Lᵢ)`. The latter equality is the precise extra conclusion supplied by
the full F.1.12 rank-two recognition; it cannot be inferred from one local
A5 quotient alone. The strictness theorem records this source boundary.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

theorem HypothesisF11.linear_local_sylow_factorization
    (h : HypothesisF11 L S) (i : Fin 2)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : (L i ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (hn : borel (L i) S ≤ normalizer (S : Set G)) :
    S = twoCore (L i ⊔ S) ⊔ (S ⊓ L i) := by
  let K := L i
  obtain ⟨R,hRmap⟩ := h.sylow i
  have hR : (R : Subgroup K) = S.subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hRmap,subgroupOf_map_subtype,inf_comm]
  have hR' : (R : Subgroup K) = (S ⊓ K).subgroupOf K := by
    rw [hR]
    ext x
    change (x:G) ∈ S ↔ (x:G) ∈ S ⊓ K
    exact ⟨fun hx => ⟨hx,x.property⟩, fun hx => hx.1⟩
  have hb : (normalizer (R : Set K)).map K.subtype = borel K S := by
    change (normalizer ((R : Subgroup K) : Set K)).map K.subtype = _
    rw [hR',←subgroupOf_normalizer_eq (show S⊓K≤K from inf_le_right),
      subgroupOf_map_subtype]
    exact inf_comm _ _
  let f : K →* PSL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let a : S → MulAut PSL(2,F) := fun s => MulAut.congr e
    (pCoreJoinAction 2 (h.S_normalizes i) (inclusion le_sup_right s))
  have ha (s : S) (x : K) : a s (f x) =
      f (K.normalizerMonoidHom ⟨s,h.S_normalizes i s.property⟩ x) := by
    change e (pCoreJoinAction 2 (h.S_normalizes i) (inclusion le_sup_right s)
      (e.symm (e (QuotientGroup.mk' (pCore 2 K) x)))) = _
    rw [e.symm_apply_apply,pCoreJoinAction_mk]
    rfl
  obtain ⟨P,hP,hdisp⟩ := NormalSylowQuotientAction.quotient_displacements_of_local_sylow
    S K (h.S_normalizes i) R hR (hb ▸ hn) f
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) a ha
  have hi (s : S) : pCoreJoinAction 2 (h.S_normalizes i) (inclusion le_sup_right s) ∈
      MulAut.innerSubgroup (K ⧸ pCore 2 K) := by
    have hh := Matrix.ProjectiveSpecialLinearGroup.inner_of_normalizer_displacements
      F P (a s) (hdisp s).1 (hdisp s).2
    obtain ⟨b,hb⟩ := hh
    obtain ⟨c,hc⟩ := (MulAut.congr_inner_iff e _).mp ⟨b,hb.symm⟩
    exact ⟨c,hc.symm⟩
  have hc : center (K ⧸ pCore 2 K) = ⊥ := by
    apply bot_unique
    intro z hz
    apply e.injective
    have he : e z ∈ center PSL(2,F) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨x,rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hz x)
    simpa only [GorensteinWalter.psl2_center_eq_bot F,mem_bot,map_one] using he
  have hf := sup_core_factor_of_inner_action K S (h.S_normalizes i) h.S_isP hc R
    (hRmap ▸ inf_le_left) hi
  change S = (R : Subgroup (L i)).map (L i).subtype ⊔ (L i ⊔ S).pCoreIn 2 at hf
  simpa only [hRmap,sup_comm, twoCore,pCoreIn] using hf

theorem HypothesisF11.a5_local_sylow_factorization
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    (hn : borel (L i) S ≤ normalizer (S : Set G)) :
    S = twoCore (L i ⊔ S) ⊔ (S ⊓ L i) := by
  have hc : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  exact h.linear_local_sylow_factorization i (GaloisField 2 2) (e.trans f.symm) hn

theorem HypothesisF11.a5_local_containment_iff_core_eq
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    (hn : borel (L i) S ≤ normalizer (S : Set G)) :
    S ≤ L i ↔ twoCore (L i ⊔ S) = twoCore (L i) := by
  constructor
  · intro hs
    rw [sup_eq_left.mpr hs]
  · intro hc
    rw [h.a5_local_sylow_factorization i e hn,hc]
    exact sup_le (map_subtype_le _) inf_le_right

/-- A missing local containment produces a strict, actual enlargement of
its two-core; inner quotient action alone does not remove this subgroup. -/
theorem HypothesisF11.a5_local_core_lt_of_not_contained
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    (hn : borel (L i) S ≤ normalizer (S : Set G))
    (hout : ¬ S ≤ L i) :
    twoCore (L i) < twoCore (L i ⊔ S) := by
  have hle : twoCore (L i) ≤ twoCore (L i ⊔ S) := by
    apply le_pCoreIn_of_normalizes (pCore_isPGroup.map (L i).subtype)
      ((map_subtype_le _).trans le_sup_left)
    exact (sup_le (L i).le_normalizer (h.S_normalizes i)).trans
      (normalizer_le_normalizer_characteristic_image (L i) (pCore 2 (L i)))
  refine lt_of_le_of_ne hle ?_
  intro he
  exact hout ((h.a5_local_containment_iff_core_eq i e hn).mpr he.symm)

end CFSG.Quasithin.ChapterF.Source
