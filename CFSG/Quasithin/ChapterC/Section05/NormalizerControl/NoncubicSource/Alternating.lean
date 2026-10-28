module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.Quotient
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.LocalFamily
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPair
/-!
# Applying the noncubic source preliminaries to the actual A₅ marking

The preceding alternating setup supplies the elementary module inside T.
Its zero central layer gives the required fixed seed, so the C.5.13 span
and centralizer identities and the actual A₅ quotient need no extra module
or action assumptions. Local-family membership uses the original Sylow.
Source: Aschbacher–Smith C.5.13, printed p.162.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {T K L : Subgroup G}
omit [Finite G] in
private theorem alternating_five_not_three (h : IsAlternatingBlock K 5) :
    ¬ IsAlternatingBlock K 3 := by
  intro h3
  obtain ⟨e5⟩ := h.2.2.quotient_iso
  obtain ⟨e3⟩ := h3.2.2.quotient_iso
  have hc := Nat.card_congr (e5.symm.trans e3).toEquiv
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  have hthree : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  rw [h5,hthree] at hc
  norm_num at hc
/-- The actual alternating C.5.9 marking supplies the complete source span. -/
theorem alternating_five_source_omega_span (h : AlternatingPairSetup T K L)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    IsElementaryAbelian 2 V ∧ V ≤ N ∧ N ≤ normalizer (V : Set G) ∧
      sourceModule K ≤ V ∧ V ≤ T ∧ T ⊓ centralizer (V : Set G) = (K ⊔ T).pCoreIn 2 :=
  source_omega_span_of_noncentral_fixed K T X h.block.2.1 h.twoGroup hTK P hP hA hAX
    (alternating_five_noncentral_fixed K T h.block h.twoGroup (h.module_le.trans inf_le_left) hTK)
/-- The image of the original K in the actual action quotient is A₅. -/
theorem alternating_five_source_block_image (h : AlternatingPairSetup T K L)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := alternating_five_source_omega_span h hTK P hP X hA hAX
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    Nonempty (((K.subgroupOf N).map (QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N)))) ≃*
      alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := source_omega_block_quotient K T X h.block.2.1 h.twoGroup hTK P hP hA hAX
    (alternating_five_noncentral_fixed K T h.block h.twoGroup (h.module_le.trans inf_le_left) hTK)
  obtain ⟨f⟩ := h.block.2.2.quotient_iso
  exact ⟨e.symm.trans f⟩
/-- The original alternating setup supplies the literal L(X₁,T₁) input. -/
theorem alternating_five_source_local_family (h : AlternatingPairSetup T K L)
    (hTK : T ≤ normalizer (K : Set G)) (X : Subgroup G) (hAX : K ⊔ T ≤ X)
    (hX : X ∈ Chapter1.He G) (P : Sylow 2 X) (hP : (P : Subgroup X).map X.subtype = T) :
    K ∈ Chapter1.LIn (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) T :=
  (noncubic_auxiliary_local_family K T X (Or.inr (Or.inr h.block))
    (alternating_five_not_three h.block) hTK hAX hX P hP).1
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
