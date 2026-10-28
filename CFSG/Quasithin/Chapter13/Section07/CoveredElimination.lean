module

public import CFSG.Quasithin.Chapter13.Section07.SourceCover
public import Theory.Alternating.HexEvenQuasisimpleExtension
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.PCoreImage

/-!
# Elimination of the covered nonabelian-span case

The actual quotient action of LT on L/O₂(L) agrees with conjugation by its
realized six-letter permutation. The center preimage lies in H, so the
normal two-core O₂(H) centralizes its image modulo O₂(L). In the nonabelian
V-span case, an element of that two-core induces a transposition. Perfect
central-quotient faithfulness makes the induced automorphism an outer
involution; on the triple cover it inverts the cubic center. Fixedness and
inversion contradict its odd nontrivial order.

Thus a nonabelian V_H forces the original quotient to be ordinary A₆.
Conversely the covered branch has abelian V_H. The final original13.8
consumer fills exactly the missing abelian-span field, preserving every
subgroup and action map in NaturalSetup.
Source: Aschbacher–Smith, 13.7.3(8),13.7.9(2), pp.936,940–941;
GLS3 5.2.7 supplies the proved center inversion.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion NaturalAction
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

noncomputable def source_quotient_action :
    (L ⊔ (T : Subgroup G) : Subgroup G) →* MulAut (L ⧸ pCore 2 L) :=
  (quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp
    (inclusion (sup_le L.le_normalizer d.normalizes_L)))

theorem source_quotient_action_apply (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (l : L) :
    source_quotient_action d x (QuotientGroup.mk' (pCore 2 L) l) =
      QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom
        ⟨x.val, (sup_le L.le_normalizer d.normalizes_L) x.property⟩ l) := by
  exact quotientAut_apply_mk (pCore 2 L) _ l

theorem source_central_action (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    MulAut.centralQuotientAction (source_central_quotient d) (source_quotient_action d x) =
      MulAut.conjNormal (permutation d x) := by
  apply MulEquiv.ext
  intro a
  obtain ⟨b,rfl⟩ := d.local_quotient.surjective a
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) b
  rw [← source_central_quotient_apply d l, MulAut.centralQuotientAction_apply,
    source_quotient_action_apply, source_central_quotient_apply,
    source_central_quotient_apply]
  apply Subtype.ext
  let l' := L.normalizerMonoidHom
    ⟨x.val, (sup_le L.le_normalizer d.normalizes_L) x.property⟩ l
  have he : inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) l' =
      x * inclusion le_sup_left l * x⁻¹ := Subtype.ext rfl
  have hf := congrArg (permutation d) he
  rw [map_mul, map_mul, map_inv, permutation_L, permutation_L] at hf
  exact hf

/-- The local two-core centralizes the actual component-center section. -/
theorem local_core_centralizes_center
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (x : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hx : x.val ∈ Section08.Source.QH H)
    (z : L ⧸ pCore 2 L) (hz : z ∈ center (L ⧸ pCore 2 L)) :
    source_quotient_action d x z = z := by
  let C := (centralCore L).map L.subtype
  let : (centralCore L).Characteristic :=
    inferInstanceAs (centralPreimage (pCore 2 L)).Characteristic
  have hNC : normalizer (L : Set G) ≤ normalizer (C : Set G) :=
    normalizer_le_normalizer_characteristic_image L (centralCore L)
  have hCQ : C ⊓ Section08.Source.QH H ≤ C.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes
      ((pCore_isPGroup.map H.subtype).to_le inf_le_right) inf_le_left
    apply le_trans (le_inf C.le_normalizer ?_) inf_normalizer_le_normalizer_inf
    exact (central_core_le_local d h).trans
      (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
  have hCL : C.pCoreIn 2 ≤ L.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (map_subtype_le _) (L.le_normalizer.trans hNC)
  have hc : ⁅Section08.Source.QH H,C⁆ ≤ L.pCoreIn 2 := by
    apply (le_inf ?_ ?_).trans (hCQ.trans hCL)
    · exact le_normalizer_iff_commutator_le_right.mp
        (h.QH_le_T.trans (d.normalizes_L.trans hNC))
    · exact le_normalizer_iff_commutator_le_left.mp
        ((central_core_le_local d h).trans
          (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := ConjugateIntersections.sourceSetup T L V V₃ V₁ H)))
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
  have hl : l ∈ centralCore L := hz
  let l' := L.normalizerMonoidHom
    ⟨x.val, (sup_le L.le_normalizer d.normalizes_L) x.property⟩ l
  have hm : l' * l⁻¹ ∈ pCore 2 L := by
    have hh := hc (commutator_mem_commutator hx (mem_map_of_mem L.subtype hl))
    obtain ⟨a,ha,he⟩ := hh
    have he' : a = l' * l⁻¹ := Subtype.ext he
    exact he' ▸ ha
  rw [source_quotient_action_apply]
  apply mul_inv_eq_one.mp
  rw [← map_inv, ← map_mul]
  exact (QuotientGroup.eq_one_iff (l' * l⁻¹)).mpr hm

/-- In the nonabelian source branch the covered alternative is impossible;
the original component quotient is ordinary A₆. -/
theorem nonabelian_source_ordinary
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  rcases source_core_quotient_alternatives d with he | hj
  · exact he
  obtain ⟨j⟩ := hj
  exfalso
  let := source_core_quotient_quasisimple d
  obtain ⟨t, ht, hA, _⟩ := nonabelian_transposition_images d h hU hV
  have htm : t ∈ ((Section08.Source.VH H V).subgroupOf (L ⊔ (T : Subgroup G))).map
      (permutation d) := hA.symm ▸ mem_zpowers t
  obtain ⟨x,hx,hxt⟩ := htm
  have hxQ : x.val ∈ Section08.Source.QH H := VH_le_core d h hU hx
  let a := source_quotient_action d x
  have hβ : MulAut.centralQuotientAction (source_central_quotient d) a =
      MulAut.conjNormal t := by rw [source_central_action, hxt]
  have ht2 : t^2 = 1 := by rw [← ht.orderOf]; exact pow_orderOf_eq_one t
  have ha2 : a^2 = 1 := by
    apply MulAut.centralQuotientAction_injective (source_central_quotient d)
    rw [map_pow, map_one, hβ, ← map_pow, ht2, map_one]
  have haout : ∀ c : L ⧸ pCore 2 L, a ≠ MulAut.conj c := by
    intro c hc
    let b := source_central_quotient d (QuotientGroup.mk' (center (L ⧸ pCore 2 L)) c)
    have hb : MulAut.conjNormal t = MulAut.conj b := by
      rw [← hβ, hc, MulAut.centralQuotientAction_conj]
    have htval : t = b.val :=
      GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by decide)
        (hb.trans (MulAut.conjNormal_val (h := b)).symm)
    have hs : Equiv.Perm.sign t = 1 := by
      rw [htval]
      exact (Equiv.Perm.mem_alternatingGroup.mp b.property)
    rw [ht.sign_eq] at hs
    norm_num at hs
  have hinv := Theory.HexEvenExtension.center_inverted_of_hex_model j a ha2 haout
  have hzcard : Nat.card (center (L ⧸ pCore 2 L)) = 3 :=
    (Nat.card_congr (centerCongr j).toEquiv).trans
      Representation.Hexacode.even_center_card
  have hzbot : center (L ⧸ pCore 2 L) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hfix : a z = z := local_core_centralizes_center d h x hxQ z hz
    have hz2 : z^2 = 1 := by
      have he : z = z⁻¹ := hfix.symm.trans (hinv z hz)
      rw [pow_two]
      calc
        z * z = z⁻¹ * z := congrArg (fun w => w*z) he
        _ = 1 := inv_mul_cancel z
    have hz3 : z^3 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨z,hz⟩ : center (L ⧸ pCore 2 L)))
      rw [hzcard] at hh
      exact congrArg Subtype.val hh
    rw [pow_succ, hz2, one_mul] at hz3
    exact hz3
  rw [hzbot, card_bot] at hzcard
  contradiction

/-- The triple-cover branch therefore has abelian full V-span. -/
theorem covered_source_span_abelian
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    IsMulCommutative (Section08.Source.VH H V) := by
  by_contra hV
  obtain ⟨e⟩ := nonabelian_source_ordinary d h hU hV
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hz : center (alternatingGroup (Fin 6)) = ⊥ := by
    exact alternatingGroup.center_eq_bot (by simp)
  have hh := Nat.card_congr (centerCongr e).toEquiv
  rw [hc, hz, card_bot] at hh
  contradiction

/-- Literal13.8 consumer: the covered source branch supplies the missing
abelian-span field of the unchanged local setup. Only the ordinary branch remains. -/
theorem ordinary_or_source_local_setup
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH G₁ V₃)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (LocalSetup T L V V₁ V₂ V₃ M G₁) := by
  rcases source_odd_center_alternatives d with hc | hc
  · exact Or.inl ⟨GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6
      (source_central_quotient d) hc⟩
  · exact Or.inr ⟨d.toLocalSetup (covered_source_span_abelian d h hU hc)⟩

end CFSG.Quasithin.Chapter13.Section07
