module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenFixed
public import Theory.SpecificGroups.Alternating.SevenComponent.Extension
public import Theory.Representation.BinaryPermutation.SevenMarkedAction
public import Theory.Representation.BinaryPermutationMulAction

/-!
# Whole-module coordinates for a normal ordinary A₇ block

The fixed layer vanishes, so the defining deleted permutation module lifts
to the whole U(K). The action on K/O₂(K) extends to the ambient group through
Aut(A₇)=S₇. The trivial commutant of the natural module makes this extension
agree with actual conjugation on U(K). For a two-group quotient G/K its
kernel is exactly O₂(G).

Source: Aschbacher--Smith C.1.13(c), C.4.6 and the A₇ case of 4.3.7,
printed pp.124,152,616.
-/

public noncomputable section
open Subgroup BinaryPermutation BinaryPermutation.SevenMarkedAction
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- Coordinates for the whole module, with the actual ambient action and
its two-core kernel. No transposition or parabolic placement is assumed. -/
theorem IsAlternatingBlock.exists_extension_coordinates (K : Subgroup G) [K.Normal]
    (ha : IsAlternatingBlock K 7) (hG : IsPGroup 2 (G ⧸ K)) :
    ∃ (f : G →* Equiv.Perm (Fin 7))
      (e : (blockU K).map K.subtype ≃* Multiplicative (core (Fin 7))),
      f.ker = pCore 2 G ∧ K.map f = alternatingGroup (Fin 7) ∧
      ∀ (g : G) (v : (blockU K).map K.subtype),
        (e.symm (coreAction (f g) (e v)) : G) = g * (v : G) * g⁻¹ := by
  obtain ⟨ρ, ⟨m⟩, hρ⟩ := ha.2.2
  obtain ⟨f,hf⟩ := alternatingGroup.SevenComponent.exists_extension K m.quotientIso
  let eU := (blockU K).equivMapOfInjective K.subtype K.subtype_injective
  have hq : Function.Bijective (QuotientGroup.mk' (blockFixed K)) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
      rw [QuotientGroup.ker_mk',ha.seven_fixed_eq_bot]),
      QuotientGroup.mk'_surjective _⟩
  let eQ := MulEquiv.ofBijective (QuotientGroup.mk' (blockFixed K)) hq
  let c := (coreEquivNatural (Fin 7) (by decide)).toAddEquiv.toMultiplicative
  let e := eU.symm.trans (eQ.trans (m.moduleIso.trans c.symm))
  have he (k : K) (u : blockU K) :
      e (eU (blockConjugate K k u)) = coreAction (f k) (e (eU u)) := by
    apply c.injective
    change c (c.symm (m.moduleIso (eQ (eU.symm (eU (blockConjugate K k u)))))) = _
    rw [c.apply_symm_apply,eU.symm_apply_apply]
    change m.moduleIso (QuotientGroup.mk' _ (blockConjugate K k u)) = _
    rw [m.intertwining,hf]
    apply Multiplicative.toAdd.injective
    rw [hρ]
    change naturalRepresentation (Fin 7) _ (m.moduleIso (QuotientGroup.mk' _ u)).toAdd =
      coreEquivNatural (Fin 7) (by decide)
        (coreRepresentation (Fin 7) _ (e (eU u)).toAdd)
    rw [coreEquivNatural_equivariant]
    congr 1
    change _ = (c (c.symm (m.moduleIso (eQ (eU.symm (eU u)))))).toAdd
    rw [c.apply_symm_apply,eU.symm_apply_apply]
    rfl
  have himage : K.map f = alternatingGroup (Fin 7) := by
    apply le_antisymm
    · rintro _ ⟨k,hk,rfl⟩
      rw [hf ⟨k,hk⟩]
      exact (m.quotientIso (QuotientGroup.mk' _ ⟨k,hk⟩)).property
    · intro a ha
      obtain ⟨q,hq⟩ := m.quotientIso.surjective ⟨a,ha⟩
      obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) q
      exact ⟨k,k.property,(hf k).trans (congrArg Subtype.val hq)⟩
  let U := (blockU K).map K.subtype
  have hn : (⊤ : Subgroup G) ≤ normalizer (U : Set G) := by
    exact (show (⊤ : Subgroup G) ≤ normalizer (K : Set G) by
      rw [normalizer_eq_top]).trans
        (normalizer_le_normalizer_characteristic_image K (blockU K))
  let a : G →* MulAut U := U.normalizerMonoidHom.comp
    ((MonoidHom.id G).codRestrict (normalizer (U : Set G)) (fun g => hn (mem_top g)))
  let α := (MulAut.congr e).toMonoidHom.comp a
  have hα : ∀ k : K, α k = coreAction (f k) := by
    intro k
    apply MulEquiv.ext
    intro v
    let u := eU.symm (e.symm v)
    have hu : eU u = e.symm v := eU.apply_symm_apply _
    have hh := he k u
    rw [hu,e.apply_symm_apply] at hh
    change e (a k (e.symm v)) = _
    rw [← hh]
    apply congrArg e
    apply Subtype.ext
    change (k : G) * (e.symm v : G) * (k : G)⁻¹ =
      (k : G) * (((u : blockU K) : K) : G) * (k : G)⁻¹
    rw [← congrArg Subtype.val hu]
    rfl
  have hαeq := extension_eq K f himage α hα
  refine ⟨f,e,alternatingGroup.SevenComponent.extension_kernel_eq_twoCore
    K m.quotientIso hG f hf,himage,?_⟩
  intro g v
  have hh := DFunLike.congr_fun (DFunLike.congr_fun hαeq g) (e v)
  change e (a g (e.symm (e v))) = coreAction (f g) (e v) at hh
  rw [e.symm_apply_apply] at hh
  rw [← hh,e.symm_apply_apply]
  rfl

end CFSG.Quasithin.ChapterC
