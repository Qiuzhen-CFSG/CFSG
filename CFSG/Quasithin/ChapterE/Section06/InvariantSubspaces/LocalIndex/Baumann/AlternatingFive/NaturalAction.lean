module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.Action
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction.FixedKernel
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.Reduction
public import Theory.Representation.BinaryAlternatingFiveNormalizer
public import Theory.Representation.BinaryPermutationMulAction

/-!
# Constructing the actual natural action of an alternating-five block

The block definition identifies U/C_U(L). Projectivity of the natural A₅ module
kills its fixed kernel, so we lift these coordinates to the actual embedded U.
Transporting H-conjugation then gives automorphisms normalizing the concrete A₅
action. That normalizer is contained in the natural S₅ action, and faithfulness
supplies a unique permutation
for each element of H, and these permutations form a homomorphism. Its kernel
is the literal C_H(U), so the supplied centralizer theorem identifies it with
O₂(H). The image of L is exactly A₅, and every action formula is literal.

The conditional assembly lemmas isolate these two representation facts;
`naturalActionInput` discharges both using their independently proved results.
The possible central extension in O₂(L) is retained, and the image of H is
permitted to be a proper subgroup of S₅.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.13(c),
printed pp.124–125/PDF pp.135–136; C.5.4(3), printed p.155/PDF p.166;
I.1.6(1), printed p.408/PDF p.419.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive
open Subgroup BinaryPermutation
universe u
variable {G : Type u} [Group G] {H L : Subgroup G}

/-- Removing the fixed kernel identifies the actual embedded U with the defining model. -/
theorem exists_lifted_block_action
    (hL : ChapterC.IsAlternatingBlock L 5) (hf : ChapterC.blockFixed L = ⊥) :
    ∃ (a : L →* alternatingGroup (Fin 5))
      (e : U L ≃* Multiplicative (natural (Fin 5))),
      Function.Surjective a ∧ ∀ (l : L) (v : U L),
        (e.symm (naturalMulAction (Fin 5) (a l).val (e v)) : G) =
          (l : G) * (v : G) * (l : G)⁻¹ := by
  obtain ⟨ρ, ⟨m⟩, hρ⟩ := hL.2.2
  let a := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have ha : Function.Surjective a :=
    m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  let eU : ChapterC.blockU L ≃* U L :=
    (ChapterC.blockU L).equivMapOfInjective L.subtype L.subtype_injective
  have hq : Function.Bijective (QuotientGroup.mk' (ChapterC.blockFixed L)) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hf]),
      QuotientGroup.mk'_surjective _⟩
  let eQ := MulEquiv.ofBijective (QuotientGroup.mk' (ChapterC.blockFixed L)) hq
  let e := eU.symm.trans (eQ.trans m.moduleIso)
  refine ⟨a, e, ha, ?_⟩
  intro l v
  have hv : (((eU.symm v : ChapterC.blockU L) : L) : G) = v :=
    congrArg Subtype.val (eU.apply_symm_apply v)
  have he : e (eU (ChapterC.blockConjugate L l (eU.symm v))) =
      naturalMulAction (Fin 5) (a l).val (e v) := by
    change m.moduleIso (eQ (eU.symm (eU (ChapterC.blockConjugate L l (eU.symm v))))) = _
    rw [eU.symm_apply_apply]
    change m.moduleIso (QuotientGroup.mk' _ (ChapterC.blockConjugate L l (eU.symm v))) = _
    rw [m.intertwining]
    apply Multiplicative.toAdd.injective
    exact hρ (a l) (e v)
  rw [← he, e.symm_apply_apply]
  change (l : G) * (((eU.symm v : ChapterC.blockU L) : L) : G) * (l : G)⁻¹ = _
  rw [hv]

/-- Transport actual conjugation by H to the coordinates on U.
The body is exposed to retain the literal conjugation formula. -/
@[expose] noncomputable def transportedAction (hn : H ≤ normalizer (U L : Set G))
    (e : U L ≃* Multiplicative (natural (Fin 5))) :
    H →* MulAut (Multiplicative (natural (Fin 5))) :=
  (MulAut.congr e).toMonoidHom.comp
    ((U L).normalizerMonoidHom.comp (Subgroup.inclusion hn))

@[simp] theorem transportedAction_apply (hn : H ≤ normalizer (U L : Set G))
    (e : U L ≃* Multiplicative (natural (Fin 5))) (x : H)
    (v : Multiplicative (natural (Fin 5))) :
    transportedAction hn e x v = e
      ⟨(x : G) * (e.symm v : G) * (x : G)⁻¹,
        (mem_normalizer_iff.mp (hn x.property) _).mp (e.symm v).property⟩ := rfl

/-- The transported action has precisely the literal centralizer as kernel. -/
theorem transportedAction_ker (hn : H ≤ normalizer (U L : Set G))
    (e : U L ≃* Multiplicative (natural (Fin 5))) :
    (transportedAction hn e).ker = (centralizer (U L : Set G)).subgroupOf H := by
  ext x
  change transportedAction hn e x = 1 ↔ (x : G) ∈ centralizer (U L : Set G)
  rw [mem_centralizer_iff]
  constructor
  · intro hx v hv
    have hh := DFunLike.congr_fun hx (e ⟨v, hv⟩)
    have he := e.injective hh
    have hc := congrArg Subtype.val he
    change (x : G) * (e.symm (e ⟨v, hv⟩) : G) * (x : G)⁻¹ = _ at hc
    rw [e.symm_apply_apply] at hc
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  · intro hx
    apply MulEquiv.ext
    intro v
    change e ⟨_, _⟩ = v
    apply e.symm.injective
    rw [e.symm_apply_apply]
    apply Subtype.ext
    change (x : G) * (e.symm v : G) * (x : G)⁻¹ = (e.symm v : G)
    rw [← hx _ (e.symm v).property, mul_inv_cancel_right]

/-- The lifted L coordinates identify its entire action image. -/
theorem transportedAction_block_image
    (hn : H ≤ normalizer (U L : Set G)) (hLH : L ≤ H)
    (a : L →* alternatingGroup (Fin 5)) (ha : Function.Surjective a)
    (e : U L ≃* Multiplicative (natural (Fin 5)))
    (he : ∀ (l : L) (v : U L),
      (e.symm (naturalMulAction (Fin 5) (a l).val (e v)) : G) =
        (l : G) * (v : G) * (l : G)⁻¹) :
    (L.subgroupOf H).map (transportedAction hn e) =
      (alternatingGroup (Fin 5)).map (naturalMulAction (Fin 5)) := by
  have hh (l : L) : transportedAction hn e (inclusion hLH l) =
      naturalMulAction (Fin 5) (a l).val := by
    apply MulEquiv.ext
    intro v
    apply e.symm.injective
    apply Subtype.ext
    change (e.symm (e ⟨_, _⟩) : G) = _
    rw [e.symm_apply_apply]
    exact (he l (e.symm v)).symm.trans (by rw [e.apply_symm_apply])
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    let l : L := ⟨x, hx⟩
    have hx' : inclusion hLH l = x := Subtype.ext rfl
    rw [← hx', hh]
    exact mem_map_of_mem _ (a l).property
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨l, hl⟩ := ha ⟨g, hg⟩
    refine ⟨inclusion hLH l, l.property, ?_⟩
    rw [hh, hl]

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive
open Subgroup BinaryPermutation
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {A H R L : Subgroup G}

/-- The two independent representation facts suffice for the full H action. -/
theorem naturalActionModel_of_fixedKernel_and_normalizer
    (hnormalizer : normalizer
        ((alternatingGroup (Fin 5)).map (naturalMulAction (Fin 5)) :
          Set (MulAut (Multiplicative (natural (Fin 5))))) ≤
      (naturalMulAction (Fin 5)).range)
    (h : Configuration K A H R L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H)
    (hL : ChapterC.IsAlternatingBlock L 5)
    (hfixed : ChapterC.blockFixed L = ⊥) : Nonempty (NaturalActionModel H L) := by
  have hfaithful := naturalMulAction_injective_of_odd (Fin 5) (by decide)
  obtain ⟨a, e, ha, he⟩ := exists_lifted_block_action hL hfixed
  let hn := normalizes_module h
  let ρ := transportedAction hn e
  have hLH : L ≤ H := h.join_eq ▸ le_sup_left
  have himage : (L.subgroupOf H).map ρ =
      (alternatingGroup (Fin 5)).map (naturalMulAction (Fin 5)) :=
    transportedAction_block_image hn hLH a ha e he
  let : (L.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer h.normalizes_L
  have hr : ρ.range ≤ normalizer ((L.subgroupOf H).map ρ : Set _) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map] using
      (L.subgroupOf H).le_normalizer_map ρ
  rw [himage] at hr
  have hp (x : H) : ρ x ∈ (naturalMulAction (Fin 5)).range :=
    hnormalizer (hr ⟨x, rfl⟩)
  let q : H →* Equiv.Perm (Fin 5) :=
    (MonoidHom.ofInjective hfaithful).symm.toMonoidHom.comp (ρ.codRestrict _ hp)
  have hq (x : H) : naturalMulAction (Fin 5) (q x) = ρ x :=
    MonoidHom.apply_ofInjective_symm hfaithful ⟨ρ x, hp x⟩
  have hcomp : (naturalMulAction (Fin 5)).comp q = ρ := MonoidHom.ext hq
  have hk : q.ker = ρ.ker := by
    ext x
    change q x = 1 ↔ ρ x = 1
    rw [← hq, ← (naturalMulAction (Fin 5)).map_one, hfaithful.eq_iff]
  have hc' : (centralizer (U L : Set G)).subgroupOf H = pCore 2 H := by
    apply map_injective H.subtype_injective
    rw [subgroupOf_map_subtype, inf_comm, hc]
    rfl
  refine ⟨⟨q, ?_, ?_, e, ?_⟩⟩
  · rw [hk, transportedAction_ker, hc']
  · apply map_injective hfaithful
    rw [map_map, hcomp, himage]
  · intro x v
    change (e.symm (naturalMulAction (Fin 5) (q x) (e v)) : G) = _
    rw [hq]
    change (e.symm (e ⟨_, _⟩) : G) = _
    rw [e.symm_apply_apply]
    change (x : G) * (e.symm (e v) : G) * (x : G)⁻¹ = _
    rw [e.symm_apply_apply]

/-- Final assembly with the fixed-kernel and concrete normalizer obligations explicit. -/
theorem naturalActionInput_of_fixedKernel_and_normalizer
    (hnormalizer : normalizer
        ((alternatingGroup (Fin 5)).map (naturalMulAction (Fin 5)) :
          Set (MulAut (Multiplicative (natural (Fin 5))))) ≤
      (naturalMulAction (Fin 5)).range)
    (hfixed : ∀ L : Subgroup G, ChapterC.IsAlternatingBlock L 5 →
      ChapterC.blockFixed L = ⊥) : NaturalActionInput (G := G) K := by
  intro A H R L h hc hL
  exact naturalActionModel_of_fixedKernel_and_normalizer hnormalizer
    h hc hL (hfixed L hL)

/-- The original local configuration and centralizer equality give the actual
natural H-action on U, with kernel O₂(H) and alternating image of L. -/
theorem naturalActionInput : NaturalActionInput (G := G) K :=
  naturalActionInput_of_fixedKernel_and_normalizer
    normalizer_alternatingFive_naturalMulAction_le_range
    (fun _ hL => hL.blockFixed_eq_bot)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive

end
