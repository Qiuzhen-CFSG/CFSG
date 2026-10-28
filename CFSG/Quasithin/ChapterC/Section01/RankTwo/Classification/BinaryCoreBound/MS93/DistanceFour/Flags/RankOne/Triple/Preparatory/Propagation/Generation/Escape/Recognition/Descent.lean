module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Escape.RecognitionInputs
public import Theory.GroupAction.SubgroupQuotientCommutatorImage
public import Theory.GroupAction.CardTwoDisplacementInvolution
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# Faithful quotient action and a transvection actor

The actual conjugation action on H/N descends through the marked surjection
onto SL3(2), since its kernel centralizes this quotient. Nontriviality and
simplicity make the descended action faithful. The relative commutator index
is exactly the cyclic displacement order; the small actor therefore has
order-two displacement and is an involution.

This is the action-theoretic reduction for the natural-section inference in
Meierfrankenfeld--Stellmacher (1993), (4.6.8)(2), printed p.906. The splitting
and natural coordinates are established separately.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation
variable {A : Type*} [Group A] [Finite A] {π : A →* SL} {H N : Subgroup A}

/-- Literal quotient conjugation descends faithfully, and the small actor becomes
an involution with displacement of order two. -/
theorem SmallDisplacementData.exists_faithful_action (d : SmallDisplacementData π H N) :
    let := d.normal_kernel
    ∃ ρ : SL →* MulAut (H ⧸ N.subgroupOf H),
      Function.Injective ρ ∧
      (∀ a : A, ∀ h : H,
        ρ (π a) (QuotientGroup.mk' (N.subgroupOf H) h) =
          QuotientGroup.mk' (N.subgroupOf H)
            ⟨a * (h : A) * a⁻¹, d.normal_group.conj_mem _ h.property a⟩) ∧
      ∃ t : SL, t ≠ 1 ∧ t ^ 2 = 1 ∧
        Nat.card (commutatorAction (zpowers (ρ t)) (H ⧸ N.subgroupOf H)) = 2 := by
  let := d.normal_group
  let := d.normal_kernel
  let := d.elementary
  let E := H ⧸ N.subgroupOf H
  have hH : (⊤ : Subgroup A) ≤ normalizer (H : Set A) := by rw [normalizer_eq_top]
  have hN : (⊤ : Subgroup A) ≤ normalizer (N : Set A) := by rw [normalizer_eq_top]
  obtain ⟨τ, hτ⟩ := exists_quotient_conjugation_action ⊤ H N hH hN inferInstance
  let f : (⊤ : Subgroup A) →* SL := π.comp (⊤ : Subgroup A).subtype
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨a, ha⟩ := d.projection_surjective g
    exact ⟨⟨a, mem_top a⟩, ha⟩
  have hk : f.ker ≤ τ.ker :=
    quotient_conjugation_action_kills_commutator_layer ⊤ H N π.ker inferInstance hH
      d.kernel_action τ hτ
  let ρ : SL →* MulAut E := f.liftOfSurjective hf ⟨τ, hk⟩
  have hρ (a : (⊤ : Subgroup A)) : ρ (π a) = τ a :=
    f.liftOfRightInverse_comp_apply _ _ ⟨τ, hk⟩ a
  have hformula (a : A) (h : H) :
      ρ (π a) (QuotientGroup.mk' (N.subgroupOf H) h) =
        QuotientGroup.mk' (N.subgroupOf H)
          ⟨a * (h : A) * a⁻¹, d.normal_group.conj_mem _ h.property a⟩ := by
    rw [hρ ⟨a, mem_top a⟩]
    exact hτ ⟨a, mem_top a⟩ h
  have hinj : Function.Injective ρ := by
    let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
    rcases (inferInstance : ρ.ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact ρ.ker_eq_bot_iff.mp hb
    · have hone : ρ = 1 := MonoidHom.ker_eq_top_iff.mp ht
      exfalso
      apply d.nontrivial_action
      rw [commutator_comm]
      apply commutator_le.mpr
      intro a _ h hh
      have he := hformula a ⟨h, hh⟩
      rw [hone] at he
      have hm := QuotientGroup.eq_iff_div_mem.mp he.symm
      change a * h * a⁻¹ / h ∈ N at hm
      simpa only [commutatorElement_def, div_eq_mul_inv] using hm
  refine ⟨ρ, hinj, hformula, ?_⟩
  obtain ⟨x, hx, hsmall⟩ := d.small_actor
  have hmap : ((zpowers x).subgroupOf (⊤ : Subgroup A)).map τ = zpowers (ρ (π x)) := by
    have he : (zpowers x).subgroupOf (⊤ : Subgroup A) =
        zpowers (⟨x, mem_top x⟩ : (⊤ : Subgroup A)) := by
      ext a
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext hn⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, congrArg Subtype.val hn⟩
    rw [he, τ.map_zpowers, ← hρ]
  have hbound : Nat.card (commutatorAction (zpowers (ρ (π x))) E) ≤ 2 := by
    rw [← hmap, quotient_conjugation_commutatorAction_card ⊤ H N (zpowers x)
      hH le_top inferInstance τ hτ]
    exact hsmall
  have hne : ρ (π x) ≠ 1 := fun he => hx (hinj (he.trans ρ.map_one.symm))
  have htwo : Nat.card (commutatorAction (zpowers (ρ (π x))) E) = 2 := by
    have hpos : 0 < Nat.card (commutatorAction (zpowers (ρ (π x))) E) := Nat.card_pos
    by_contra hc
    have hone : Nat.card (commutatorAction (zpowers (ρ (π x))) E) = 1 := by omega
    have hbot := Subgroup.card_eq_one.mp hone
    apply hne
    ext v
    have hm : v⁻¹ * ρ (π x) v ∈ commutatorAction (zpowers (ρ (π x))) E := by
      rw [commutatorAction_eq_closure]
      exact subset_closure ⟨⟨ρ (π x), mem_zpowers _⟩, v, rfl⟩
    rw [hbot] at hm
    exact (inv_mul_eq_one.mp (mem_bot.mp hm)).symm
  have hi := isInvolution_of_card_two_displacement (ρ (π x)) htwo
  exact ⟨π x, hx, hinj (by rw [map_pow, hi.2, map_one]), htwo⟩
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation
