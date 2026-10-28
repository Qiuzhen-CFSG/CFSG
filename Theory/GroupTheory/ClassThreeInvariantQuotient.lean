module
public import Theory.GroupTheory.InvariantKernelMarkedSurvival

/-!
# The actual class-three invariant-kernel quotient

For the specified Sylow automorphism, a marked third commutator escaping its
conjugacy twist survives the largest invariant ambient-normal kernel. If it
lies in the core's central omega, the central-chief-kernel theorem proves
that the two-residual centralizes the kernel. Characteristic two and unique
Sylow maximality then descend to the literal quotient, which retains class
three and the exact induced automorphism formula.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 6.5, printed p.54.
The existing proof of Lemma 7.3 is reused for quotient structure; it depends
only on the original minimal-parabolic hypotheses and is independent of the
class-three classification.
-/

public section
open Subgroup NilesRankOneKernel Theory.GroupTheory.SubgroupTransport
namespace Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
/-- The induced image automorphism retains its literal formula as well as
its fixed-normal exclusion. -/
theorem quotientImage_noInvariantNormal_formula
    (S : Subgroup H) (β : MulAut S) :
    ∃ γ : MulAut (S.map (QuotientGroup.mk'
        ((invariantNormalKernel S β).map S.subtype))),
      (∀ x : S, γ (((QuotientGroup.mk'
          ((invariantNormalKernel S β).map S.subtype)).subgroupMap S) x) =
        ((QuotientGroup.mk' ((invariantNormalKernel S β).map S.subtype)).subgroupMap S) (β x)) ∧
      NoInvariantNormal (S.map (QuotientGroup.mk'
        ((invariantNormalKernel S β).map S.subtype))) γ := by
  obtain ⟨γ,hγ⟩ := exists_quotientImageAut S β
  refine ⟨γ,hγ,?_⟩
  intro B hB hfix
  let P := S.map (QuotientGroup.mk' ((invariantNormalKernel S β).map S.subtype))
  let L := B.map P.subtype
  let _ := hB
  have hL : L = ⊥ := quotient_normal_eq_bot_of_imageAut_fixed S β γ hγ L
    (map_subtype_le B) (by
      change ((B.map P.subtype).comap P.subtype).map γ.toMonoidHom =
        (B.map P.subtype).comap P.subtype
      rw [comap_map_eq_self_of_injective P.subtype_injective]
      exact hfix)
  exact (B.map_eq_bot_iff_of_injective P.subtype_injective).mp hL

/-- A marked escaping third commutator yields the actual class-three Main
Hypothesis quotient for the specified automorphism, including its exact
induced automorphism formula and its original simple quotient. -/
theorem classThree_main_quotient_of_escape
    (S : Sylow 2 H) (β : MulAut S) (g : H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup (H ⧸ K)]
    (hK : ¬ IsPGroup 2 (H ⧸ K)) (hf : generalizedFitting H = pCore 2 H)
    (Z : Subgroup H) (hZV : Z ≤ omegaCenterIn (pCore 2 H))
    (hclass : ((S : Subgroup H).map (MulAut.conj g).toMonoidHom).lowerCentralSeries 3 = ⊥)
    (hZthird : Z ≤ ((S : Subgroup H).map (MulAut.conj g).toMonoidHom).lowerCentralSeries 2)
    (n : ℕ) (hescape : ¬ (image (β.trans ((MulAut.conj g).subgroupMap (S : Subgroup H))))^[n] Z ≤
      (S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom) :
    let N := (invariantNormalKernel (S : Subgroup H) β).map (S : Subgroup H).subtype
    let q := QuotientGroup.mk' N
    N ≤ pCore 2 H ∧ N ≤ K ∧
      Nonempty (((H ⧸ N) ⧸ K.map q) ≃* (H ⧸ K)) ∧
      generalizedFitting (H ⧸ N) = pCore 2 (H ⧸ N) ∧
      Order.HasUniqueMaximalOver ((S : Subgroup H).map q) ⊤ ∧
      Group.nilpotencyClass (((S : Subgroup H).map (MulAut.conj g).toMonoidHom).map q) = 3 ∧
      ∃ γ : MulAut ((S : Subgroup H).map q),
        (∀ x : S, γ (q.subgroupMap (S : Subgroup H) x) =
          q.subgroupMap (S : Subgroup H) (β x)) ∧
        NoInvariantNormal ((S : Subgroup H).map q) γ := by
  let N := (invariantNormalKernel (S : Subgroup H) β).map (S : Subgroup H).subtype
  let q := QuotientGroup.mk' N
  have hsurvive : ¬ Z ≤ N :=
    not_le_invariantKernel_of_twisted_escape (S : Subgroup H) β g Z n hescape
  have hV : ¬ omegaCenterIn (pCore 2 H) ≤ N := fun h => hsurvive (hZV.trans h)
  obtain ⟨series,hcentral⟩ := invariantKernel_central_chief_of_omega_not_le S hu K hK β hV
  have hNS : N ≤ (S : Subgroup H) := map_subtype_le _
  have hp : IsPGroup 2 N := S.isPGroup'.of_injective (inclusion hNS) (inclusion_injective hNS)
  have hNQ : N ≤ pCore 2 H := le_sSup ⟨inferInstance,hp⟩
  have hQK : pCore 2 H ≤ K := by
    simpa only [QuotientGroup.ker_mk'] using
      MinimalParabolicKernel.core_le_simple_kernel (QuotientGroup.mk' K)
        (QuotientGroup.mk'_surjective K) hK
  have hNK := hNQ.trans hQK
  obtain ⟨hfit,hunique,_⟩ := invariantKernel_quotient_structure S hu hf β
    (residual_le_centralizer_of_central_chief_series N hp series hcentral)
  refine ⟨hNQ,hNK,⟨QuotientGroup.quotientQuotientEquivQuotient N K hNK⟩,
    hfit,hunique,?_,quotientImage_noInvariantNormal_formula (S : Subgroup H) β⟩
  exact nilpotencyClass_image_eq_three_of_surviving_subgroup q _ Z hclass hZthird
    (by simpa only [q,QuotientGroup.ker_mk'] using hsurvive)

end Theory.GroupTheory
