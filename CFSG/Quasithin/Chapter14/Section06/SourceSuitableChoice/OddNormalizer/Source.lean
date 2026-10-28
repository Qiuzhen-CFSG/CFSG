module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Support
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Setup
public import Theory.GroupAction.FixedModuloCentralLine
public import CFSG.Quasithin.Chapter14.Section06.SourceMovedModule

/-!
# The literal odd-branch support and its fixed moving vector

For the actual outside subgroup H, the whole moved module equals the
O²(H)-moved module. Odd-order averaging therefore makes each exchanged
summand fixed-free for O²(H). Pulling the first summand back through U_H/Z
provides the support geometry and an N_T(H₁)-fixed moving involution.

These results discharge the support premises used in the first paragraph
of 14.6.17. They do not assert suitability: fitting containment from
14.6.14 and the local normalizer equality from 14.6.16 remain to be proved.
The earlier exchanged-factor setup is explicitly supplied by the original
14.6.12 producer. No maximal-prime choice is needed for the support lemmas;
it is retained separately in `MaximalOddPrime` for 14.6.14--16.

Source: Aschbacher--Smith, 14.6.12 and 14.6.17, printed pp.1031,1035--1036.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
/-- The actual preimage U_{H,1} of [U_H/Z,H₁*]. -/
def firstSupport {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (H1 : Subgroup G) : Subgroup G :=
  supportPreimage a (subspaceCommutator a.representation ⊤ (actorImage H H1))

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))


include hG hempty hM hunique hmany hcard e hab hH

/-- Odd averaging removes all residual-fixed vectors from the first support. -/
theorem source_first_support_fixedFree
    (hodd : Odd (Nat.card (pResidual 2 (H ⧸ pCore 2 H)))) (H1 : Subgroup G) :
    ∀ u ∈ firstSupport a H1,
      (∀ k ∈ residual H, ⁅u,k⁆ ∈ centralInvolutions T) → u ∈ centralInvolutions T := by
  apply supportPreimage_fixedFree a hodd
  rw [← source_rankTwo_whole_moved_eq_residual
    hG T hempty hM hunique hmany hcard e hab H hH a]
  apply Submodule.span_le.mpr
  rintro _ ⟨k,_hk,v,hv,rfl⟩
  exact Submodule.subset_span ⟨k,mem_top _,v,hv,rfl⟩

/-- All support premises except the separate ambient fitting and normalizer
conclusions, derived from the literal exchanged-factor setup. -/
theorem source_exchanged_support_premises
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    let W := firstSupport a H1
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    W ≤ conjugateSpanBy (localModule T M) H ∧ centralInvolutions T < W ∧
      residual H ≤ normalizer (W : Set G) ∧ S ≤ normalizer (W : Set G) ∧
      S.relIndex (T : Subgroup G) = 2 ∧
      (∀ t ∈ (T : Subgroup G), t ∉ S →
        W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralInvolutions T ∧
        residual H ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G)) ∧
      (∀ u ∈ W, (∀ k ∈ residual H, ⁅u,k⁆ ∈ centralInvolutions T) →
        u ∈ centralInvolutions T) := by
  have hn : subspaceCommutator a.representation ⊤ (actorImage H H1) ≠ ⊥ := by
    intro hz
    have hd := d.first_dimension
    rw [hz,finrank_bot] at hd
    omega
  obtain ⟨x,hx,hxN,hex⟩ := d.exchanged
  obtain ⟨hWU,hZW,hKW,hSW,hi,hsep⟩ := exchanged_support_geometry a
    (T : Subgroup G) H0 H1 H2 hH.1.2 d.zero_le (d.first_le.trans d.zero_le)
    (d.second_le.trans d.zero_le) d.index d.normalizes_first d.normalizes_second
    x hx hxN hex hn d.disjoint
  have hodd : Odd (Nat.card (pResidual 2 (H ⧸ pCore 2 H))) := by
    rw [d.residual_card]
    rcases d.prime with hp | hp <;> rw [hp] <;> decide
  exact ⟨hWU,hZW,hKW,hSW,hi,hsep,
    source_first_support_fixedFree hG T hempty hM hunique hmany hcard e hab H hH a hodd H1⟩

/-- Choose the actual N_T(H₁)-fixed moving involution before proving (U3).
The later normalizer theorem is needed to assert that this vector is suitable. -/
theorem source_exists_fixed_moving_in_support
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    ∃ u ∈ firstSupport a H1, u ^ 2 = 1 ∧ u ≠ 1 ∧
      (∀ s ∈ (T : Subgroup G) ⊓ normalizer (H1 : Set G),
        ⁅u,s⁆ ∈ centralInvolutions T) ∧
      ∃ k ∈ residual H, ⁅u,k⁆ ∉ centralInvolutions T := by
  let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
  let W := firstSupport a H1
  obtain ⟨hWU,hZW,_hKW,hSW,_hi,_hsep,hff⟩ := source_exchanged_support_premises
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 d
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWU
  obtain ⟨u,hu,huz,hfix⟩ := Theory.GroupAction.exists_nonidentity_fixed_modulo
    S W (centralInvolutions T) (T.isPGroup'.to_le inf_le_left) hSW
    (inf_le_left.trans (le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T))) hZW
  refine ⟨u,hu,elemPow_eq_one_of_isElementaryAbelian (p := 2) u (hWU hu),
    fun he => huz (he ▸ one_mem _),hfix,?_⟩
  by_contra hn
  push Not at hn
  exact huz (hff u hu hn)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
