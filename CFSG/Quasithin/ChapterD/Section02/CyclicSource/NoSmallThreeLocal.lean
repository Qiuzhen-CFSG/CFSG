module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NineSupport
public import Theory.GroupTheory.Fitting.Core
public import Stellmacher.SectionOne.InvolutionPGroupSmallIndexClassification
/-!
# Local alternatives in the absence of small cubic supports

Apply the faithful small-index classification to [O₃(G),t]. Coprime
commutator idempotence supplies its exact generation hypothesis. Absence
of a cubic plane excludes the support-four case and, through NineSupport,
the elementary-nine case. The remaining local core is cyclic of order
three on a four-space or extraspecial of order twenty-seven on a six-space.
Source application: Aschbacher–Smith D.2.26–29, pp.191–192.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
  [IsElementaryAbelian 2 V] [MulDistribMulAction G V] [FaithfulSMul G V]

theorem threeCore_commutator_alternatives
    (t : G) (ht : IsInvolution t)
    (hm : ⁅pCore 3 G, zpowers t⁆ ≠ ⊥)
    (hindex : Nat.card V ≤ 4 * Nat.card (FixedPoints.subgroup (zpowers t) V))
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Nat.card (commutatorAction X V) ≠ 4) :
    (Nat.card (⁅pCore 3 G, zpowers t⁆ : Subgroup G) = 3 ∧
      Nat.card (commutatorAction (⁅pCore 3 G, zpowers t⁆ : Subgroup G) V) = 16) ∨
    (IsExtraspecial 3 (⁅pCore 3 G, zpowers t⁆ : Subgroup G) ∧
      Nat.card (⁅pCore 3 G, zpowers t⁆ : Subgroup G) = 27 ∧
      Nat.card (commutatorAction (⁅pCore 3 G, zpowers t⁆ : Subgroup G) V) = 64 ∧
      ⁅(center (⁅pCore 3 G, zpowers t⁆ : Subgroup G)).map
        (⁅pCore 3 G, zpowers t⁆ : Subgroup G).subtype, zpowers t⁆ = ⊥) := by
  let F : Subgroup G := ⁅pCore 3 G, zpowers t⁆
  have hFR : F ≤ pCore 3 G := commutator_le_left _ _
  have hF : IsPGroup 3 F := pCore_isPGroup.to_le hFR
  obtain ⟨n,hn⟩ := hF.exists_card_eq
  obtain ⟨m,hmR⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
  have hc : ⁅F,zpowers t⁆ = F := by
    apply Stellmacher.SectionOne.commutator_double_eq_self_of_coprime
    · rw [normalizer_eq_top]
      exact le_top
    · rw [Nat.card_zpowers, orderOf_eq_prime ht.2 ht.1, hmR]
      exact (by decide : Nat.Coprime 2 3).pow_right _
  have hf : fixingSubgroup G (Set.univ : Set V) = ⊥ := by
    apply bot_unique
    intro g hg
    apply eq_of_smul_eq_smul (α := V)
    intro v
    simpa only [one_smul] using ((mem_fixingSubgroup_iff (M := G)).mp hg v trivial)
  have ha := Stellmacher.SectionOne.involutionPGroup_smallIndex_classification_on_commutator
    F hm 3 hF (by rw [hn]; exact (by decide : Nat.Coprime 2 3).pow_right _)
    t ht hc hindex hf
  rcases ha with ⟨hfour,⟨e⟩⟩ | ⟨hs,_,hthree | hfive | hnine⟩ | ⟨hs,_,hcent,hex,hcard⟩
  · have he : Nat.card F = 3 := (Nat.card_congr e.toEquiv).trans (by norm_num)
    exact (hNo F hFR he hfour).elim
  · obtain ⟨e⟩ := hthree
    exact Or.inl ⟨(Nat.card_congr e.toEquiv).trans (by norm_num),hs⟩
  · obtain ⟨e⟩ := hfive
    have he : Nat.card F = 5 := (Nat.card_congr e.toEquiv).trans (by norm_num)
    have hd : 3 ∣ Nat.card F := hF.card_eq_or_dvd.resolve_left (by omega)
    omega
  · obtain ⟨e⟩ := hnine
    let : IsElementaryAbelian 3 (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) :=
      { exponent_dvd_p := by
          rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
          intro x
          ext <;> exact ZModModule.char_nsmul_eq_zero 3 _ }
    let : IsElementaryAbelian 3 F := IsElementaryAbelian.of_injective e.toMonoidHom e.injective
    have he : Nat.card F = 9 := (Nat.card_congr e.toEquiv).trans (by norm_num [Nat.card_prod])
    obtain ⟨X,hXF,hX,hXs⟩ := exists_small_three_support_of_nine (V := V) F he hs
    exact (hNo X (hXF.trans hFR) hX hXs).elim
  · exact Or.inr ⟨hex,hcard,hs,hcent⟩

end CFSG.Quasithin.ChapterD.CyclicSource
