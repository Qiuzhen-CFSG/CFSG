module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Preparation
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportPermutation
public import Theory.GroupTheory.OddPrimeSectionCentralizers.FactorFamily
public import Theory.GroupTheory.Fitting.PrimeSubgroups

/-!
# Canonical quintic supports in the original action

A cubic-minimum actor that moves the five-core inverts one canonical
four-dimensional quintic support and fixes every other such support.
The original SQTK cover therefore bounds the complete canonical family
by two. Every original starred actor normalizes each support: cyclic
actors have displacement two, while noncyclic actors centralize the
five-core. Both conclusions precede restriction to a moved module.

Source: Aschbacher--Smith D.2.13 and D.2.14, printed pp.184--186,
and 15.1.2, second paragraph, printed p.1084.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal
namespace CFSG.Quasithin.ChapterD
variable {G H V : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Group H] [Finite H] [FiniteDimensional (ZMod 2) V] in
private theorem involution_support_eq (t : G) (ht : orderOf t = 2) :
    subspaceCommutator ρ ⊤ (zpowers t) = LinearMap.range (ρ t - LinearMap.id) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp ha)
    have hi := Finset.mem_range.mp hi
    rw [ht] at hi
    interval_cases i
    · simp
    · exact ⟨v,by simp⟩
  · rintro _ ⟨v,rfl⟩
    exact Submodule.subset_span ⟨t,mem_zpowers t,v,Submodule.mem_top,rfl⟩

omit [Group H] [Finite H] in
theorem fiveSupport_Jhat_le_normalizer (hf : Function.Injective ρ)
    (hq : cubicRatio ρ = 2) :
    let := BinaryGroupAction.action ρ
    ∀ X ∈ smallSupportFactors G (Multiplicative V) 2,
      Jhat ρ ≤ normalizer (X : Set G) := by
  let := BinaryGroupAction.action ρ
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := BinaryGroupAction.faithful ρ hf
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  dsimp only
  intro X hX
  apply sSup_le
  intro A hA
  by_cases hr : rank A = 1
  · obtain ⟨t,ht,he⟩ := CyclicSource.starred_generator ρ hA hr
    rw [←he]
    apply zpowers_le.mpr
    apply smallSupportFactors_normalized_of_displacement_card (Or.inr rfl) t ?_ X hX
    have hd : fixedCodim ρ A = 2 := by
      exact_mod_cast (CyclicSource.starred_codimension ρ hA hr).trans hq
    rw [BinaryGroupAction.commutator_card,involution_support_eq ρ t ht,
      ←fixedCodim_zpowers_eq_displacement_rank,he,hd]
  · have hr' : 1 < rank A := by have := hA.1.2.1.rank_pos; omega
    have hc : ⁅pCore 5 G,A⁆ = ⊥ := by
      by_contra hm
      have := source_lemma_D_2_13_noncyclic_prime ρ hf hA hr' (by decide : Odd 5) hm
      norm_num at this
    have hXP : X ≤ pCore 5 G :=
      IsPGroup.le_pCore_of_le_fitting (IsPGroup.of_card (n := 1) (by simpa using hX.2.1)) hX.1
    exact ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
      (centralizer_le hXP)).trans (Subgroup.centralizer_le_normalizer _)

theorem five_core_canonical_family_bound (hf : Function.Injective ρ)
    (f : H →* G) (honto : Function.Surjective f) (hrank : primeRank 5 H ≤ 2)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hr : rank A = 1)
    (hm : ⁅pCore 5 G,A⁆ ≠ ⊥) :
    let := BinaryGroupAction.action ρ
    Nat.card (smallSupportFactors G (Multiplicative V) 2) ≤ 2 := by
  let := BinaryGroupAction.action ρ
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := BinaryGroupAction.faithful ρ hf
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨hq,hcard,_,hdim,hcompl⟩ := source_lemma_D_2_13_cyclic_five ρ hf hA hr hm
  let D : Subgroup G := ⁅pCore 5 G,A⁆
  have hD : D ∈ smallSupportFactors G (Multiplicative V) 2 := by
    refine ⟨(commutator_le_left _ _).trans (pCore_le_fitting G 5),by simpa using hcard,?_⟩
    rw [BinaryGroupAction.commutator_card,hdim]
  obtain ⟨t,ht,he⟩ := CyclicSource.starred_generator ρ hA hr
  have hti : IsInvolution t := ⟨fun h => by simp [h] at ht,ht ▸ pow_orderOf_eq_one t⟩
  have hsmall : Nat.card (commutatorAction (zpowers t) (Multiplicative V)) = 2 ^ 2 := by
    have hd : fixedCodim ρ A = 2 := by
      exact_mod_cast (CyclicSource.starred_codimension ρ hA hr).trans hq
    rw [BinaryGroupAction.commutator_card,involution_support_eq ρ t ht,
      ←fixedCodim_zpowers_eq_displacement_rank,he,hd]
  have htP : t ∉ centralizer (pCore 5 G : Set G) := by
    intro hc
    apply hm
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    rw [←he]
    exact zpowers_le.mpr hc
  rcases smallSupportFactors_involution_alternative (V := Multiplicative V)
      (Or.inr rfl) t hti hsmall with hfix | ⟨X,hX,_,_,_,hfix⟩
  · have heq : ρ t = ρ 1 := by
      ext v
      obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
        (show v ∈ subspaceCommutator ρ ⊤ D ⊔ fixedSpace ρ (D ⊔ A) from
          by rw [show subspaceCommutator ρ ⊤ D ⊔ fixedSpace ρ (D ⊔ A) = ⊤ from hcompl.sup_eq_top]; trivial)
      have hu' : ρ t u = u := congrArg Multiplicative.toAdd
        ((hfix.1 D hD).2 (Multiplicative.ofAdd u) (by rw [BinaryGroupAction.commutator_eq]; exact hu))
      have hw' : ρ t w = w := hw ⟨t,(show A ≤ D ⊔ A from le_sup_right) (he ▸ mem_zpowers t)⟩
      simp only [map_add,hu',hw',map_one,Module.End.one_apply]
    exact False.elim (hti.1 (hf heq))
  · let I := smallSupportFactors G (Multiplicative V) 2
    let i : I := ⟨X,hX⟩
    have hd := smallSupportFactors_internalDirectProduct (G := G) (V := Multiplicative V)
      (Or.inr rfl)
    apply commuting_pFamily_card_le_two (by decide : Odd 5) f honto hrank
      (pCore 5 G) pCore_isPGroup t ht htP (fun Y : I => Y.val) i
    · intro Y
      exact IsPGroup.of_card (n := 1) (by simpa using Y.property.2.1)
    · intro Y heY
      have hcY := Y.property.2.1
      rw [heY,card_bot] at hcY
      norm_num at hcY
    · exact hd.1.pairwiseDisjoint
    · intro Y Z hne y hy z hz
      exact (hd.2.1 hne y z hy hz).symm.eq
    · intro Y hne y hy z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact ((hfix Y.val Y.property (fun e => hne (Subtype.ext e))).1 y hy).eq

end CFSG.Quasithin.ChapterD
