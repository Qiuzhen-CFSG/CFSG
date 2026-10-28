module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Quotient

/-!
# The actual max2 central quotient and its outer-image bound

Let H be `localSubgroup` and N its certified seed normal closure. Here the
quotient is N/<t>, for the distinguished involution t viewed inside N; it is
not a quotient by an assumed intrinsic center. The thirteen certified
commutator relations imply that this quotient is abelian. Conjugation by H
fixes t and hence acts on the quotient. Inner automorphisms of N act
trivially, so the image of this action is a quotient of the actual outer
image of H/N. No injectivity of H/N -> Out(N) is used.

Source motivation: GLS3 Table 5.3i, printed p.270, the 2A centralizer entry.
The literal ATLAS words and certified relations are in `Max2Bridge` and
`NormalClosureControl.Certificates.Relations`.
-/

set_option maxRecDepth 4000

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
namespace OuterImageComparison
open NormalClosureControl
open scoped IsMulCommutative

def centralWord : localNormalClosure :=
  ⟨subgroupInvolution, subgroupInvolution_mem_normalClosure⟩

def centralPowers : Subgroup localNormalClosure := Subgroup.zpowers centralWord

theorem centralWord_mem_center : centralWord ∈ Subgroup.center localNormalClosure := by
  rw [Subgroup.mem_center_iff]
  intro z
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp involution_mem_center) z

instance centralPowers_normal : centralPowers.Normal := by
  have hc : centralPowers ≤ Subgroup.center localNormalClosure :=
    Subgroup.zpowers_le.mpr centralWord_mem_center
  exact ⟨fun n hn x => by
    rw [(Subgroup.mem_center_iff.mp (hc hn)) x, mul_inv_cancel_right]
    exact hn⟩

abbrev CentralQuotient := localNormalClosure ⧸ centralPowers

def projection : localNormalClosure →* CentralQuotient := QuotientGroup.mk' centralPowers

def basisElement (i : Fin 13) : localNormalClosure := ⟨basis i, basis_mem_normalClosure i⟩
def quotientBasis (i : Fin 13) : CentralQuotient := projection (basisElement i)

theorem projection_centralWord : projection centralWord = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)

theorem quotientBasis_zero : quotientBasis 0 = 1 := projection_centralWord

theorem basisElement_generate : Subgroup.closure (Set.range basisElement) = ⊤ := by
  apply Subgroup.map_injective localNormalClosure.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hs : localNormalClosure.subtype '' Set.range basisElement = Set.range basis := by
    rw [← Set.range_comp]
    rfl
  rw [hs]
  exact localNormalClosure_eq_span.symm

theorem quotientBasis_generate : Subgroup.closure (Set.range quotientBasis) = ⊤ := by
  have hr : projection.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  rw [← hr, MonoidHom.range_eq_map, ← basisElement_generate, MonoidHom.map_closure]
  congr 1
  exact Set.range_comp projection basisElement

theorem quotientBasis_commute (i j : Fin 13) : Commute (quotientBasis i) (quotientBasis j) := by
  have h := basis_commutator i j
  have h' : basisElement i * basisElement j = basisElement j * basisElement i ∨
      basisElement i * basisElement j = basisElement j * basisElement i * centralWord := by
    rcases h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  change projection (basisElement i) * projection (basisElement j) =
    projection (basisElement j) * projection (basisElement i)
  rcases h' with h | h
  · exact congrArg projection h
  · have hh := congrArg projection h
    simpa only [map_mul, projection_centralWord, mul_one] using hh

instance centralQuotient_commutative : IsMulCommutative CentralQuotient := by
  have h : IsMulCommutative (Subgroup.closure (Set.range quotientBasis)) :=
    Subgroup.isMulCommutative_closure (by
      rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩
      exact (quotientBasis_commute i j).eq)
  refine ⟨⟨fun a b => ?_⟩⟩
  have ha : a ∈ Subgroup.closure (Set.range quotientBasis) := by rw [quotientBasis_generate]; trivial
  have hb : b ∈ Subgroup.closure (Set.range quotientBasis) := by rw [quotientBasis_generate]; trivial
  exact congrArg Subtype.val (mul_comm
    (⟨a, ha⟩ : Subgroup.closure (Set.range quotientBasis)) ⟨b, hb⟩)

theorem inner_projection (n z : localNormalClosure) :
    projection (MulAut.conj n z) = projection z := by
  change projection (n * z * n⁻¹) = projection z
  simp only [map_mul, map_inv, mul_comm (projection n), mul_inv_cancel_right]

theorem action_centralWord (g : localSubgroup) :
    localNormalClosureAction g centralWord = centralWord := by
  apply Subtype.ext
  change g * subgroupInvolution * g⁻¹ = subgroupInvolution
  rw [(Subgroup.mem_center_iff.mp involution_mem_center) g, mul_inv_cancel_right]

theorem action_map_centralPowers (g : localSubgroup) :
    centralPowers.map (localNormalClosureAction g).toMonoidHom = centralPowers := by
  change (Subgroup.zpowers centralWord).map _ = Subgroup.zpowers centralWord
  rw [MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers (action_centralWord g)

def quotientAction : localSubgroup →* MulAut CentralQuotient where
  toFun g := QuotientGroup.congr centralPowers centralPowers
    (localNormalClosureAction g) (action_map_centralPowers g)
  map_one' := by
    apply MulEquiv.ext
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective centralPowers q
    change projection (localNormalClosureAction 1 n) = projection n
    rw [map_one]; rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective centralPowers q
    change projection (localNormalClosureAction (g * h) n) =
      projection (localNormalClosureAction g (localNormalClosureAction h n))
    rw [map_mul]; rfl

theorem quotientAction_projection (g : localSubgroup) (n : localNormalClosure) :
    quotientAction g (projection n) = projection (localNormalClosureAction g n) := rfl

def outerMap : localSubgroup →* MulAut.Outer localNormalClosure :=
  localNormalClosureOuterAction.comp (QuotientGroup.mk' localNormalClosure)

theorem outerMap_ker_le_quotientAction_ker : outerMap.ker ≤ quotientAction.ker := by
  intro g hg
  have hinner : localNormalClosureAction g ∈ MulAut.innerSubgroup localNormalClosure :=
    (QuotientGroup.eq_one_iff _).mp hg
  obtain ⟨n, hn⟩ := hinner
  apply MulEquiv.ext
  intro q
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective centralPowers q
  change projection (localNormalClosureAction g z) = projection z
  rw [← hn]
  exact inner_projection n z

/-- Kernel containment gives a surjection between the actual images. -/
theorem range_card_le_of_ker_le {G A B : Type*} [Group G] [Group A] [Group B]
    [Finite G] (f : G →* A) (k : G →* B) (h : f.ker ≤ k.ker) :
    Nat.card k.range ≤ Nat.card f.range := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let lift : f.range →* k.range := f.rangeRestrict.liftOfSurjective
    f.rangeRestrict_surjective ⟨k.rangeRestrict, by
      intro x hx
      apply Subtype.ext
      exact h (congrArg Subtype.val hx)⟩
  have hl (x : G) : lift (f.rangeRestrict x) = k.rangeRestrict x := by
    simp only [lift, MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply]
  have hs : Function.Surjective lift := by
    intro y
    obtain ⟨x, rfl⟩ := k.rangeRestrict_surjective y
    exact ⟨f.rangeRestrict x, hl x⟩
  exact Nat.card_le_card_of_surjective lift hs

theorem quotientAction_range_card_le_outerAction :
    Nat.card quotientAction.range ≤ Nat.card localNormalClosureOuterAction.range := by
  have h := range_card_le_of_ker_le outerMap quotientAction outerMap_ker_le_quotientAction_ker
  have hr : outerMap.range = localNormalClosureOuterAction.range := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨QuotientGroup.mk' localNormalClosure g, rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective localNormalClosure q
      exact ⟨g, rfl⟩
  rwa [hr] at h

end OuterImageComparison
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
