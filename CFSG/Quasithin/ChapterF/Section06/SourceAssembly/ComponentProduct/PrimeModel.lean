module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentExclusions.Janko
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex
public import GorensteinWalter.SL2UniversalCover
public import GorensteinWalter.PSL2PerfectSubnormal
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import CFSG.Quasithin.ClassicalModels

/-!
# The odd prime-field component in F.6.17

The central projection of the actual component is an isomorphism: its
kernel is a three-group in the original O₃′ quotient, whereas the proved
prime-field covering theorem makes it a two-group. The actual outer group
then has order two by projective-linear automorphism coverage. These facts
supply the inner-action and direct-product argument in F.6.17.

Source: Aschbacher--Smith F.6.17, printed p.309. The prime-field restriction
is supplied by the SQTK refinement in F.6.18, printed p.310.
-/

@[expose] public section
open Subgroup Theory.GroupTheory GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
variable {K : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The literal prime-field outer quotient is a two-group. -/
theorem prime_psl_outer_isTwoGroup (hp : Odd p) (hlarge : 3 < p) :
    IsPGroup 2 (MulAut.Outer PSL(2, ZMod p)) :=
  IsPGroup.of_card (n := 1) (by
    change (MulAut.conj : PSL(2, ZMod p) →* MulAut PSL(2, ZMod p)).range.index = 2 ^ 1
    simpa using Theory.PSL2.prime_card_inner_index (ZMod p) hp hlarge (by simp))

/-- The component's original central projection onto PSL₂(p) is bijective. -/
noncomputable def prime_psl_component_equiv
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (hK : IsComponent G K)
    (hlarge : 3 < p) (j : (K ⧸ center K) ≃* PSL(2, ZMod p)) :
    K ≃* PSL(2, ZMod p) := by
  let : Theory.GroupTheory.IsQuasisimple K := hK.2
  let : Fact (3 < Nat.card (ZMod p)) := ⟨by simpa using hlarge⟩
  let f := PerfectCentralCovering.centralQuotientCover j
  have h3 : IsPGroup 3 f.toMonoidHom.ker := by
    rw [PerfectCentralCovering.centralQuotientCover_ker]
    exact component_center_is_three_group e hK
  have h2 : IsPGroup 2 f.toMonoidHom.ker :=
    PSL2Cover.kernel_isPGroup_of_card_prime (ZMod p) f.toCovering (by simpa using Fact.out (p := p.Prime))
  have hbot : f.toMonoidHom.ker = ⊥ :=
    (disjoint_self.mp (IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ h2 h3))
  exact MulEquiv.ofBijective f.toMonoidHom
    ⟨f.toMonoidHom.ker_eq_bot_iff.mp hbot, f.surjective⟩

/-- The isomorphism is the actual central quotient map followed by the supplied marking. -/
theorem prime_psl_component_equiv_apply
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (hK : IsComponent G K)
    (hlarge : 3 < p) (j : (K ⧸ center K) ≃* PSL(2, ZMod p)) (x : K) :
    prime_psl_component_equiv e hK hlarge j x = j (QuotientGroup.mk x) := rfl

omit [Finite G] in
/-- An arbitrary field of prime cardinality is transported to the prime-field carrier. -/
theorem prime_psl_marking_of_model (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 p) :
    Nonempty ((K ⧸ center K) ≃* PSL(2, ZMod p)) := by
  obtain ⟨F, hfield, hfinite, hcard, ⟨j⟩⟩ := hm
  let : Field F := hfield
  let : Finite F := hfinite
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard)
  exact ⟨j.trans (Atlas.fieldEquivPSL 2 eF)⟩

omit [Finite G] in
/-- The actual simple perfect component quotient excludes the exceptional prime three. -/
theorem prime_psl_component_prime_gt_three
    (hK : IsComponent G K) (hp : Odd p)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 p) : 3 < p := by
  let : Theory.GroupTheory.IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := Theory.GroupTheory.IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center K))
  obtain ⟨j⟩ := prime_psl_marking_of_model hm
  let : IsSimpleGroup PSL(2, ZMod p) := j.symm.isSimpleGroup
  let : Group.IsPerfect PSL(2, ZMod p) := Group.IsPerfect.ofSurjective (f := j.toMonoidHom) j.surjective
  let : Group.IsPerfect (⊤ : Subgroup PSL(2, ZMod p)) :=
    Group.IsPerfect.ofSurjective
      (f := (topEquiv : (⊤ : Subgroup PSL(2, ZMod p)) ≃* _).symm.toMonoidHom)
      (topEquiv : (⊤ : Subgroup PSL(2, ZMod p)) ≃* _).symm.surjective
  have hF : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, hp, by omega, by simp⟩
  have hh := psl2_perfect_subnormal_eq_top (ZMod p) hF ⊤ top_ne_bot
    inferInstance Subgroup.IsSubnormal.top
  simpa using hh.1

/-- Both structural facts used by the actual component product construction. -/
theorem prime_psl_component_center_and_outer
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (hK : IsComponent G K)
    (hp : Odd p) (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 p) :
    center K = ⊥ ∧ IsPGroup 2 (MulAut.Outer K) ∧
      Nonempty (K ≃* PSL(2, ZMod p)) := by
  obtain ⟨j⟩ := prime_psl_marking_of_model hm
  have hlarge := prime_psl_component_prime_gt_three hK hp hm
  let k := prime_psl_component_equiv e hK hlarge j
  exact ⟨center_eq_bot_of_mulEquiv k (psl2_center_eq_bot _),
    (prime_psl_outer_isTwoGroup hp hlarge).of_equiv (MulAut.outerCongr k).symm, ⟨k⟩⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
