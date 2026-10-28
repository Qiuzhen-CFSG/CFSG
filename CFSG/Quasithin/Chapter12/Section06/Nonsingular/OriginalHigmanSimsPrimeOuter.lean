module

public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupTheory.SolvableOuterQuotient
public import CFSG.Quasithin.ClassicalModels

/-!
# Inner restrictions on the literal A5 in the prime and equality rows

A pointwise fixer of a full Sylow two-subgroup of prime-field PSL₂ is
inner. Every literal A₅ subgroup is self-normalizing: a proper normalizer
is nonsolvable, so Dickson's classification makes it another A₅, and equal
orders force equality. Thus an automorphism preserving that A₅ restricts
to an inner automorphism of the same subgroup. In the equality row the
actual A₅ subgroup has the whole ambient order, and the checked A₅ Sylow
fixer theorem gives the same conclusion.

The actual Sylow, subgroup, normalization equality and automorphism are
retained. No assertion is made about automorphisms that merely preserve a
Sylow setwise. These lemmas close the prime and equality alternatives
against the original HS residual's outer-action witness.

Source: Aschbacher--Smith A.3.14(3), pp.49--50, and 16.1.6, p.1172,
using the proved prime-field Dickson and projective semilinear calculations.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsPrimeOuter
variable {G : Type*} [Group G] [Finite G]

private theorem five_nonsolvable {A : Type*} [Group A]
    (e : A ≃* alternatingGroup (Fin 5)) : ¬ Group.IsSolvable A := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  intro h
  let := h
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5))
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

private theorem prime_five_selfnormalizing {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hl : 3 < p) (B : Subgroup PSL(2, ZMod p))
    (eB : B ≃* alternatingGroup (Fin 5)) : normalizer (B : Set PSL(2, ZMod p)) = B := by
  let : IsSimpleGroup PSL(2, ZMod p) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by simp only [Nat.card_zmod]; omega)
  by_cases ht : B = ⊤
  · subst B
    exact (⊤ : Subgroup PSL(2, ZMod p)).normalizer_eq_top
  have hb : B ≠ ⊥ := by
    intro hh
    have hc : Nat.card B = 60 := by
      rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    simp [hh] at hc
  have hn : normalizer (B : Set PSL(2, ZMod p)) ≠ ⊤ := by
    intro hh
    let : B.Normal := normalizer_eq_top_iff.mp hh
    exact ((inferInstance : B.Normal).eq_bot_or_eq_top).elim hb ht
  have hs : ¬ Group.IsSolvable (normalizer (B : Set PSL(2, ZMod p))) := by
    intro hh
    let := hh
    exact five_nonsolvable eB
      (Group.isSolvable_of_isSolvable_injective (inclusion_injective B.le_normalizer))
  obtain ⟨_,_,⟨eN⟩⟩ := Theory.PSL2.prime_nonsolvable_proper_is_alternating_five
    hp (by simp) (normalizer (B : Set PSL(2, ZMod p))) hn hs
  exact (eq_of_le_of_card_ge B.le_normalizer (by
    rw [Nat.card_congr eB.toEquiv,Nat.card_congr eN.toEquiv])).symm

omit [Finite G] in
private theorem restriction_inner_of_conj_mem (B : Subgroup G) (α : MulAut G)
    (hB : B.map α.toMonoidHom = B) (g : G) (hg : g ∈ B) (he : α = MulAut.conj g) :
    ((α.subgroupMap B).trans (MulEquiv.subgroupCongr hB)) ∈ MulAut.innerSubgroup B := by
  refine ⟨⟨g,hg⟩,?_⟩
  ext x
  change g*(x : G)*g⁻¹ = α x
  rw [he]
  rfl

/-- In the equality row, the pointwise full-Sylow fixer restricts to an
inner automorphism of the actual normalized A₅ subgroup. -/
theorem five_sylow_fixed_restriction_inner
    (eG : G ≃* alternatingGroup (Fin 5)) (P : Sylow 2 G)
    (B : Subgroup G) (eB : B ≃* alternatingGroup (Fin 5))
    (α : MulAut G) (hfix : ∀ x ∈ P, α x = x) (hB : B.map α.toMonoidHom = B) :
    ((α.subgroupMap B).trans (MulEquiv.subgroupCongr hB)) ∈ MulAut.innerSubgroup B := by
  have htop : B = ⊤ := B.eq_top_of_card_eq (by
    rw [Nat.card_congr eB.toEquiv,Nat.card_congr eG.toEquiv])
  obtain ⟨g,_,hg⟩ := Theory.PSL2.SylowFixedQuotients.sylow_fixed_inner_of_equiv_five eG P α hfix
  exact restriction_inner_of_conj_mem B α hB g (htop ▸ mem_top g) hg

/-- In the odd-prime PSL₂ row, a pointwise full-Sylow fixer preserving the
literal A₅ restricts to an inner automorphism of that same subgroup. -/
theorem prime_sylow_fixed_restriction_inner
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hl : 3 < p)
    (hG : ClassicalGroup.IsPSL G 2 p) (P : Sylow 2 G)
    (B : Subgroup G) (eB : B ≃* alternatingGroup (Fin 5))
    (α : MulAut G) (hfix : ∀ x ∈ P, α x = x) (hB : B.map α.toMonoidHom = B) :
    ((α.subgroupMap B).trans (MulEquiv.subgroupCongr hB)) ∈ MulAut.innerSubgroup B := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hG
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let k : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp
    (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  let d := e.trans (Atlas.fieldEquivPSL 2 k)
  let Q := P.mapSurjective (f := d.toMonoidHom) d.surjective
  obtain ⟨g,_,hg⟩ := Theory.PSL2.SylowFixedQuotients.fixed_inner_transport d
    (P : Subgroup G) (Theory.PSL2.primeField_sylow_fixed_inner ho hl Q) α hfix
  have hn : normalizer (B : Set G) = B := by
    apply map_injective (f := d.toMonoidHom) d.injective
    rw [map_equiv_normalizer_eq]
    exact prime_five_selfnormalizing ho hl (B.map d.toMonoidHom)
      ((B.equivMapOfInjective d.toMonoidHom d.injective).symm.trans eB)
  have hgN : g ∈ normalizer (B : Set G) := mem_normalizer_iff_map_conj_eq.mpr (by
    change B.map (MulAut.conj g).toMonoidHom = B
    rw [←hg]
    exact hB)
  exact restriction_inner_of_conj_mem B α hB g (hn ▸ hgN) hg

end CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsPrimeOuter
