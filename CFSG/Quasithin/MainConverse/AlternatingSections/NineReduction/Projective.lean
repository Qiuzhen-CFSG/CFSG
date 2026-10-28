module

public import CFSG.Quasithin.MainConverse.SolvableSections
public import Stellmacher.Recognition.ConversePSL2Binary
public import Theory.GroupTheory.SimpleSectionSolvableReduction

/-!
# The projective degree-nine section branch

Source obligation: Aschbacher–Smith, Theorem 0.1.2(3), condition K,
printed pp.4 and 482. The primitive A₉ calculation needs PSL₂(8) and its
outer extensions. Here the existing binary minimal-simple theorem, proved
from Dickson's subgroup theorem, shows that proper subgroups of PSL₂(8)
are solvable. A nontrivial simple quotient of the whole group is isomorphic
to it. Its carrier is definitionally the projective special linear group
used in `ClassicalGroup.IsPSL`, so the catalogue witness uses that actual
model over `GaloisField 2 3`.

An outer extension is handled by an actual normal subgroup and its actual
solvable quotient. These section lemmas do not assert that a primitive
subgroup of A₉ has that structure; the exhaustive primitive classification
is a separate obligation of the degree-nine assembly.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction

open CFSG.KnownSimple BenderSuzuki.MatrixGroups

universe u

/-- Simple sections of PSL₂(8) are prime cyclic or isomorphic to the actual PSL₂(8) carrier. -/
public theorem pslTwoEight_simple_section {H S : Type*} [Group H] [Group S] [IsSimpleGroup S]
    (e : H ≃* PSL2MatrixGroup (GaloisField 2 3))
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    IsPrimeCyclicCarrier S ∨ Nonempty (S ≃* PSL2MatrixGroup (GaloisField 2 3)) := by
  let : Finite H := Finite.of_injective e e.injective
  have hm : IsMinimalSimple H :=
    (Stellmacher.Recognition.isMinimalSimple_psl2_binary (by decide : Nat.Prime 3)).of_mulEquiv e.symm
  by_cases hU : U = ⊤
  · subst U
    let : IsSimpleGroup H := hm.isSimpleGroup
    let : IsSimpleGroup (⊤ : Subgroup H) := Subgroup.topEquiv.isSimpleGroup
    exact .inr ⟨(MulEquiv.ofBijective f
      ⟨f.injective_of_surjective_of_simple hf, hf⟩).symm.trans (Subgroup.topEquiv.trans e)⟩
  · let : Group.IsSolvable U := hm.solvable_of_lt U (lt_top_iff_ne_top.mpr hU)
    let : Group.IsSolvable S := Group.isSolvable_of_surjective hf
    exact .inl (primeCyclic_of_solvable_simple S)

/-- The projective alternative is in the classical catalogue with parameters `(2, 8)`. -/
public theorem pslTwoEight_simple_section_constructed {H S : Type*}
    [Group H] [Group S] [IsSimpleGroup S]
    (e : H ≃* PSL2MatrixGroup (GaloisField 2 3))
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  rcases pslTwoEight_simple_section e U f hf with hs | es
  · exact .cyclic hs
  · apply IsConstructedCarrier.classical
    apply IsClassicalModel.linear 2 8
    · refine ⟨?_, by decide, by decide⟩
      exact (isPrimePow_nat_iff 8).mpr ⟨2, 3, by decide, by decide, by decide⟩
    · exact ⟨GaloisField 2 3, inferInstance, inferInstance,
        (GaloisField.card 2 3 (by decide)).trans (by decide), es⟩

/-- A solvable outer quotient adds only prime-cyclic simple sections to PSL₂(8). -/
public theorem normal_pslTwoEight_simple_section_constructed {H S : Type*}
    [Group H] [Group S] [IsSimpleGroup S]
    (N : Subgroup H) [N.Normal]
    (e : N ≃* PSL2MatrixGroup (GaloisField 2 3)) [Group.IsSolvable (H ⧸ N)]
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  rcases Subgroup.simple_section_normal_or_quotient N U f hf with
    ⟨W, g, hg⟩ | ⟨W, g, hg⟩
  · exact pslTwoEight_simple_section_constructed e W g hg
  · let : Group.IsSolvable S := Group.isSolvable_of_surjective hg
    exact .cyclic (primeCyclic_of_solvable_simple S)

/-- All simple sections of any actual copy of PSL₂(8) lie in the catalogue. -/
public theorem pslTwoEight_isKGroup_constructed {H : Type u} [Group H]
    (e : H ≃* PSL2MatrixGroup (GaloisField 2 3)) : IsKGroup IsConstructedCarrier H := by
  intro S _ hS U f hf
  let := hS
  exact pslTwoEight_simple_section_constructed e U f hf

/-- Extension closure for an actual normal PSL₂(8) and a solvable quotient. -/
public theorem isKGroup_of_normal_pslTwoEight {H : Type u} [Group H]
    (N : Subgroup H) [N.Normal]
    (e : N ≃* PSL2MatrixGroup (GaloisField 2 3)) [Group.IsSolvable (H ⧸ N)] :
    IsKGroup IsConstructedCarrier H :=
  IsKGroup.of_normal_quotient N (pslTwoEight_isKGroup_constructed e)
    (solvable_isKGroup_constructed (H ⧸ N))

end CFSG.Quasithin.MainConverse.NineReduction
