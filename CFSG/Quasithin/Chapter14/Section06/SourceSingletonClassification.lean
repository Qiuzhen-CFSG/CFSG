module
public import CFSG.Quasithin.Chapter14.Section06.SourceTransitiveFactors
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.PrimitiveSingletonCyclic

/-!
# Cyclic starred actors in the primitive singleton branch

The original quotient J/O₂(J) has a minimal normal elementary odd residual
of prime rank at most two. The actual seed argument supplies a globally fixed
complement to its moved space. The primitive representation theorem applies
with the original SQTK cover J and the literal quotient map, and makes every
ambient starred actor cyclic. Injective factor embeddings give the requested
singleton conclusion. This argument also works for the nonsingleton family.

The elementary-nine extension with cyclic starred actors is allowed; its
ambient exclusion and the final 14.6.12 assembly remain separate.
Source: Aschbacher--Smith 14.6.11--12, printed pp.1030--1031, and D.2.14--22.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hu hmany hcard e hab

/-- The original primitive residual and fixed complement exclude noncyclic
starred actors on the literal quotient module. -/
theorem source_solvable_minimal_star_cyclic
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (A : Subgroup (J ⧸ pCore 2 J)) (hA : A ∈ ChapterD.QhatStar a.representation) :
    IsCyclic A := by
  let := hs
  obtain ⟨p,hp,hE,hbound,_hne,hmin⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  let : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> decide⟩
  have ho : Odd p := by rcases hp with rfl | rfl <;> decide
  obtain ⟨_,_,_,hcover,_,_⟩ := Section02.source_lemma_14_2_2_8_minimal
    hG T hempty hM hu hmany hcard e J hJ
  exact ChapterD.RatioDecomposition.primitive_star_cyclic_of_fixed_complement
    a.representation a.faithful (pCore_quotient_pCore_eq_bot 2) p ho hE hbound hmin
    (source_rankTwo_span_decomposition hG T hempty hM hu hmany hcard e hab J hJ.1 a)
    hcover (QuotientGroup.mk' (pCore 2 J)) (QuotientGroup.mk'_surjective _) A hA

/-- Every starred actor of the actual singleton factor is cyclic. The proof
retains the literal factor inclusion, rather than identifying Sylow with cyclic.
The stronger ambient theorem does not need the two displayed singleton premises. -/
theorem source_singleton_factor_star_cyclic
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (_hd : d.FittingFull) (_hsingle : Nat.card d.Index = 1)
    (i : d.Index) (A : Subgroup (d.factor i).Carrier)
    (hA : A ∈ ChapterD.QhatStar (d.factor i).action) : IsCyclic A := by
  let j : (d.factor i).Carrier →* (J ⧸ pCore 2 J) :=
    (ChapterD.Jhat a.representation).subtype.comp (d.factor i).embedding.groupMap
  have hj : Function.Injective j :=
    (ChapterD.Jhat a.representation).subtype_injective.comp (d.factor i).embedding.group_injective
  have hstar : A.map j ∈ ChapterD.QhatStar a.representation := by
    change A.map ((ChapterD.Jhat a.representation).subtype.comp
      (d.factor i).embedding.groupMap) ∈ _
    rw [← map_map]
    exact (f.stars _).mp (((d.factor i).embedding.stars A).mp hA)
  let : IsCyclic (A.map j) := source_solvable_minimal_star_cyclic
    hG T hempty hM hu hmany hcard e hab J hJ hs a (A.map j) hstar
  exact isCyclic_of_injective (equivMapOfInjective A j hj).toMonoidHom
    (equivMapOfInjective A j hj).injective

end CFSG.Quasithin.Chapter14.Section06
