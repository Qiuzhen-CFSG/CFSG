module
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.ExchangedSetup
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.PrimitiveCubic
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.Reduction
public import CFSG.Quasithin.Chapter14.Section06.SourceCyclicComplete
public import CFSG.Quasithin.Chapter14.Section06.SourceSolvableContainment

/-!
# The exchanged-factor family from its remaining ambient branches

The primitive elementary residual makes every minimal outside subgroup solvable.
Its actual quotient action supplies the ratio decomposition. The singleton
classification reduces to the cyclic first-parabolic recognition or elementary
nine. In the nonsingleton case, the kernel reduction leaves only the literal
quintic outer action. Once these three independent source inputs are supplied,
the same factors lift to all clauses of 14.6.12 and to the universal earlier
cubic orders needed by the later Borel argument.

The three inputs are explicit, not proofs of their ambient exclusions. In
particular no later normalizer theorem supplies the earlier index-two claim.
Source: Aschbacher--Smith 14.6.12, printed p.1031; its use in 14.6.14--17,
printed pp.1032--1036.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]

namespace SourceSingletonCompatibility

/-- The still-open elementary-nine exclusion on the literal singleton data.
The original ambient hypotheses are supplied by the assembly theorem. -/
def NineExclusion (T : Sylow 2 G) (M : Subgroup G) : Prop :=
  ∀ (J : Subgroup G), J ∈ Chapter3.HStar (T : Subgroup G) M →
    Group.IsSolvable J →
    ∀ (hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)),
      let := hU
      ∀ (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
        (f : ChapterD.RatioDecomposition.FactorData a.representation
          (ChapterD.Jhat a.representation)
          (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
        (d : ChapterD.RatioDecomposition.Decomposition f.representation),
        d.FittingFull → Nat.card d.Index = 1 →
        Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9 →
        ClassificationModels.IsTheoremEModel G

/-- The unresolved outer action on the actual quintic factor. Both the
permutation and its kernel keep their literal quotient maps. -/
def QuinticOuterExclusion (T : Sylow 2 G) (M : Subgroup G) : Prop :=
  ∀ (J : Subgroup G), J ∈ Chapter3.HStar (T : Subgroup G) M →
    Group.IsSolvable J →
    ∀ (hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)),
      let := hU
      ∀ (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
        (f : ChapterD.RatioDecomposition.FactorData a.representation
          (ChapterD.Jhat a.representation)
          (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
        (d : ChapterD.RatioDecomposition.Decomposition f.representation),
        d.FittingFull →
        ∀ (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index),
          ChapterD.Jhat a.representation ≤ π.ker →
          (π.ker.comap (QuotientGroup.mk' (pCore 2 J))).index = 2 →
          (∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
            (f.ambientFactor d (π g i)).actor) →
          (∀ i j, ∃ g : J ⧸ pCore 2 J, π g i = j) →
          SourcePairCompatibility.QuinticOuterAction a f d π →
          ClassificationModels.IsTheoremEModel G

/-- The genuine first-parabolic alternatives used by the existing cyclic
recognition theorem, required only at the original Sylow index five. -/
def QuinticFirstParabolics (T : Sylow 2 G) (M : Subgroup G) : Prop :=
  ∀ J : Subgroup G, J ∈ Chapter3.HStar (T : Subgroup G) M →
    (T : Subgroup G).relIndex J = 5 →
    Nonempty (Tits.ExceptionalParabolics.FullRee.first ≃* J) ∨
    Nonempty (Tits.ExceptionalParabolics.first ≃* J)

end SourceSingletonCompatibility

private theorem solvable_of_primitive_residual (J : Subgroup G) (p : ℕ)
    (hp : p = 3 ∨ p = 5) (hprim : OddNormalizer.PrimitiveResidual J p) :
    Group.IsSolvable J := by
  let := hprim.elementary
  let : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> decide⟩
  let : Group.IsNilpotent (pResidual 2 (J ⧸ pCore 2 J)) :=
    (IsElementaryAbelian.isPGroup p _).isNilpotent
  let : Group.IsNilpotent ((J ⧸ pCore 2 J) ⧸ pResidual 2 (J ⧸ pCore 2 J)) :=
    (isPGroup_quotient_pResidual 2).isNilpotent
  let : Group.IsSolvable (J ⧸ pCore 2 J) :=
    (Group.isSolvable_iff_subgroup_quotient (pResidual 2 (J ⧸ pCore 2 J))).mpr
      ⟨inferInstance,inferInstance⟩
  let : Group.IsNilpotent (pCore 2 J) := pCore_isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 J)).mpr
    ⟨inferInstance,inferInstance⟩

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab


variable (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (hfirst : SourceSingletonCompatibility.QuinticFirstParabolics T M)
    (hnine : SourceSingletonCompatibility.NineExclusion T M)
    (houter : SourceSingletonCompatibility.QuinticOuterExclusion T M)

include hnot hfirst hnine

/-- The actual ratio family has two factors after discharging its two
singleton endpoints. The action, factors and original subgroup are preserved. -/
theorem source_ratio_two_of_singleton_inputs
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    : Nat.card d.Index = 2 := by
  classical
  obtain ⟨π,_hblocks,_hker,hperm⟩ := source_ratio_factor_permutation
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd
  have hcount := (source_ratio_factor_count hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π (fun g i => (hperm g i).2.1)).1
  by_contra htwo
  have hpos : 0 < Nat.card d.Index := Nat.card_pos
  have hone : Nat.card d.Index = 1 := by omega
  obtain ⟨i,hi⟩ := Nat.card_eq_one_iff_exists.mp hone
  have hc := source_singleton_factor_star_cyclic hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d hd hone i
  rcases source_ratio_singleton_cyclicStar_alternatives
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd i hi hc with hcyc | hn
  · exact hnot (source_solvable_minimal_cyclic_theoremE_of_first_parabolic
      hG T hempty hM hu hmany hcard e hab J hJ hs hcyc (hfirst J hJ))
  · exact hnot (hnine J hJ hs inferInstance a f d hd hone hn.2.1)

omit hfirst hnine
include houter

/-- The only remaining kernel obstruction is the original quintic outer
action; excluding it gives index two for the actor join itself. -/
theorem source_ratio_index_two_of_outer_input
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index) : (ChapterD.Jhat a.representation).index = 2 := by
  obtain ⟨π,hker,hindex,hp,ht,halt⟩ := source_ratio_nonsingleton_kernel_reduction
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore
  rcases halt with he | ho
  · exact he.2
  · exact (hnot (houter J hJ hs inferInstance a f d hd π hker hindex hp ht (Classical.choice ho))).elim

include hnot hfirst hnine houter

/-- All literal clauses of 14.6.12 for every fresh primitive outside group,
conditional only on the three independent ambient branches above. -/
theorem source_exchanged_factor_family_of_singleton_inputs : SourceExchangedFactorFamily T M := by
  intro J hJ p hp hprim _hne
  have hs := solvable_of_primitive_residual J p hp hprim
  obtain ⟨hU,a,_hq⟩ := source_rankTwo_quadratic_bound
    hG T hempty hM hu hmany hcard e hab J hJ.1
  let := hU
  obtain ⟨f,d,hd⟩ := source_solvable_minimal_ratio_decomposition
    hG T hempty hM hu hmany hcard e hab J hJ hs a
  have htwo := source_ratio_two_of_singleton_inputs
    hG T hempty hM hu hmany hcard e hab hnot hfirst hnine J hJ hs a f d hd
  have hmore : 1 < Nat.card d.Index := by omega
  have hi := source_ratio_index_two_of_outer_input
    hG T hempty hM hu hmany hcard e hab hnot houter J hJ hs a f d hd hmore
  exact ⟨hU,a,source_ratio_nonsingleton_exchanged_setup_of_index
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore p hp hprim hi⟩

omit houter

/-- The fresh cubic subgroups require no quintic outer-action exclusion:
the cubic pair kernel is already proved. The same singleton inputs give
exactly the residual and quotient orders used by the Borel construction. -/
theorem source_earlier_cubic_orders_of_singleton_inputs :
    OddNormalizer.EarlierCubicFactorOrders (T : Subgroup G) M := by
  intro J hJ hprim _hne
  have hs := solvable_of_primitive_residual J 3 (Or.inl rfl) hprim
  obtain ⟨hU,a,_hq⟩ := source_rankTwo_quadratic_bound
    hG T hempty hM hu hmany hcard e hab J hJ.1
  let := hU
  obtain ⟨f,d,hd⟩ := source_solvable_minimal_ratio_decomposition
    hG T hempty hM hu hmany hcard e hab J hJ hs a
  have htwo := source_ratio_two_of_singleton_inputs
    hG T hempty hM hu hmany hcard e hab hnot hfirst hnine J hJ hs a f d hd
  exact source_ratio_nonsingleton_cubic_orders hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d hd (by omega) hprim

end CFSG.Quasithin.Chapter14.Section06
