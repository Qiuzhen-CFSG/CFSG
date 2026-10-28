module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.SylowGeometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.PrimeSelection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticResidual
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticActor
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticCubic
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticPrimeGroup

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticSeven
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticLinear
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.Source

/-!
# Actual decomposable large-action supports

In dimension eight, the original large-action alternatives select the
ratio-two decomposable branch. Its original partition and same dihedral
prime give two complementary sixteen-element supports, their odd kernels,
and the index-two Sylow support stabilizer. The prepared source action also
constructs the actual four-subgroups V_i ∩ C_V(J₁(T)), their splitting of
V_E, and their exchange by every element exchanging the supports.

Inside the literal factor-product preimage, the marked centralizer has
faithful quotient residual equal to the opposite odd kernel, retaining the
same prime and both original sixteen-element supports. In the full marked
centralizer, the original C_T(Z1) is Sylow and the faithful residual order is
divisible by that same prime. Its fixed and moved subgroups are exactly the
two original sixteen-element supports. The actual source application gives
their complementarity, marked containment and exchange, in addition to the
central-seed bound for component selection.
For the same prime-three marking, the Sylow support stabilizer equals
C_T(Z₁), is normal of index two in T, and acts on the fixed support with
kernel of index two. This completes the exchanged-plane geometry in that
branch. The actual consumer retains the same prime-five alternative.
The prime-three full residual now equals the original opposite cubic kernel,
and its literal faithful quotient residual has that exact prime order. The
actual consumer retains this equality with the same geometry and prime-five
alternative. The original support-normalizer calculation and Sylow exchange
now prove marker generation. Component selection constructs the actual
prime-three component and retains its same pre-exclusion witness through
`exchangedSource`. The earlier 15.1.14 residual remains the parent's explicit
input. In prime five, restriction to the opposite support now proves the
full faithful residual cyclic of order five or fifteen. The original-action
consumer retains these alternatives and both sixteen-element supports.
The canonical O^{5′}(C_M(Z₁)) now has exact order-five image, through the
literal quotient, and acts irreducibly on the same moving support. Its fixed
support, C_T(Z₁)-normalization and containment in O²(C_M(Z₁)) are retained.
A genuine five-group lift now permutes with the original marked Sylow
centralizer and retains these supports and their movement. For the same
component and pre-exclusion witness, the moving support acts faithfully on
that component with image of order sixteen. The same-marking consumer now
excludes all ordinary components, the natural binary SL3 block and the
constrained rank-one alternative at prime five, retaining the original
pre-exclusion witness and faithful moving support. The prime-to-three
residual now centralizes V, excluding the constrained centralizer rows.
The original A₇ partition residual has a full-cover fixer of order at most
four, excluding the same faithful support of order sixteen. The remaining
SL₄(2) and SL₅(2) quotients now force equality of the selected parabolic's
two-residual and prime-to-three residual. Its centralization of V places
the parabolic in Mc, contradicting the original generation clause. The
same-component consumer therefore excludes every constrained alternative.
Excluding the extra cubic factor, constructing the prime-five marker, and
discharging constrained catalogue exhaustion remain necessary for the full
prime-five exclusion.

Source: Aschbacher--Smith 15.1.7(6), 15.1.16(a), and 15.1.24(1),
printed pp.1087--1088, 1092, and 1101.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

/-- On the actual eight-dimensional large action, retain the classified
decomposition together with its constructed support pair and same odd prime. -/
theorem LargeSourceAction.decomposable_supports_of_dimension_eight
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    {hn : M ≤ normalizer (V : Set G)} (hTM : (T : Subgroup G) ≤ M)
    (ha : LargeSourceAction T M V hn)
    (hdim : Module.finrank (ZMod 2) (Additive V) = 8) :
    ∃ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
      (d : Decomposition c.representation)
      (π : internalActionImage M V hn →* Equiv.Perm d.Index),
      SourceCases.Decomposable (imageRepresentation M V hn) (T : Subgroup G) M
        (actionHom M V hn).rangeRestrict c d π ∧
      cubicRatio (imageRepresentation M V hn) = 2 ∧
      Nonempty (DecomposableMarker.SupportPair (T := T) hn c d) := by
  obtain ⟨U,c,d,π,_,_,_,hperm,hcases⟩ := ha
  rcases hcases with h9 | hex | ⟨hdec,hq⟩
  · obtain ⟨l,_,hd,_⟩ := h9
    omega
  · obtain ⟨l,_,_,_,_,_,hd,_⟩ := hex
    omega
  · exact ⟨U,c,d,π,hdec,hq,
      DecomposableMarker.supportPair_of_decomposable hTM hn c d π
        (fun g k => (hperm g k).2.2) hdec hq⟩

end CFSG.Quasithin.Chapter15.Section01

public section

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual eight-dimensional large action constructs its two Thompson
four-groups, retaining its original supports, odd kernels and common prime. -/
theorem PreparedChosenModule.decomposable_thompsonPair_of_dimension_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (ha : letI := h.elementary; LargeSourceAction T M V h.normalized)
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 8) :
    letI := h.elementary
    ∃ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π ∧
      cubicRatio (imageRepresentation M V h.normalized) = 2 ∧
      Nonempty (DecomposableMarker.ThompsonPair (T := T) h.normalized c d) := by
  let := h.elementary
  obtain ⟨U,c,d,π,hd,_,_,hperm,hcases⟩ := ha
  rcases hcases with h9 | hex | ⟨hdec,hq⟩
  · obtain ⟨l,_,hfour,_⟩ := h9
    omega
  · obtain ⟨l,_,_,_,_,_,hsix,_⟩ := hex
    omega
  · exact ⟨U,c,d,π,hdec,hq,
      DecomposableMarker.thompsonPair_of_decomposable hG T hempty hM hmany hJ h hfull
        c d hd π (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) hdec hq⟩

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The original eight-dimensional prepared action constructs the marked
centralizer in its factor-product preimage, including the exact quotient
residual and the same original prime. No Thompson-image callback remains. -/
theorem PreparedChosenModule.decomposable_factorCentralizer_of_dimension_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (ha : letI := h.elementary; LargeSourceAction T M V h.normalized)
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 8) :
    letI := h.elementary
    ∃ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d),
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π ∧
      cubicRatio (imageRepresentation M V h.normalized) = 2 ∧
      let ρ := imageRepresentation M V h.normalized
      let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
        (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M V h.normalized).rangeRestrict)
      let C := DecomposableMarker.factorCentralizer M V h.normalized W
      let a := (actionHom M V h.normalized).rangeRestrict.comp C.subtype
      (pResidual 2 C).map a = (s.marking s.second).kernel.map
        (c.ambientFactor d s.second).embedding.groupMap ∧
      Nat.card (pResidual 2 (C ⧸ a.ker)) = s.prime := by
  subst V
  let := h.elementary
  obtain ⟨U,c,d,π,hd,_,_,hperm,hcases⟩ := ha
  rcases hcases with h9 | hex | ⟨hdec,hq⟩
  · obtain ⟨l,_,hfour,_⟩ := h9
    omega
  · obtain ⟨l,_,_,_,_,_,hsix,_⟩ := hex
    omega
  · have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π
      (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2)
      (Or.inr (Or.inr (Or.inl hdec)))
    have hstar := (h.thompson_actors T hM.1.2 hq
      (fun E hE => hE.rank_le_of_primeRank_le hr)).1
    have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
    have he := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
      hm hstar c d π (fun g k => (hperm g k).2.1) hdec).1
    obtain ⟨s⟩ := DecomposableMarker.thompsonPair_of_image hM.1.2 h.normalized c d π
      (fun g k => (hperm g k).2.2) hdec hq he
    exact ⟨U,c,d,π,s,hdec,hq,s.factorCentralizer_residual hM.1.2 h.normalized c d he⟩
end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The actual eight-dimensional action supplies the Sylow and central-seed
clauses in the full marked centralizer. Its residual contains the original
opposite prime kernel, retaining the same two supports and prime marking. -/
theorem PreparedChosenModule.decomposable_fullCentralizer_of_dimension_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (ha : letI := h.elementary; LargeSourceAction T M V h.normalized)
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 8) :
    letI := h.elementary
    ∃ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d),
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π ∧
      cubicRatio (imageRepresentation M V h.normalized) = 2 ∧
      let Z := DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z : Set G)
      let R := (pResidual 2 C).map C.subtype
      letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z : Set G)) C ∧
      s.prime ∣ Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) ∧
      V ⊓ centralizer (R : Set G) ≤ DecomposableMarker.plane V (c.ambientFactor d s.first).space ∧
      DecomposableMarker.plane V (c.ambientFactor d s.second).space ≤ ⁅V,R⁆ ∧
      centralInvolutions T ⊓ V ≤ Z ⊔ ⁅V,R⁆ := by
  subst V
  let := h.elementary
  obtain ⟨U,c,d,π,hd,_,_,hperm,hcases⟩ := ha
  rcases hcases with h9 | hex | ⟨hdec,hq⟩
  · obtain ⟨l,_,hfour,_⟩ := h9
    omega
  · obtain ⟨l,_,_,_,_,_,hsix,_⟩ := hex
    omega
  · have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π
      (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2)
      (Or.inr (Or.inr (Or.inl hdec)))
    have hstar := (h.thompson_actors T hM.1.2 hq
      (fun E hE => hE.rank_le_of_primeRank_le hr)).1
    have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
    have he := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
      hm hstar c d π (fun g k => (hperm g k).2.1) hdec).1
    obtain ⟨s⟩ := DecomposableMarker.thompsonPair_of_image hM.1.2 h.normalized c d π
      (fun g k => (hperm g k).2.2) hdec hq he
    exact ⟨U,c,d,π,s,hdec,hq,
      s.local_sylow hM.1.2 h.normalized c d π (fun g k => (hperm g k).2.2),
      s.full_quotient_residual_prime_dvd hM.1.2 h.normalized c d he,
      s.full_residual_bounds hM.1.2 h.normalized c d he⟩
end CFSG.Quasithin.Chapter15.Section01


namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
/-- The actual eight-dimensional source action gives exactly the two original
sixteen-element residual supports and their exchange, retaining the same
prime-three-or-five marking and the literal faithful quotient. -/
theorem PreparedChosenModule.decomposable_fullResidualGeometry_of_dimension_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (ha : letI := h.elementary; LargeSourceAction T M V h.normalized)
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 8) :
    letI := h.elementary
    ∃ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d),
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π ∧
      cubicRatio (imageRepresentation M V h.normalized) = 2 ∧
      let Z := DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z : Set G)
      let R := (pResidual 2 C).map C.subtype
      letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z : Set G)) C ∧
      s.prime ∣ Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) ∧
      V ⊓ centralizer (R : Set G) = DecomposableMarker.plane V (c.ambientFactor d s.first).space ∧
      ⁅V,R⁆ = DecomposableMarker.plane V (c.ambientFactor d s.second).space ∧
      Nat.card (V ⊓ centralizer (R : Set G) : Subgroup G) = 16 ∧
      Nat.card (⁅V,R⁆ : Subgroup G) = 16 ∧
      (V ⊓ centralizer (R : Set G)) ⊔ ⁅V,R⁆ = V ∧
      (V ⊓ centralizer (R : Set G)) ⊓ ⁅V,R⁆ = ⊥ ∧
      Z ≤ V ⊓ centralizer (R : Set G) ∧
      ∀ t ∈ (T : Subgroup G), t ∉ normalizer ((V ⊓ centralizer (R : Set G) : Subgroup G) : Set G) →
        (V ⊓ centralizer (R : Set G)).map (MulAut.conj t).toMonoidHom = ⁅V,R⁆ ∧
        ⁅V,R⁆.map (MulAut.conj t).toMonoidHom = V ⊓ centralizer (R : Set G) := by
  subst V
  let := h.elementary
  obtain ⟨U,c,d,π,hd,_,_,hperm,hcases⟩ := ha
  rcases hcases with h9 | hex | ⟨hdec,hq⟩
  · obtain ⟨l,_,hfour,_⟩ := h9
    omega
  · obtain ⟨l,_,_,_,_,_,hsix,_⟩ := hex
    omega
  · have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π
      (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2)
      (Or.inr (Or.inr (Or.inl hdec)))
    have hstar := (h.thompson_actors T hM.1.2 hq
      (fun E hE => hE.rank_le_of_primeRank_le hr)).1
    have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
    have he := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
      hm hstar c d π (fun g k => (hperm g k).2.1) hdec).1
    obtain ⟨s⟩ := DecomposableMarker.thompsonPair_of_image hM.1.2 h.normalized c d π
      (fun g k => (hperm g k).2.2) hdec hq he
    obtain ⟨hfix,hmove,hcf,hcm⟩ := s.full_residual_geometry hM.1.2 h.normalized c d π
      (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he
    refine ⟨U,c,d,π,s,hdec,hq,
      s.local_sylow hM.1.2 h.normalized c d π (fun g k => (hperm g k).2.2),
      s.full_quotient_residual_prime_dvd hM.1.2 h.normalized c d he,
      hfix,hmove,hcf,hcm,?_,?_,?_,?_⟩
    · rw [hfix,hmove]
      exact s.complement
    · rw [hfix,hmove]
      exact s.disjoint
    · rw [hfix]
      exact inf_le_left
    · rw [hfix,hmove]
      exact s.exchanges

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The original eight-dimensional action retains its same prime-five
alternative. In prime three it constructs the full exchanged-plane geometry
and the relative normality of the actual Sylow marked centralizer. -/
theorem PreparedChosenModule.decomposable_prime_five_or_exchangedGeometry_of_dimension_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (ha : letI := h.elementary; LargeSourceAction T M V h.normalized)
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 8) :
    letI := h.elementary
    ∃ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d),
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π ∧
      cubicRatio (imageRepresentation M V h.normalized) = 2 ∧
      (s.prime = 5 ∨
        (s.prime = 3 ∧
          (((T : Subgroup G) ⊓ centralizer
            (DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space : Set G)).subgroupOf
              (T : Subgroup G)).Normal ∧
          ∀ {Mc : Subgroup G} (e : CaseIComponentData T M Mc V),
            e.Z1 = DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space →
            e.row = .six → e.ExchangedPlaneGeometry)) := by
  subst V
  let := h.elementary
  obtain ⟨U,c,d,π,hd,_,_,hperm,hcases⟩ := ha
  rcases hcases with h9 | hex | ⟨hdec,hq⟩
  · obtain ⟨l,_,hfour,_⟩ := h9
    omega
  · obtain ⟨l,_,_,_,_,_,hsix,_⟩ := hex
    omega
  · have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π
      (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2)
      (Or.inr (Or.inr (Or.inl hdec)))
    have hstar := (h.thompson_actors T hM.1.2 hq
      (fun E hE => hE.rank_le_of_primeRank_le hr)).1
    have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
    have he := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
      hm hstar c d π (fun g k => (hperm g k).2.1) hdec).1
    obtain ⟨s⟩ := DecomposableMarker.thompsonPair_of_image hM.1.2 h.normalized c d π
      (fun g k => (hperm g k).2.2) hdec hq he
    refine ⟨U,c,d,π,s,hdec,hq,?_⟩
    rcases s.prime_cases with hthree | hfive
    · have hfour := s.support_four_not_dvd_of_prime_three hG T hM rfl h.normalized
        c d hd π (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2)
        hthree s.first
      have hnormal := (s.sylow_geometry_of_support_four_not_dvd hM.1.2 h.normalized c d hfour).2.2.1
      exact Or.inr ⟨hthree,hnormal,fun e hZ hrow =>
        s.exchangedPlaneGeometry_of_support_four_not_dvd hM.1.2 h.normalized c d π
          (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he hfour e hZ hrow⟩
    · exact Or.inl hfive

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The actual eight-dimensional source retains its same prime-five marking,
or proves the exact prime residual and exchanged geometry for its original
prime-three marking. The quotient uses C_M(V), not a substituted two-core. -/
theorem PreparedChosenModule.decomposable_prime_five_or_primeResidual_of_dimension_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (ha : letI := h.elementary; LargeSourceAction T M V h.normalized)
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 8) :
    letI := h.elementary
    ∃ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d),
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π ∧
      cubicRatio (imageRepresentation M V h.normalized) = 2 ∧
      (s.prime = 5 ∨
        (s.prime = 3 ∧
        let Z := DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space
        let C := M ⊓ centralizer (Z : Set G)
        letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
        Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = s.prime ∧
        (((T : Subgroup G) ⊓ centralizer (Z : Set G)).subgroupOf (T : Subgroup G)).Normal ∧
        ∀ (Mc : Subgroup G) (e : CaseIComponentData T M Mc V),
          e.Z1 = Z → e.row = .six → e.ExchangedPlaneGeometry)) := by
  subst V
  let := h.elementary
  obtain ⟨U,c,d,π,hd,_,_,hperm,hcases⟩ := ha
  rcases hcases with h9 | hex | ⟨hdec,hq⟩
  · obtain ⟨l,_,hfour,_⟩ := h9
    omega
  · obtain ⟨l,_,_,_,_,_,hsix,_⟩ := hex
    omega
  · have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π
      (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2)
      (Or.inr (Or.inr (Or.inl hdec)))
    have hstar := (h.thompson_actors T hM.1.2 hq
      (fun E hE => hE.rank_le_of_primeRank_le hr)).1
    have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
    have he := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
      hm hstar c d π (fun g k => (hperm g k).2.1) hdec).1
    obtain ⟨s⟩ := DecomposableMarker.thompsonPair_of_image hM.1.2 h.normalized c d π
      (fun g k => (hperm g k).2.2) hdec hq he
    refine ⟨U,c,d,π,s,hdec,hq,?_⟩
    rcases s.prime_cases with hthree | hfive
    · right
      have hf := s.support_four_not_dvd_of_prime_three hG T hM rfl h.normalized c d hd π
        (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) hthree s.first
      exact ⟨hthree,
        s.full_quotient_residual_card_of_prime_three hG T hM h.normalized c d π
          (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he hthree,
        (s.sylow_geometry_of_support_four_not_dvd hM.1.2 h.normalized c d hf).2.2.1,
        fun Mc e hZ hrow => s.exchangedPlaneGeometry_of_support_four_not_dvd hM.1.2
          h.normalized c d π (fun g k => (hperm g k).2.1)
          (fun g k => (hperm g k).2.2) he hf e hZ hrow⟩
    · exact Or.inl hfive

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Select the actual exchanged component in prime three while retaining the
same original marking, prime, and pre-exclusion source. Prime five remains an
explicit alternative. The parent large-component reduction discharges the
earlier 15.1.14 residual input; no later catalogue exclusion is assumed here. -/
theorem PreparedChosenModule.decomposable_prime_five_or_exchangedSource_of_dimension_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (ha : letI := h.elementary; LargeSourceAction T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 8) :
    letI := h.elementary
    ∃ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d),
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π ∧
      cubicRatio (imageRepresentation M V h.normalized) = 2 ∧
      (s.prime = 5 ∨
        (s.prime = 3 ∧ ∃ e : CaseIComponentData T M Mc V,
          e.Z1 = DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space ∧
          e.row = .six ∧ e.PreExclusionSource h.normalized s.prime ∧ e.ExchangedSource)) := by
  subst V
  let := h.elementary
  obtain ⟨U,c,d,π,hd,_,_,hperm,hcases⟩ := ha
  rcases hcases with h9 | hex | ⟨hdec,hq⟩
  · obtain ⟨l,_,hfour,_⟩ := h9
    omega
  · obtain ⟨l,_,_,_,_,_,hsix,_⟩ := hex
    omega
  · have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π
      (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2)
      (Or.inr (Or.inr (Or.inl hdec)))
    have hstar := (h.thompson_actors T hM.1.2 hq
      (fun E hE => hE.rank_le_of_primeRank_le hr)).1
    have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
    have he := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
      hm hstar c d π (fun g k => (hperm g k).2.1) hdec).1
    obtain ⟨s⟩ := DecomposableMarker.thompsonPair_of_image hM.1.2 h.normalized c d π
      (fun g k => (hperm g k).2.2) hdec hq he
    refine ⟨U,c,d,π,s,hdec,hq,?_⟩
    rcases s.prime_cases with hthree | hfive
    · obtain ⟨m,hmZ,hmp,hmrow,hgeometry⟩ := s.preExclusionMarker_of_prime_three
        hG T hM rfl h.normalized c d hd π (fun g k => (hperm g k).2.1)
          (fun g k => (hperm g k).2.2) he hthree
      obtain ⟨e,hZ,hrow,hpre⟩ := h.component_of_preExclusionMarker
        hG T hempty hM hmany hJ hu hne rfl m hres
      have hsPre : e.PreExclusionSource h.normalized s.prime := hmp ▸ hpre
      have h3Pre : e.PreExclusionSource h.normalized 3 := hthree ▸ hsPre
      exact Or.inr ⟨hthree,e,hZ.trans hmZ,hrow.trans hmrow,hsPre,
        h3Pre.exchangedSource hG h (hgeometry e hZ hrow)⟩
    · exact Or.inl hfive

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The original eight-dimensional action has a cyclic faithful marked-centralizer
residual. The only unexcluded extra factor is cubic in the prime-five branch.
The same original marking and both sixteen-element residual supports are retained. -/
theorem PreparedChosenModule.decomposable_cyclicResidual_of_dimension_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (ha : letI := h.elementary; LargeSourceAction T M V h.normalized)
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 8) :
    letI := h.elementary
    ∃ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d),
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π ∧
      cubicRatio (imageRepresentation M V h.normalized) = 2 ∧
      let Z := DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z : Set G)
      let R := (pResidual 2 C).map C.subtype
      letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
      let Q := pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)
      IsCyclic Q ∧
      (Nat.card Q = s.prime ∨ (s.prime = 5 ∧ Nat.card Q = 15)) ∧
      V ⊓ centralizer (R : Set G) =
        DecomposableMarker.plane V (c.ambientFactor d s.first).space ∧
      ⁅V,R⁆ = DecomposableMarker.plane V (c.ambientFactor d s.second).space ∧
      Nat.card (V ⊓ centralizer (R : Set G) : Subgroup G) = 16 ∧
      Nat.card (⁅V,R⁆ : Subgroup G) = 16 := by
  subst V
  let := h.elementary
  obtain ⟨U,c,d,π,hd,_,_,hperm,hcases⟩ := ha
  rcases hcases with h9 | hex | ⟨hdec,hq⟩
  · obtain ⟨l,_,hfour,_⟩ := h9
    omega
  · obtain ⟨l,_,_,_,_,_,hsix,_⟩ := hex
    omega
  · have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π
      (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2)
      (Or.inr (Or.inr (Or.inl hdec)))
    have hstar := (h.thompson_actors T hM.1.2 hq
      (fun E hE => hE.rank_le_of_primeRank_le hr)).1
    have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
    have he := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
      hm hstar c d π (fun g k => (hperm g k).2.1) hdec).1
    obtain ⟨s⟩ := DecomposableMarker.thompsonPair_of_image hM.1.2 h.normalized c d π
      (fun g k => (hperm g k).2.2) hdec hq he
    refine ⟨U,c,d,π,s,hdec,hq,?_⟩
    have hgeo := s.full_residual_geometry hM.1.2 h.normalized c d π
      (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he
    rcases s.prime_cases with hthree | hfive
    · have hc := s.full_quotient_residual_card_of_prime_three hG T hM h.normalized c d π
        (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he hthree
      exact ⟨isCyclic_of_prime_card (hc.trans hthree),Or.inl hc,hgeo⟩
    · obtain ⟨hcyc,hcard⟩ := s.full_quotient_residual_of_prime_five hM.1.2 h.normalized c d π
        (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he hfive
      refine ⟨hcyc,?_,hgeo⟩
      exact hcard.elim (fun hc => Or.inl (hc.trans hfive.symm))
        (fun hc => Or.inr ⟨hfive,hc⟩)

end CFSG.Quasithin.Chapter15.Section01

public section
namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The actual eight-dimensional action supplies the canonical quintic actor,
its exact original quotient image and its irreducible moving support. The same
prime-three alternative and original marking are retained. The full two-residual
is not replaced by this smaller residual. -/
theorem PreparedChosenModule.decomposable_quinticActor_of_dimension_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (ha : letI := h.elementary; LargeSourceAction T M V h.normalized)
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 8) :
    letI := h.elementary
    ∃ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d),
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π ∧
      cubicRatio (imageRepresentation M V h.normalized) = 2 ∧
      (s.prime = 3 ∨ (s.prime = 5 ∧
      let Z := DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z : Set G)
      let Y := (primeToResidual 5 C).map C.subtype
      let B := DecomposableMarker.plane V (c.ambientFactor d s.second).space
      letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
      Nat.card (primeToResidual 5
        (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5 ∧
      (Y.subgroupOf M).map (actionHom M V h.normalized).rangeRestrict =
        (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap ∧
      V ⊓ centralizer (Y : Set G) =
        DecomposableMarker.plane V (c.ambientFactor d s.first).space ∧
      ⁅V,Y⁆ = B ∧
      ⁅B,Y⁆ = B ∧
      Nat.card (V ⊓ centralizer (Y : Set G) : Subgroup G) = 16 ∧
      Nat.card (⁅V,Y⁆ : Subgroup G) = 16 ∧
      ((T : Subgroup G) ⊓ centralizer (Z : Set G)) ≤ normalizer (Y : Set G) ∧
      (primeToResidual 5 Y).map Y.subtype = Y ∧
      Y ≤ (pResidual 2 C).map C.subtype ∧
      ∀ D : Subgroup G, D ≤ B → Y ≤ normalizer (D : Set G) → D = ⊥ ∨ D = B)) := by
  subst V
  let := h.elementary
  obtain ⟨U,c,d,π,hd,_,_,hperm,hcases⟩ := ha
  rcases hcases with h9 | hex | ⟨hdec,hq⟩
  · obtain ⟨l,_,hfour,_⟩ := h9
    omega
  · obtain ⟨l,_,_,_,_,_,hsix,_⟩ := hex
    omega
  · have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π
      (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2)
      (Or.inr (Or.inr (Or.inl hdec)))
    have hstar := (h.thompson_actors T hM.1.2 hq
      (fun E hE => hE.rank_le_of_primeRank_le hr)).1
    have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
    have he := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
      hm hstar c d π (fun g k => (hperm g k).2.1) hdec).1
    obtain ⟨s⟩ := DecomposableMarker.thompsonPair_of_image hM.1.2 h.normalized c d π
      (fun g k => (hperm g k).2.2) hdec hq he
    refine ⟨U,c,d,π,s,hdec,hq,?_⟩
    rcases s.prime_cases with hthree | hfive
    · exact Or.inl hthree
    · refine Or.inr ⟨hfive,?_⟩
      have hc := s.full_quotient_quintic_residual hM.1.2 h.normalized c d π
        (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he hfive
      obtain ⟨him,hfix,hmove,hcf,hcm,hnorm,hself,hres⟩ :=
        s.quintic_actor_geometry hM.1.2 h.normalized c d π
          (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he hfive
      have hmoveB := s.quintic_actor_moves_support hM.1.2 h.normalized c d π
        (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he hfive
      exact ⟨hc,him,hfix,hmove,hmoveB,hcf,hcm,hnorm,hself,hres,
        s.quintic_actor_irreducible hM.1.2 h.normalized c d π
          (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he hfive⟩

end CFSG.Quasithin.Chapter15.Section01


namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The actual eight-dimensional source supplies a five-group that permutes
with the original marked Sylow centralizer and acts irreducibly on the same
sixteen-element support. The original prime-three alternative is retained. -/
theorem PreparedChosenModule.decomposable_quinticPrimeGroup_of_dimension_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (ha : letI := h.elementary; LargeSourceAction T M V h.normalized)
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 8) :
    letI := h.elementary
    ∃ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d),
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π ∧
      cubicRatio (imageRepresentation M V h.normalized) = 2 ∧
      (s.prime = 3 ∨ (s.prime = 5 ∧
      let Z := DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z : Set G)
      let S := (T : Subgroup G) ⊓ centralizer (Z : Set G)
      let B := DecomposableMarker.plane V (c.ambientFactor d s.second).space
      ∃ Y : Subgroup G, IsPGroup 5 Y ∧ IsPPerfect 2 Y ∧
        Y ≤ (primeToResidual 5 C).map C.subtype ∧
        (S : Set G) * (Y : Set G) = (Y : Set G) * (S : Set G) ∧
        (Y.subgroupOf M).map (actionHom M V h.normalized).rangeRestrict =
          (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap ∧
        V ⊓ centralizer (Y : Set G) =
          DecomposableMarker.plane V (c.ambientFactor d s.first).space ∧
        ⁅V,Y⁆ = B ∧ ⁅B,Y⁆ = B ∧
        (∀ D : Subgroup G, D ≤ B → Y ≤ normalizer (D : Set G) → D = ⊥ ∨ D = B) ∧
        ∀ (Mc : Subgroup G) (e : CaseIComponentData T M Mc V),
          e.Z1 = Z → e.PreExclusionSource h.normalized 5 →
          Y ≤ normalizer (e.L : Set G) ∧
          ∃ hBL : B ≤ normalizer (e.L : Set G),
            Function.Injective (actionHom B e.L hBL) ∧
            Nat.card (internalActionImage B e.L hBL) = 16)) := by
  subst V
  let := h.elementary
  obtain ⟨U,c,d,π,hd,_,_,hperm,hcases⟩ := ha
  rcases hcases with h9 | hex | ⟨hdec,hq⟩
  · obtain ⟨l,_,hfour,_⟩ := h9
    omega
  · obtain ⟨l,_,_,_,_,_,hsix,_⟩ := hex
    omega
  · have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π
      (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2)
      (Or.inr (Or.inr (Or.inl hdec)))
    have hstar := (h.thompson_actors T hM.1.2 hq
      (fun E hE => hE.rank_le_of_primeRank_le hr)).1
    have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
    have he := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
      hm hstar c d π (fun g k => (hperm g k).2.1) hdec).1
    obtain ⟨s⟩ := DecomposableMarker.thompsonPair_of_image hM.1.2 h.normalized c d π
      (fun g k => (hperm g k).2.2) hdec hq he
    refine ⟨U,c,d,π,s,hdec,hq,?_⟩
    rcases s.prime_cases with hthree | hfive
    · exact Or.inl hthree
    · obtain ⟨Y,hYp,hYperf,hYA,hSY,him,hfix,hmove,hmoveB,hirr⟩ :=
        s.exists_permuting_quintic_actor hM.1.2 h.normalized h.le_selected c d π
          (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he hfive
      refine Or.inr ⟨hfive,Y,hYp,hYperf,hYA,hSY,him,hfix,hmove,hmoveB,hirr,?_⟩
      intro Mc e hZ hpre
      have hnorm := le_sup_left.trans hpre.residual_normalizes
      change (pResidual 2 (M ⊓ centralizer (e.Z1 : Set G) : Subgroup G)).map
        (M ⊓ centralizer (e.Z1 : Set G)).subtype ≤ normalizer (e.L : Set G) at hnorm
      rw [hZ] at hnorm
      have hAR := (s.quintic_actor_geometry hM.1.2 h.normalized c d π
        (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he hfive).2.2.2.2.2.2.2
      exact ⟨hYA.trans (hAR.trans hnorm),
        s.quintic_moving_support_faithful_on_component hM.1.2 h.normalized c d π
          (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he hfive e hZ hpre⟩

end CFSG.Quasithin.Chapter15.Section01


namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Apply the prime-five exclusions on the same marking supplied by the
original eight-dimensional action. Its moving support still acts faithfully
with image of order sixteen. The prime-three alternative is unchanged;
the missing prime-five marker is not assumed to have been constructed. -/
theorem PreparedChosenModule.decomposable_quintic_component_exclusions_of_dimension_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (ha : letI := h.elementary; LargeSourceAction T M V h.normalized)
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 8)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    letI := h.elementary
    ∃ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d),
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π ∧
      cubicRatio (imageRepresentation M V h.normalized) = 2 ∧
      (s.prime = 3 ∨ (s.prime = 5 ∧
        ∀ e : CaseIComponentData T M Mc V,
          e.Z1 = DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space →
          e.PreExclusionSource h.normalized s.prime →
          ¬ IsComponent e.G1 (e.L.subgroupOf e.G1) ∧
          ¬ ChapterC.IsSL3EvenBlock e.L 1 ∧
          ¬ e.ConstrainedRankOneAlternative ∧
          let B := DecomposableMarker.plane V (c.ambientFactor d s.second).space
          ∃ hBL : B ≤ normalizer (e.L : Set G),
            Function.Injective (actionHom B e.L hBL) ∧
            Nat.card (internalActionImage B e.L hBL) = 16)) := by
  let := h.elementary
  obtain ⟨U,c,d,π,s,hdec,hq,hcases⟩ :=
    h.decomposable_quinticPrimeGroup_of_dimension_eight hG T hempty hM hmany hJ hfull ha hdim
  refine ⟨U,c,d,π,s,hdec,hq,?_⟩
  rcases hcases with hthree | ⟨hfive,Y,_,_,_,_,_,_,_,_,_,hcomponent⟩
  · exact .inl hthree
  · refine .inr ⟨hfive,?_⟩
    intro e hZ hpre
    have hp : e.PreExclusionSource h.normalized 5 := hfive ▸ hpre
    exact ⟨hp.not_ordinary_of_prime_five (h := h) hG hempty hM hJ hu hne hmany hres,
      hp.not_linearThree_of_prime_five (h := h) hG hM hJ,
      hp.no_constrained_rankOne (h := h) (.inr rfl) hG hM hJ,
      (hcomponent Mc e hZ hp).2⟩

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- On the same eight-dimensional marking, exclude the constrained cubic
centralizer and A₇ rows, retaining only the actual binary linear quotients.
The original moving support remains faithful of order sixteen. -/
theorem PreparedChosenModule.decomposable_quintic_constrained_reduction_of_dimension_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (ha : letI := h.elementary; LargeSourceAction T M V h.normalized)
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 8)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    letI := h.elementary
    ∃ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d),
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π ∧
      cubicRatio (imageRepresentation M V h.normalized) = 2 ∧
      (s.prime = 3 ∨ (s.prime = 5 ∧
        ∀ e : CaseIComponentData T M Mc V,
          e.Z1 = DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space →
          e.PreExclusionSource h.normalized s.prime →
          ¬ IsComponent e.G1 (e.L.subgroupOf e.G1) ∧
          ¬ ChapterC.IsSL3EvenBlock e.L 1 ∧
          ¬ e.ConstrainedRankOneAlternative ∧
          ¬ e.ConstrainedCentralizerIdentity ∧
          ((primeToResidual 3 (M ⊓ e.L : Subgroup G)).map (M ⊓ e.L).subtype ≤
            centralizer (V : Set G)) ∧
          ¬ e.ConstrainedA7Alternative ∧
          (e.ConstrainedAlternatives →
            ∃ (n : ℕ) (f : (e.L ⧸ pCore 2 e.L) ≃*
                Matrix.SpecialLinearGroup (Fin n) (ZMod 2)),
              (n = 4 ∨ n = 5) ∧ e.ConstrainedLinearParabolic f e.ML ∧
              e.ConstrainedLinearParabolic f (M ⊓ e.L) ∧ (M ⊓ e.L) ⊔ e.ML = e.L) ∧
          let B := DecomposableMarker.plane V (c.ambientFactor d s.second).space
          ∃ hBL : B ≤ normalizer (e.L : Set G),
            Function.Injective (actionHom B e.L hBL) ∧
            Nat.card (internalActionImage B e.L hBL) = 16)) := by
  let := h.elementary
  obtain ⟨U,c,d,π,s,hdec,hq,hcases⟩ :=
    h.decomposable_quintic_component_exclusions_of_dimension_eight
      hG T hempty hM hmany hJ hu hne hfull ha hdim hres
  refine ⟨U,c,d,π,s,hdec,hq,?_⟩
  rcases hcases with hthree | ⟨hfive,hcomponent⟩
  · exact .inl hthree
  · refine .inr ⟨hfive,?_⟩
    intro e hZ hpre
    have hp : e.PreExclusionSource h.normalized 5 := hfive ▸ hpre
    obtain ⟨ho,hl,hr,hBL,hfaith,hcard⟩ := hcomponent e hZ hpre
    have hA7 := hp.not_alternatingSeven_of_image_sixteen (h := h) hM.1.2
      (DecomposableMarker.plane_le _) hBL hcard
    exact ⟨ho,hl,hr,hp.not_constrainedCentralizerIdentity_of_prime_five (h := h) hM.1.2,
      hp.cubic_residual_centralizes_of_prime_five (h := h),
      hA7,fun a => (hp.constrained_reduction_of_prime_five (h := h) hG hM hJ a).resolve_left hA7,
      hBL,hfaith,hcard⟩

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The original eight-dimensional action excludes both the ordinary and
constrained catalogues at prime five on its same component. Both original
supports retain order sixteen. The pre-exclusion witness remains explicit
until the ambient prime-five marker is constructed. -/
theorem PreparedChosenModule.decomposable_quintic_catalogue_obstruction_of_dimension_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (ha : letI := h.elementary; LargeSourceAction T M V h.normalized)
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 8)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    letI := h.elementary
    ∃ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d),
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π ∧
      cubicRatio (imageRepresentation M V h.normalized) = 2 ∧
      Nat.card (DecomposableMarker.plane V (c.ambientFactor d s.first).space) = 16 ∧
      Nat.card (DecomposableMarker.plane V (c.ambientFactor d s.second).space) = 16 ∧
      (s.prime = 3 ∨ (s.prime = 5 ∧
        ∀ e : CaseIComponentData T M Mc V,
          e.Z1 = DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space →
          e.PreExclusionSource h.normalized s.prime →
          ¬ IsComponent e.G1 (e.L.subgroupOf e.G1) ∧
          ¬ e.ConstrainedAlternatives ∧
          let B := DecomposableMarker.plane V (c.ambientFactor d s.second).space
          ∃ hBL : B ≤ normalizer (e.L : Set G),
            Function.Injective (actionHom B e.L hBL) ∧
            Nat.card (internalActionImage B e.L hBL) = 16)) := by
  let := h.elementary
  obtain ⟨U,c,d,π,s,hdec,hq,hcases⟩ :=
    h.decomposable_quintic_component_exclusions_of_dimension_eight
      hG T hempty hM hmany hJ hu hne hfull ha hdim hres
  refine ⟨U,c,d,π,s,hdec,hq,s.support_card s.first,s.support_card s.second,?_⟩
  rcases hcases with hthree | ⟨hfive,hcomponent⟩
  · exact .inl hthree
  · refine .inr ⟨hfive,?_⟩
    intro e hZ hpre
    have hp : e.PreExclusionSource h.normalized 5 := hfive ▸ hpre
    obtain ⟨ho,_,_,hBL,hfaith,hcard⟩ := hcomponent e hZ hpre
    exact ⟨ho,hp.not_constrained_of_prime_five_image_sixteen (h := h)
      hG hM hJ hfull hu (DecomposableMarker.plane_le _) hBL hcard,hBL,hfaith,hcard⟩

end CFSG.Quasithin.Chapter15.Section01
