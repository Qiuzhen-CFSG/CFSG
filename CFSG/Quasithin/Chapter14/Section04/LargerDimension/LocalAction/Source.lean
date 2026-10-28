module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags.Construction.Source

/-!
# The source local action and its three-vertex geometry

The natural action constructs the original cubic residual flag, including
[V₂,L₁]=V and ⟨L₁,L₂⟩=L across its two-core kernel. The extraspecial action
then constructs, for every Y-member, the full automorphism action on its
moved space and the selected faithful component. Cubic indices identify
the two whole parabolics, including their exhaustive and intersection clauses.

All markings here are the literal subgroups of Notation 12.8.2: H=F.H,
U=F.U, Wᵍ=F.X g, E=F.E g and Lᵢ=F.Li L i. The earlier 12.8.9(1) identity
identifies F.I₂ L with ⟨U,Uᵍ⟩. The whole parabolic is I₂T=L₂T; neither
I₂ nor a residual is identified with the whole parabolic.

The inputs are the earlier natural action, the explicit 12.8 extraspecial
clauses, condition (E), 1.2.1(1), and the universal 14.3.4 implication.
Their instantiation from genuine Hypothesis 14.3.10 remains with the outer
source assembly. No conclusion of 14.4.8 is an input. The geometry additionally
uses the sibling S₃ × S₃ quotient for a distinct second member, and the earlier
normality of L in M and uniqueness M=!M(LT). It constructs the intersections,
O²(L∩H₃)=L₂ and the relative normalizer and invokes the existing intrinsic
G₀ construction; recognition of G₀ remains with the outer assembly.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.4.8 and the ambient deductions in 14.4.13, printed pp.1009,1012.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
open Components
open Chapter12.Section08 (conjugate)
variable {G : Type*} [Group G] [Finite G]

/-- Both clauses of 14.4.8 from their earlier source inputs, without the
later middle-quotient hypothesis. `FullMovedSpaceAction` contains canonical
LStar and faithful-family membership, both actual PSL₃(2) core quotients,
and the literal surjective conjugation action with two-core kernel, together
with its GL₃(2) comparison. The parabolic record retains both maximality
clauses, distinctness, intersection T and exhaustiveness. -/
theorem source_lemma_14_4_8
    (earlier : EarlierComponentGeneration G)
    (T : Sylow 2 G) (hEven : IsEvenCharacteristicAt T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (d : NaturalThreeAction L V T) (F : Chapter12.Section08.InvariantFlag T V 3)
    (g : G) (hg : g ∈ L) [IsElementaryAbelian 2 (F.E g)]
    (extraspecial : EarlierExtraspecialData T (F.Vi 2) (F.E g)
      F.U (conjugate F.U g) (F.Vi 1) (conjugate (F.Vi 1) g) (F.X g) (F.Li L 2))
    (hI : F.I₂ L = F.U ⊔ conjugate F.U g) :
    F.Li L 1 ∈ YFamily F.H T (F.Vi 2) (F.E g) ∧
      movedSpace (F.Vi 2) (F.Li L 1) = V ∧
      localJoin (F.Li L 2) (F.Li L 1) = L ∧
      ∀ X : Subgroup G, X ∈ YFamily F.H T (F.Vi 2) (F.E g) →
        Nonempty (FullMovedSpaceAction T (F.I₂ L) (F.Li L 2) (F.Vi 2) X) ∧
        Quasithin.I5.RankTwoParabolics
          (localJoin (F.Li L 2) X ⊔ (T : Subgroup G) : Subgroup G)
          ((T : Subgroup G).subgroupOf (localJoin (F.Li L 2) X ⊔ (T : Subgroup G)))
          ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf
            (localJoin (F.Li L 2) X ⊔ (T : Subgroup G)))
          ((X ⊔ (T : Subgroup G)).subgroupOf
            (localJoin (F.Li L 2) X ⊔ (T : Subgroup G))) := by
  have hN := NaturalFlags.naturalFlagData_of_invariant_flag d F g hg
  obtain ⟨h₁, hjoin, _⟩ := NaturalFlags.source_membership_of_invariant_flag d F g hg
  refine ⟨h₁, hN.moved_eq, hjoin, ?_⟩
  intro X hX
  have ha : Nonempty (FullMovedSpaceAction T (F.I₂ L) (F.Li L 2) (F.Vi 2) X) := by
    rw [hI]
    exact full_action_of_earlier_data earlier T hEven classification extraspecial hX hN.L₂_three
  obtain ⟨a⟩ := ha
  exact ⟨⟨a⟩, a.parabolics hX hN.L₂_three (hI.trans extraspecial.supplement)
    extraspecial.U_le_T⟩

/-- Apply 14.4.8 to L₁ and the surviving second member and construct the
ambient geometry needed by 14.4.13. The three intersections, residual,
relative normalizer, proper maximality and D-system on the actual G₀ are
outputs. Only the independently produced middle quotient and genuine earlier
M-normality and uniqueness clauses are added to the local-action inputs. -/
noncomputable def source_geometry_of_source_flag
    (earlier : EarlierComponentGeneration G)
    (T : Sylow 2 G) (hEven : IsEvenCharacteristicAt T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    {M L V X : Subgroup G} [IsElementaryAbelian 2 V]
    (d : NaturalThreeAction L V T) (F : Chapter12.Section08.InvariantFlag T V 3)
    (g : G) (hg : g ∈ L) [IsElementaryAbelian 2 (F.E g)]
    (extraspecial : EarlierExtraspecialData T (F.Vi 2) (F.E g)
      F.U (conjugate F.U g) (F.Vi 1) (conjugate (F.Vi 1) g) (F.X g) (F.Li L 2))
    (hI : F.I₂ L = F.U ⊔ conjugate F.U g)
    (hX : X ∈ YFamily F.H T (F.Vi 2) (F.E g)) (hne : X ≠ F.Li L 1)
    (e₂ : coreQuotient (F.Li L 1 ⊔ X ⊔ (T : Subgroup G)) ≃* SymmetricThreeProduct.G)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → L ⊔ (T : Subgroup G) ≤ K → K = M)
    (hLM : L ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hMnorm : M ≤ normalizer (L : Set G)) :
    SourceGeometry L (F.Li L 1) (F.Li L 2) X M T := by
  have h := source_lemma_14_4_8 earlier T hEven classification d F g hg extraspecial hI
  let a₁ := (h.2.2.2 (F.Li L 1) h.1).1.some
  let aX := (h.2.2.2 X hX).1.some
  exact source_geometry_of_full_actions F.H M L (F.Li L 1) (F.Li L 2)
    (F.Vi 1) (F.Vi 2) V (F.E g) X (F.I₂ L) T
    (NaturalFlags.naturalFlagData_of_invariant_flag d F g hg)
    hX hne a₁ aX e₂ hunique hLM hTM hMnorm

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
