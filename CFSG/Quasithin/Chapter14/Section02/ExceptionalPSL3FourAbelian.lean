module
public import CFSG.Quasithin.Chapter14.Section02.ExceptionalPSL3FourSections
public import CFSG.Quasithin.Chapter14.Section02.OutsideParabolic
public import CFSG.Quasithin.Chapter14.Section06.SourcePlacedQuadraticActor
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection

/-!
# The abelian branch of the original exceptional PSL₃(4) contradiction

The rank-two source hypotheses construct the original outside group's faithful
binary span action and a placed quadratic actor. Normality and the Sylow
supplement identify the selected C-component with the literal two-residual.
The actor is therefore faithful on its image in H/O₂(H).

On that exact quotient, the component is PSL₃(4). A surviving irreducible
section keeps the same quadratic actor and its bound, contradicting the
field-cover exclusion. No section selection or representation hypothesis is
left as an additional source input.

Source: Aschbacher–Smith 14.2.13, printed p.984, using 12.8.6(5),
F.9.16(3), F.9.18(2–4), and B.4.2/B.4.5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]

theorem source_abelian_psl3Four_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (K : Subgroup H) (hK : K.IsCComponent) (hn : K.Normal)
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) : False := by
  let := hn
  obtain ⟨hU,a,B,hB,hBA,hq,hcost,_,_⟩ := Section06.source_rankTwo_bounded_placed_action
    hG T hempty hM hu hmany hcard e hab H hH.1
  let := hU
  have hgen' : K ⊔ (T : Subgroup G).subgroupOf H = ⊤ := by
    exact hgen
  have hfaith := Section06.source_placed_actor_faithful_on_normal_cComponent
    T hH.1.1.2 B hB K hK hn hgen'
  obtain ⟨_,_,_,hsq,_,_⟩ := source_lemma_14_2_2_8_minimal
    hG T hempty hM hu hmany hcard e H hH
  have hsqQ := ChapterE.Structure.sqtk_two_quotient hsq (pCore 2 H) pCore_isPGroup
  have hmQ : ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (pCore 2 H))) 3 4 :=
    hm.of_mulEquiv (hK.subnormal.quotientCoreImageEquiv 2).symm
  exact false_of_psl3Four_faithful_quadratic_actor a.representation
    (K.map (QuotientGroup.mk' (pCore 2 H))) (B.map (QuotientGroup.mk' (pCore 2 H)))
    hsqQ hmQ a.faithful hBA hq hcost hfaith

end CFSG.Quasithin.Chapter14.Section02
