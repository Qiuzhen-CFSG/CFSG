module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.Assembly
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.Interfaces
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.ModelMarking
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.Selection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.SourceReduction

/-!
# The actual V₂ marking and completed constituent selection

The full earlier FF classification is applied to the faithful Thompson
action on U_I and transferred to the actual U_L = [U_I,L]. It leaves
Irr⁺ on all of U_L or two binary natural SL₃(2) copies. In the latter
case, V₂ has order four and meets the actual parabolic's fixed space
trivially; the marked parabolic has order 24. Binary geometry therefore
selects a natural copy containing V₂, and equivariant transport gives a
genuine Irr⁺ constituent in the original module.

The witness retains the exact stabilizer M_L*, the literal central
submodule and quotient action, and injectivity of V₂ into that quotient.
The doubled output also retains the actual natural embedding and the
model plane. Its two separately transported coordinate lines have the
same original parabolic marking, with the same node and group equivalence.
The original V₂ is not asserted to lie in both disjoint summands.

The source-facing theorems use relative component normality, I=LS,
Y₊≤L, the common Sylow witness, rank one and the genuine preliminary
plane identities. These are the needed conclusions of 15.3.11 and
15.3.26–29; minimality and solvable-invariant control need not be invoked
again once those conclusions and the small marking are supplied. SQTK
remains explicit. The universal earlier FF implication is the authorized
input, using the corrected projective-line convention. No local
constituent, line, or full-action classification is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
B.5.3–6, pp.104–105; 15.3.26–31, pp.1130–1132 (PDF pp.1147–1149).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

section Source
open EightGeometry.NaturalModule.Recognition
universe u
variable {G : Type u} [Group G] [Finite G]
  (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
  (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
  (hf : HasCharacteristicTwo I)
  (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = d.S)
  [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)]

/-- The actual component parabolic contains Y₊, whose action on V₂ has
no fixed vector. This supplies the moving-plane input for binary geometry. -/
theorem plane_disjoint_parabolic_fixed (hline : LineData d I) (hYL : d.Yplus ≤ c.L) :
    Disjoint (planeSpace d c)
      (fixedSpace ((componentAction d c hn hI hf S hS).comp (d.starImage I c.L).subtype)
        ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L))) := by
  have hYM : d.Yplus ≤ d.M :=
    (hline.theta_eq ▸ theta_le (d.MI I)).trans inf_le_left
  have hYP : d.starImage I d.Yplus ≤ d.starImage I (d.M ⊓ c.L) :=
    map_mono (comap_mono (le_inf hYM hYL))
  apply (hline.planeSpace_fixed_disjoint d c hn hI hf S hS).mono_right
  intro v hv y
  exact hv ⟨⟨y, (map_mono (comap_mono hYL)) y.property⟩, hYP y.property⟩

/-- The first paragraph of 15.3.31 from the actual local source inputs
and the authorized universal earlier FF classification. The doubled branch
retains full coordinates and a natural embedding containing the original V₂.
No containing-constituent, splitting or marked-line premise remains. -/
theorem marked_alternative_of_source (hline : LineData d I) (hYL : d.Yplus ≤ c.L)
    (hRank : primeRank 3 d.Yplus = 1) (hYRank : 2 ≤ primeRank 3 d.Y)
    (hVT : d.V ≤ (d.T : Subgroup G)) {κ : GroupClass.{u}} (hSQTK : IsSQTK κ I)
    (classification : ProjectiveLine.CompleteClassificationInput.{u,u} κ)
    (hm : Parabolics.SmallParabolicMarking d I c.L) :
    let ρ := componentAction d c hn hI hf S hS
    let Lstar := d.starImage I c.L
    let Pstar := (d.starImage I (d.M ⊓ c.L)).subgroupOf Lstar
    Nonempty (MarkedConstituent ρ Lstar (planeSpace d c) Pstar) ∧
      (IsIrrPlus ρ Lstar ⊤ ∨ ∃ e : ActionEquiv (ρ.comp Lstar.subtype) (repeated binaryNatural 2),
        Nonempty (BinaryDoubledLine ((planeSpace d c).map e.linearEquiv.toLinearMap)
          (Pstar.map e.groupEquiv.toMonoidHom))) := by
  apply marked_of_smallAction
  · exact SourceReduction.smallAction_of_projectiveLine_source d c hn hI hf S hS
      hVT hYL hSQTK classification hm
  · exact hline.planeSpace_card d c S hS hYL
  · exact plane_stabilizer_eq_of_rank_one d c hn hI hf S hS hline hYL hRank hYRank
  · exact plane_disjoint_parabolic_fixed d c hn hI hf S hS hline hYL

/-- The actual V₂ lies in a noncentral Irr⁺ constituent; its stabilizer is
M_L* and its map to the literal central quotient is injective. -/
theorem marked_constituent_of_source (hline : LineData d I) (hYL : d.Yplus ≤ c.L)
    (hRank : primeRank 3 d.Yplus = 1) (hYRank : 2 ≤ primeRank 3 d.Y)
    (hVT : d.V ≤ (d.T : Subgroup G)) {κ : GroupClass.{u}} (hSQTK : IsSQTK κ I)
    (classification : ProjectiveLine.CompleteClassificationInput.{u,u} κ)
    (hm : Parabolics.SmallParabolicMarking d I c.L) :
    Nonempty (MarkedConstituent (componentAction d c hn hI hf S hS)
      (d.starImage I c.L) (planeSpace d c)
      ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L))) :=
  (marked_alternative_of_source d c hn hI hf S hS hline hYL hRank hYRank hVT
    hSQTK classification hm).1

/-- Apply the original rank-two marking, including its original node, to
each of the separate coordinate lines supplied by the doubled branch. -/
theorem doubled_copy_stabilizer_model {H : Type*} [Group H]
    (e : ActionEquiv ((componentAction d c hn hI hf S hS).comp
      (d.starImage I c.L).subtype) (repeated binaryNatural 2))
    (b : BinaryDoubledLine ((planeSpace d c).map e.linearEquiv.toLinearMap)
      (((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)).map e.groupEquiv.toMonoidHom))
    (parabolic : Fin 2 → Subgroup H)
    (m : Parabolics.RankTwoParabolicMarking d I c.L H parabolic) (i : Fin 2) :
    (subspaceStabilizer ((componentAction d c hn hI hf S hS).comp
      (d.starImage I c.L).subtype) (b.plane.map (copyEmbedding e i))).map m.equiv.toMonoidHom =
        parabolic m.node := by
  rw [((binaryLine_copy_markings _ e _ _ b).1 i).2.2]
  exact m.intersection

omit [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)] in
/-- Construct the elementary structure on U_L as well as the marked
constituent. Only the genuine earlier local and universal FF inputs remain. -/
theorem marked_constituent_of_local_source (hline : LineData d I) (hYL : d.Yplus ≤ c.L)
    (hRank : primeRank 3 d.Yplus = 1) (hYRank : 2 ≤ primeRank 3 d.Y)
    (hVT : d.V ≤ (d.T : Subgroup G)) {κ : GroupClass.{u}} (hSQTK : IsSQTK κ I)
    (classification : ProjectiveLine.CompleteClassificationInput.{u,u} κ)
    (hm : Parabolics.SmallParabolicMarking d I c.L) :
    let _ := component_internal_elementary d c hf S hS
    Nonempty (MarkedConstituent (componentAction d c hn hI hf S hS)
      (d.starImage I c.L) (planeSpace d c)
      ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L))) := by
  let _ := component_internal_elementary d c hf S hS
  exact marked_constituent_of_source d c hn hI hf S hS hline hYL hRank hYRank hVT
    hSQTK classification hm

end Source
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
