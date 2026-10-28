module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# The two terminal contradictions in Theorem 15.3.1

In the S₃ branch the actual X_E centralizes both singular four-groups E
and F. It therefore normalizes their join. The source normalizer assertion
15.3.46(2) puts this normalizer in M: a totally singular subgroup of the
given orthogonal four-space has order at most four, whereas E and F are
distinct fours. This is the normalizer argument applied in the source to
EF = Z-perp, and contradicts the genuine escape of X_E in 15.3.67(3).

In the other branch the assembled action recognition gives an actual A₅
quotient of X intersect N_G(V₁), with X the embedded J(G₀). The source
containment N_G(V₁) ≤ M and solvability of M make this quotient solvable,
contrary to the perfectness and nontriviality of A₅. The definite V₁ is
the original supported plane; it is not one of the singular groups E,F.

The final implications consume the original terminal alternative. Earlier
source construction, the normalizer controls, solvability and escape, and
the full F.6/B.5 classification witnesses remain explicit inputs owned by
the assembly of 15.3.1. No recognition or quotient conclusion is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the final
paragraph of Theorem 15.3.1, printed p.1155 (PDF p.1172), using 15.3.45(2),
15.3.46(2), and 15.3.66–68.
-/

@[expose] public section

open Subgroup Atlas.Codes Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame

open TerminalRecognition TerminalRecognition.ExceptionalAction AbelianAmalgam
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

universe u
variable {G : Type u} [Group G] [Finite G] {G₀ M V : Subgroup G}
  {d : NaturalOrthogonalAction M V}
  {a : Intersection.SourceInput (V.subgroupOf G₀)}

omit [Finite G] in
private theorem singular_card_le_four {A : Subgroup G}
    (hA : MarkedPlane.IsSingularIn M V A d) : Nat.card A ≤ 4 := by
  let f : A →* OrthogonalPlaneVector :=
    { toFun := fun x => d.coordinates ⟨x, hA.1 x.property⟩ 1
      map_one' := by
        change d.coordinates 1 1 = 1
        rw [map_one]
        rfl
      map_mul' := by
        intro x y
        change d.coordinates ((⟨x, hA.1 x.property⟩ : V) *
          ⟨y, hA.1 y.property⟩) 1 = _
        rw [map_mul]
        rfl }
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro x hx
    have hcoord : d.coordinates ⟨x, hA.1 x.property⟩ = 1 := by
      funext i
      exact (hA.2 ⟨x, hA.1 x.property⟩ x.property i 1).mpr hx
    have he := d.coordinates.injective (hcoord.trans d.coordinates.map_one.symm)
    exact Subtype.ext (congrArg (fun v : V => (v : G)) he)
  have hc : Nat.card OrthogonalPlaneVector = 4 := by
    norm_num [OrthogonalPlaneVector, Nat.card_eq_fintype_card]
  exact (Nat.card_le_card_of_injective f hf).trans_eq hc

/-- The source 15.3.46(2) assertion controls the join of the actual two
distinct singular four-groups. No normalizer conclusion about this join
is included among the inputs. -/
theorem singular_join_normalizer_le (g : EarlierGeometry d a)
    (h46 : ∀ U : Subgroup G, U ≤ V → ¬ normalizer (U : Set G) ≤ M →
      MarkedPlane.IsSingularIn M V U d) :
    normalizer ((g.E ⊔ otherLine g.E g.s : Subgroup G) : Set G) ≤ M := by
  have hsM : g.s ∈ M := g.sylow_le g.conjugator_mem.1
  have hFV : otherLine g.E g.s ≤ V := by
    have hV : V.map (MulAut.conj g.s⁻¹).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (d.normalizes (M.inv_mem hsM))
    exact (map_mono g.singular.1).trans_eq hV
  have hFcard : Nat.card (otherLine g.E g.s) = 4 :=
    (card_map_of_injective (MulAut.conj g.s⁻¹).injective).trans g.singular_card
  have hne : otherLine g.E g.s ≠ g.E :=
    GoldschmidtCore.otherLine_ne g.T g.E g.s
      g.conjugator_mem.1 g.conjugator_not_mem
  by_contra hn
  have hc := singular_card_le_four (d := d) (h46 _ (sup_le g.singular.1 hFV) hn)
  have hE : g.E = g.E ⊔ otherLine g.E g.s :=
    eq_of_le_of_card_ge le_sup_left (hc.trans_eq g.singular_card.symm)
  have hFE : otherLine g.E g.s ≤ g.E := le_sup_right.trans hE.ge
  exact hne (eq_of_le_of_card_ge hFE
    (g.singular_card.trans hFcard.symm).le)

/-- The S₃ identities imply that the original X_E normalizes EF. All
centralizer containments are transported through the actual inclusion of G₀. -/
theorem lineX_normalizes_singular_join (g : EarlierGeometry d a)
    (hs : Cases.SymmetricThreeConclusion a ((centralInvolutions g.T).subgroupOf G₀)) :
    lineX g.E ≤ normalizer ((g.E ⊔ otherLine g.E g.s : Subgroup G) : Set G) := by
  have hXF : a.XE ≤ centralizer (a.F : Set G₀) :=
    a.second_le_thompson.trans (le_centralizer_iff.mp hs.singular_centralizes)
  have hXFambient : lineX g.E ≤ centralizer (otherLine g.E g.s : Set G) := by
    intro x hx f hf
    have hxmap : x ∈ a.XE.map G₀.subtype := g.second_map.symm ▸ hx
    have hfmap : f ∈ a.F.map G₀.subtype := g.singular_map.symm ▸ hf
    obtain ⟨x, hx', rfl⟩ := hxmap
    obtain ⟨f, hf', rfl⟩ := hfmap
    exact congrArg (fun y : G₀ => (y : G)) (hXF hx' f hf')
  exact (le_inf ((lineX_le_centralizer g.E).trans (Subgroup.centralizer_le_normalizer _))
    (hXFambient.trans (Subgroup.centralizer_le_normalizer _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup g.E (otherLine g.E g.s))

/-- The genuine 15.3.46(2) and 15.3.67(3) inputs contradict the S₃ branch. -/
theorem symmetricThree_impossible (g : EarlierGeometry d a)
    (h46 : ∀ U : Subgroup G, U ≤ V → ¬ normalizer (U : Set G) ≤ M →
      MarkedPlane.IsSingularIn M V U d)
    (hescape : ¬ lineX g.E ≤ M)
    (hs : Cases.SymmetricThreeConclusion a ((centralInvolutions g.T).subgroupOf G₀)) :
    False :=
  hescape ((lineX_normalizes_singular_join g hs).trans (singular_join_normalizer_le g h46))

variable [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))]

omit [Finite G] in
/-- The actual ambient A₅ quotient contradicts 15.3.45(2) and the
solvability conclusion of 15.3.67(1). -/
theorem exceptional_impossible (c : ExceptionalConclusion d a)
    (h45 : normalizer (d.plane 1 : Set G) ≤ M) (hsol : Group.IsSolvable M) : False := by
  let _ := hsol
  obtain ⟨f, hf⟩ := c.ambient_normalizer_quotients 1
  let P : Subgroup G := ambientThompson G₀ ⊓ normalizer (d.plane 1 : Set G)
  have hPM : P ≤ M := inf_le_right.trans h45
  let _ : Group.IsSolvable P := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hPM) (inclusion_injective hPM)
  let _ : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5))
    (Group.isSolvable_of_surjective hf)

omit [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))] in
/-- The earlier source conclusions used only by the final contradictions.
They do not contain a terminal alternative, recognized action or quotient. -/
structure EarlierControls (g : EarlierGeometry d a) : Prop where
  /-- The singular-normalizer implication of 15.3.46(2), in the same coordinates. -/
  normalizer_escape_singular : ∀ U : Subgroup G, U ≤ V →
    ¬ normalizer (U : Set G) ≤ M → MarkedPlane.IsSingularIn M V U d
  /-- 15.3.45(2), for the original definite plane. -/
  definite_normalizer : normalizer (d.plane 1 : Set G) ≤ M
  /-- The solvability conclusion in 15.3.67(1). -/
  solvable : Group.IsSolvable M
  /-- The ambient escape assertion of 15.3.67(3). -/
  residual_escape : ¬ lineX g.E ≤ M

/-- Both genuine terminal contradictions, applied to the assembled
alternative on the unchanged local input and original definite planes. -/
theorem terminal_alternative_impossible (g : EarlierGeometry d a) (h : EarlierControls g)
    (halt : Cases.SymmetricThreeConclusion a ((centralInvolutions g.T).subgroupOf G₀) ∨
      Nonempty (ExceptionalConclusion d a)) : False := by
  rcases halt with hs | hc
  · exact symmetricThree_impossible g h.normalizer_escape_singular h.residual_escape hs
  · obtain ⟨c⟩ := hc
    exact exceptional_impossible c h.definite_normalizer h.solvable

omit [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))] in
/-- The full terminal source implication. Earlier construction and the
genuine classification theorems remain the parent's inputs; all terminal
classification branching and both contradictions are discharged here. -/
theorem terminal_contradiction_of_full_classifications
    (g : EarlierGeometry d a) (h : EarlierControls g)
    {K : GroupClass.{u}} (hG₀ : IsSQTK K G₀)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K)
    (hZE : centralInvolutions g.T ≤ g.E)
    (hFspan : a.F = conjugateSpanBy ((centralInvolutions g.T).subgroupOf G₀) a.YF) :
    False := by
  let _ := g.moduleClosure_elementary
  exact terminal_alternative_impossible g h
    (g.terminal_alternative_of_full_classifications hG₀ classificationF classificationB hZE hFspan)

omit [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))] in
/-- The terminal contradiction with the seed span stated in the original
ambient group and transported through the literal source inclusion. -/
theorem terminal_contradiction_of_ambient_span
    (g : EarlierGeometry d a) (h : EarlierControls g)
    {K : GroupClass.{u}} (hG₀ : IsSQTK K G₀)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K)
    (hZE : centralInvolutions g.T ≤ g.E)
    (hspan : otherLine g.E g.s = conjugateSpanBy (centralInvolutions g.T)
      (otherLine (lineY (residualY M g.Mc) g.E) g.s)) : False :=
  terminal_contradiction_of_full_classifications g h hG₀ classificationF classificationB hZE
    (g.intrinsic_seed_span hZE hspan)

end CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame
