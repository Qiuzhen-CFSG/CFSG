module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.ProfileActors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.MarkedCores
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.CartanApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearThreePresentation

/-!
# Original actor quotients force the U4 Cartan orders

Construct each local linear marking from the actual original quotient
map on S L_i, retaining its representatives and its projection square.
The full source Cartan action is then recovered from those root actors,
without identifying either whole faithful endpoint with a model. The
original elementary large radical supplies the commuting-root clause
and kills its Frattini kernel. Thus the exact full Cartan and both
Cartan-kernel orders follow from the genuine original row data.

The coefficient application removes the order premise from the scalar
construction on the same original Frattini section. Earlier section 2/5
remainder containments, original actor quotient maps and elementary
radical remain source inputs. Their structural producer is
qt-dgs85-quadrangle-structure, via ProfileActors and MarkedCores. The
irreducible action and tensor realization are not inferred from orders;
compatible field labels and the remaining Weyl equations remain with
the unitary source owner. Both orientations, q=2 and q=4 are included.

Source: DGS (11.7), pp.174--175; Fong--Seitz I (5C), (6A)(b), pp.26,37--38;
II (8.1)--(8.2), p.197, and the characteristic-two argument on p.201.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

section Marking
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)
variable (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,F))
variable (hf : Function.Surjective f)
variable (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf ((S ⊔ L i).subgroupOf (parabolic L S i)))

include e h hV f hf hk in
private theorem local_marking_exists :
    ∃ ν : localGroup Q split i ≃* PSL(2,F), ∃ μ : rankOne Q split i ≃* SL(2,F),
      (∀ r, ν (RootLocalCover.projection Q split i r) =
        Atlas.RankOneFieldAutomorphisms.slEquivPSL (μ r)) ∧
      ∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        MarkedLocal.endpointMap Q e i a.val = r ∧ μ r = f a := by
  let : ((S ⊔ L i).subgroupOf (parabolic L S i)).Normal :=
    QuadrangleStructure.marked_sylow_factor_normal Q e h split i
  obtain ⟨μ,ν,hν,hμ⟩ := QuadrangleStructure.marked_linear_localGroup Q e h split i
    (actorReflection Q split i) hV _ (subgroupOf_mono _ le_sup_left) f hf hk
  exact ⟨ν,μ,hν,hμ⟩

/-- The local marking is chosen from the original actor quotient, not supplied separately. -/
def markedLinearLocalMarking : localGroup Q split i ≃* PSL(2,F) :=
  (local_marking_exists Q e h split i hV f hf hk).choose

/-- The same marking retains the full actor and the actual original endpoint representatives. -/
theorem markedLinearLocalMarking_spec :
    ∃ μ : rankOne Q split i ≃* SL(2,F),
      (∀ r, markedLinearLocalMarking Q e h split i hV f hf hk (RootLocalCover.projection Q split i r) =
        Atlas.RankOneFieldAutomorphisms.slEquivPSL (μ r)) ∧
      ∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        MarkedLocal.endpointMap Q e i a.val = r ∧ μ r = f a :=
  (local_marking_exists Q e h split i hV f hf hk).choose_spec

omit Q e split in
/-- Literal Q.q representatives for the constructed marking on the original quotient. -/
theorem originalLinearLocalMarking_spec
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hV₀ : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i) :
    ∃ μ : rankOne Q₀ split₀ i ≃* SL(2,F),
      (∀ r, markedLinearLocalMarking Q₀ (originalMarkedIso Q₀) h split₀ i hV₀ f hf hk
          (RootLocalCover.projection Q₀ split₀ i r) =
        Atlas.RankOneFieldAutomorphisms.slEquivPSL (μ r)) ∧
      ∀ r : rankOne Q₀ split₀ i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        Q₀.q ⟨a.val,parabolic_le_generated i a.val.property⟩ = r ∧ μ r = f a := by
  obtain ⟨μ,hμ,hlift⟩ := markedLinearLocalMarking_spec Q₀ (originalMarkedIso Q₀) h split₀ i hV₀ f hf hk
  refine ⟨μ,hμ,fun r => ?_⟩
  obtain ⟨a,ha,hfa⟩ := hlift r
  exact ⟨a,(original_endpointMap_apply Q₀ i a.val).symm.trans ha,hfa⟩
end Marking

variable {K E : Type*} [Field K] [Finite K] [CharP K 2]
  [Field E] [Finite E] [CharP E 2]
variable (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
variable (hVi : simpleRemainder Q split i ≤ localKernel Q i)
variable (hVj : simpleRemainder Q split j ≤ localKernel Q j)
variable (fi : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
variable (fj : (S ⊔ L j).subgroupOf (parabolic L S j) →* SL(2,E))
variable (hfi : Function.Surjective fi) (hfj : Function.Surjective fj)
variable (hki : fi.ker = (pCore 2 (parabolic L S i)).subgroupOf ((S ⊔ L i).subgroupOf (parabolic L S i)))
variable (hkj : fj.ker = (pCore 2 (parabolic L S j)).subgroupOf ((S ⊔ L j).subgroupOf (parabolic L S j)))
variable (n : ℕ) (hn : 0 < n) (hK : Nat.card K = 2^n) (hE : Nat.card E = (2^n)^2)
variable (he : IsElementaryAbelian 2 ((parabolic L S j).pCoreIn 2))

include e h hm hij hVi hVj fi fj hfi hfj hki hkj hn hK hE he in
/-- No separate local marking, commuting equation, Cartan-order or Frattini
premise is needed once the original two actor quotient maps are supplied. -/
theorem marked_four_actor_cartan_cards :
    Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) = ((2^n)^2-1)*(2^n-1) ∧
      Nat.card (coreCartan Q i) = (2^n)^2-1 ∧
      Nat.card (coreCartan Q j) = 2^n-1 ∧
      frattini (simpleRemainder Q split j) = ⊥ := by
  have hc := QuadrangleStructure.marked_root_commutator_of_elementary_core Q e split i j hij hVj he
  have hh := four_actor_cartan_cards Q split hm i j hij hVi hVj
    (markedLinearLocalMarking Q e h split i hVi fi hfi hki)
    (markedLinearLocalMarking Q e h split j hVj fj hfj hkj) n hn hK hE hc
    (LinearThreePresentation.borel_core_eq_bot Q e h)
  let := QuadrangleStructure.marked_remainder_elementary Q e split j hVj he
  let : Fact (IsPGroup 2 (simpleRemainder Q split j)) := ⟨IsElementaryAbelian.isPGroup 2 _⟩
  exact ⟨hh.1,hh.2.1,hh.2.2,frattini_eq_bot_of_isElementaryAbelian (p := 2)⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
