module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.AffineCentralizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryAffineCartan

/-!
# The original order-32 Cartan fixed section on the affine hexagon

Pull the actual kernel centralizer back through the same endpoint marking.
It is literally C_{S intersect K_j}(H), with the original full panel
kernel and the same marked Cartan. Restriction of the endpoint map gives
an isomorphism with the quotient section and preserves every representative.
The root actor's nontrivial action transports back to the original group.

The original nonbinary linear quotient supplies the opposite local model
and its (2B) containment. The Chapter 12 application uses the inherited
perfectness of L and proves that its remaining affine hexagon alternative
contains this order-32 section with nontrivial original root action.
No perfectness or (2B) is assumed at the binary unitary endpoint.

Source: Fong--Seitz I (5I), printed pp.31--34; DGS Theorem D, p.224;
Aschbacher--Smith F.1.1--3 and 12.2.2. The subsequent solvable-module
contradiction, the other even Weyl branches, minimality and exhaustive
seven-row marked recognition remain with this source-recognition family.
The earlier marked split quotient retains the apartment/exchange producer
and final source-assembly discharge.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

/-- The original Sylow/panel-kernel intersection fixed by the actual full Cartan. -/
@[expose] def originalAffineFixed (j : Fin 2) : Subgroup (parabolic L S j) :=
  (S.subgroupOf (parabolic L S j) ⊓ originalPanelKernel (L := L) (S := S) j) ⊓
    centralizer ((Q.tits.B ⊓ Q.tits.N).comap (endpointMap Q e j) : Set (parabolic L S j))

private theorem endpointMap_injective (j : Fin 2) : Function.Injective (endpointMap Q e j) :=
  (Q.tits.standardParabolic {Q.simple j}).subtype_injective.comp (endpoint Q e j).injective

private theorem endpointMap_range (j : Fin 2) :
    (endpointMap Q e j).range = Q.tits.standardParabolic {Q.simple j} := by
  rw [endpointMap,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (endpoint Q e j).surjective,
    ← MonoidHom.range_eq_map,range_subtype]

include h in
/-- The original fixed subgroup is the literal preimage under the given endpoint map. -/
theorem originalAffineFixed_eq_comap (j : Fin 2) :
    originalAffineFixed Q e j =
      (LocalCover.radical Q split j ⊓
        centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D))).comap (endpointMap Q e j) := by
  rw [originalAffineFixed,← original_radical_comap Q e h split j]
  let f := endpointMap Q e j
  change (LocalCover.radical Q split j).comap f ⊓
    centralizer ((Q.tits.B ⊓ Q.tits.N).comap f : Set (parabolic L S j)) =
    (LocalCover.radical Q split j).comap f ⊓
      (centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D))).comap f
  congr 1
  have hH : Q.tits.B ⊓ Q.tits.N ≤ f.range := by
    rw [endpointMap_range]
    exact inf_le_left.trans (Q.tits.B_le_standardParabolic _)
  ext a
  constructor
  · intro ha
    apply mem_centralizer_iff.mpr
    intro t ht
    obtain ⟨b,hb⟩ := hH ht
    have hbH : b ∈ (Q.tits.B ⊓ Q.tits.N).comap f := by
      change f b ∈ Q.tits.B ⊓ Q.tits.N
      rwa [hb]
    simpa only [map_mul,hb] using congrArg f (mem_centralizer_iff.mp ha b hbH)
  · intro ha
    apply mem_centralizer_iff.mpr
    intro t ht
    apply endpointMap_injective Q e j
    simpa only [map_mul] using mem_centralizer_iff.mp ha (f t) ht

include h in
/-- The same endpoint map reaches the entire quotient fixed section. -/
theorem originalAffineFixed_map (j : Fin 2) :
    (originalAffineFixed Q e j).map (endpointMap Q e j) =
      LocalCover.radical Q split j ⊓
        centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) := by
  rw [originalAffineFixed_eq_comap Q e h split j,map_comap_eq,endpointMap_range]
  exact inf_eq_right.mpr (inf_le_left.trans
    (inf_le_left.trans (split.U_le.trans (Q.tits.B_le_standardParabolic _))))

/-- Restrict the original endpoint marking to its genuine affine fixed section. -/
def originalAffineFixedEquiv (j : Fin 2) (hx : BinaryUnitaryException Q split j) :
    originalAffineFixed Q e j ≃* (affineFixedSection Q split j hx.1 hx.2.1 hx.2.2.1).numerator :=
  ((originalAffineFixed Q e j).equivMapOfInjective (endpointMap Q e j)
    (endpointMap_injective Q e j)).trans (MulEquiv.subgroupCongr (originalAffineFixed_map Q e h split j))

@[simp] theorem originalAffineFixedEquiv_apply (j : Fin 2)
    (hx : BinaryUnitaryException Q split j) (x : originalAffineFixed Q e j) :
    (originalAffineFixedEquiv Q e h split j hx x : X ⧸ Q.D) = endpointMap Q e j x := by rfl

include h in
/-- The original root actor acts nontrivially on this same kernel section. -/
theorem originalAffineFixed_noncentral (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (hx : BinaryUnitaryException Q split j) :
    ¬ originalRankOne Q e split j ≤ centralizer (originalAffineFixed Q e j : Set (parabolic L S j)) := by
  intro hc
  let d := affineFixedSection Q split j hx.1 hx.2.1 hx.2.2.1
  apply affine_hexagon_fixed_section_action_ne_one Q split hm i j hij
    (UnitarySource.actorReflection Q split j) hx.1 hx.2.1 hx.2.2.1
  apply MonoidHom.ext
  intro r
  apply MulEquiv.ext
  intro z
  induction z using QuotientGroup.induction_on with
  | H x =>
    change d.action r (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [d.action_mk]
    congr 1
    apply Subtype.ext
    rw [d.numeratorAction_apply]
    obtain ⟨a,rfl⟩ := (originalRankOneEquiv Q e split j).surjective r
    obtain ⟨b,rfl⟩ := (originalAffineFixedEquiv Q e h split j hx).surjective x
    rw [originalRankOneEquiv_apply,originalAffineFixedEquiv_apply]
    have hh := congrArg (endpointMap Q e j) (mem_centralizer_iff.mp (hc a.property) b b.property)
    rw [map_mul,map_mul] at hh
    rw [← hh,mul_inv_cancel_right]

include h in
/-- The original linear factor supplies all opposite-model premises of the order-32 calculation. -/
theorem binary_affine_hexagon_fixed_section_of_linear
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hperfect : Group.IsPerfect (L i))
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (hx : BinaryUnitaryException Q split j) :
    Nat.card (originalAffineFixed Q e j) = 32 ∧
      ¬ originalRankOne Q e split j ≤ centralizer (originalAffineFixed Q e j : Set (parabolic L S j)) := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  let a := linearLocalEquiv Q e h split i hperfect T hT μ
  refine ⟨?_,originalAffineFixed_noncentral Q e h split hm i j hij hx⟩
  rw [Nat.card_congr (originalAffineFixedEquiv Q e h split j hx).toEquiv]
  exact affine_hexagon_fixed_section_card Q split hF hm i j hij
    (linear_remainder_le_kernel Q e h split i T hT μ) a
    (UnitarySource.actorReflection Q split i) hx.1 hx.2.1 hx.2.2.1

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter 12 hexagon is regular or has the marked order-32 affine fixed section. -/
theorem rankOne_global_hexagon_regularity_or_affine_fixed_section
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 6) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
    (∀ i : Fin 2, simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) i)) ∨
    (MarkedLocal.BinaryUnitaryException Q split 1 ∧
      MarkedLocal.BinaryAffineComparison Q e hf split 1 ∧
      MarkedLocal.BinaryAffineEndpointComparison Q e 1 ∧
      Nat.card (MarkedLocal.originalAffineFixed Q e 1) = 32 ∧
      ¬ MarkedLocal.originalRankOne Q e split 1 ≤
        centralizer (MarkedLocal.originalAffineFixed Q e 1 :
          Set (parabolic ![L,R] (Global.sourceS L H) 1))) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  let hf := d.hypothesisF11 hi hTH
  rcases D.rankOne_global_regularity_or_even_affine_cartan h hmany hn hpsl d hTH Q e split with hr | hx
  · exact Or.inl hr
  · obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hpsl
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    have hF2 : 2 < Nat.card F := by
      rw [hcard]
      exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) hn)
    have hh := MarkedLocal.binary_affine_hexagon_fixed_section_of_linear Q e hf split hF2 hm 0 1
      (by decide) (Chapter1.mem_L_isPerfect hi.local_mem.1.1) μ hx.1
    exact Or.inr ⟨hx.1,hx.2.1,hx.2.2.2.1,hh⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
