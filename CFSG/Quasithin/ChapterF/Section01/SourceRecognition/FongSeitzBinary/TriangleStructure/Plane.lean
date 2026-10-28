module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TriangleStructure.NaturalCores
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.MarkedPlane

/-!
# The triangle plane and its regular radical action

The literal root orders give valence q+1 on both coset fibers. The proved
rotation-three geometry therefore supplies a projective plane of order q.
Each complementary radical is its endpoint two-core, lies in the common
Borel and fixes the endpoint neighborhood by relative normality. Thus the
nontrivial middle root gives elations with the marked center and axis.
The natural SL₂ action conjugates any nonidentity element of the axis
radical to one of these middle-root elements, so the entire radical acts
by elations. Such elements fix no affine point. Its order q² then makes
its affine action regular.

Everything is derived from one original linear factor on the same fully
marked split quotient, including q=2. No natural-action record, plane or
elation premise is supplied. The resulting evaluation equivalence feeds
the remaining one-field incidence and full marked A₂ comparison steps.
Source: Fong--Seitz I (3E), printed p.14, via projective-plane recognition;
DGS, Groups and Graphs (1985), (10.5) and Theorem D, pp.156,224.
-/

@[expose] public noncomputable section
open Subgroup Configuration Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TriangleStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 3) (i : Fin 2) {n : ℕ}
  (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n))
include e h split hm i hi

private theorem root_card (j : Fin 2) : Nat.card (simpleRoot Q split j) = 2^n := by
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := original_linear_factors Q e h split hm i hi j
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  exact (simpleRoot_card_linear Q e h split j T hT μ).trans hcard

/-- The literal quotient triangle has constant valence q+1, from its original factor. -/
theorem original_neighbor_card (v : Vertex (TriangleGeometry.family Q)) :
    Nat.card ((graph (TriangleGeometry.family Q)).neighborSet v) = 2^n+1 := by
  obtain ⟨g,hg⟩ := CosetGeometry.exists_smul_base (TriangleGeometry.family Q) v
  have he := Nat.card_congr
    ((CosetGeometry.translationGraphIso (TriangleGeometry.family Q) g).mapNeighborSet
      (base (TriangleGeometry.family Q) v.type))
  change Nat.card ((graph (TriangleGeometry.family Q)).neighborSet
      (base (TriangleGeometry.family Q) v.type)) =
    Nat.card ((graph (TriangleGeometry.family Q)).neighborSet
      (g • base (TriangleGeometry.family Q) v.type)) at he
  rw [hg] at he
  rw [←he,card_neighbor_base]
  have ht : ((TriangleGeometry.family Q (!v.type)).subgroupOf
      (TriangleGeometry.family Q v.type)).index =
      (Q.tits.B.subgroupOf (TriangleGeometry.family Q v.type)).index := by
    change (TriangleGeometry.family Q (!v.type)).relIndex (TriangleGeometry.family Q v.type) = _
    cases hv : v.type
    · change (Q.tits.standardParabolic {Q.simple 1}).relIndex
        (Q.tits.standardParabolic {Q.simple 0}) = _
      rw [←inf_relIndex_left,Q.standard_intersection]
      rfl
    · change (Q.tits.standardParabolic {Q.simple 0}).relIndex
        (Q.tits.standardParabolic {Q.simple 1}) = _
      rw [←inf_relIndex_right,Q.standard_intersection]
      rfl
  rw [ht]
  change (Q.tits.B.subgroupOf (Q.tits.standardParabolic {Q.simple (if v.type then 1 else 0)})).index = _
  rw [singleton_parabolic_root_index Q split,root_card Q e h split hm i hi,Nat.add_comm]

/-- The projective-plane axioms follow from rotation three and the actual root orders. -/
@[instance_reducible] def original_plane :
    ProjectivePlane (Point (TriangleGeometry.family Q)) (Line (TriangleGeometry.family Q)) :=
  projectivePlaneOfGeometry (TriangleGeometry.family Q) (A2Source.MarkedPlane.generate Q)
    (TriangleGeometry.uniqueGeodesicsBelow Q hm) (TriangleGeometry.diameter_le_three Q hm)
    (2^n) (by
      obtain ⟨F,hF,hfin,hcard,_⟩ := hi
      exact hcard ▸ (Finite.one_lt_card (α := F)))
    (original_neighbor_card Q e h split hm i hi)

/-- The plane uses the original binary field order. -/
theorem original_plane_order :
    let := original_plane Q e h split hm i hi
    ProjectivePlane.order (Point (TriangleGeometry.family Q)) (Line (TriangleGeometry.family Q)) = 2^n := by
  let := original_plane Q e h split hm i hi
  have hc : pointCount (Point (TriangleGeometry.family Q)) (A2Source.QuotientPlane.axis Q) = 2^n+1 :=
    (Nat.card_congr (pointsOnLineEquivNeighbors (TriangleGeometry.family Q)
      (A2Source.QuotientPlane.axis Q))).trans
      (original_neighbor_card Q e h split hm i hi (A2Source.QuotientPlane.axis Q).val)
  rw [ProjectivePlane.pointCount_eq] at hc
  omega

/-- Each actual complementary radical fixes its entire radius-one neighborhood. -/
theorem original_radical_le_ballKernel (j : Bool) :
    simpleRemainder Q split (if j then 1 else 0) ≤
      ballKernel (TriangleGeometry.family Q) (base (TriangleGeometry.family Q) j) 1 := by
  let F := TriangleGeometry.family Q
  have hV (k : Fin 2) := (odd_linear_regularity Q e h split
    (hm ▸ (by decide : Odd 3)) i hi k).1
  have hcore : simpleRemainder Q split (if j then 1 else 0) = (F j).pCoreIn 2 := by
    apply Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.remainder_eq_parabolic_core
      Q split _ (hV _)
    rintro x ⟨y,hy,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal
      (split.sylow.subtype (split.U_le.trans (Q.tits.B_le_standardParabolic _))) hy
  have hB : (F j).pCoreIn 2 ≤ Q.tits.B := by
    rw [←hcore]
    exact inf_le_left.trans split.U_le
  have hc : (F j).pCoreIn 2 ≤ F false ⊓ F true := by
    change _ ≤ Q.tits.standardParabolic {Q.simple 0} ⊓ Q.tits.standardParabolic {Q.simple 1}
    rw [Q.standard_intersection]
    exact hB
  have hs (k : Bool) : stabilizer F (base F k) = F k := CosetGeometry.stabilizer_base F k
  have hadj : (graph F).Adj (base F j) (base F (!j)) :=
    ⟨by change j ≠ !j; cases j <;> decide,CosetGeometry.incident_base _ _ _⟩
  rw [hcore,ballKernel_one_eq_map_normalCore F hadj,hs j,hs (!j)]
  apply map_mono
  apply normal_le_normalCore.mpr
  intro a ha
  have hh : (a : X ⧸ Q.D) ∈ (F j).pCoreIn 2 := mem_map_of_mem (F j).subtype ha
  have hit := hc hh
  change (a : X ⧸ Q.D) ∈ F j ⊓ F (!j)
  cases j
  · exact ⟨hit.1,hit.2⟩
  · exact ⟨hit.2,hit.1⟩

/-- The literal middle root consists of elations with the marked incident center and axis. -/
theorem original_intersection_isElation (z : X ⧸ Q.D)
    (hz : z ∈ simpleRemainder Q split 1 ⊓ simpleRemainder Q split 0) (hne : z ≠ 1) :
    IsElation z (A2Source.QuotientPlane.centerPoint Q) (A2Source.QuotientPlane.axis Q) := by
  refine ⟨⟨Bool.false_ne_true,CosetGeometry.incident_base _ _ _⟩,?_,?_,?_⟩
  · intro p hp
    apply Subtype.ext
    exact original_radical_le_ballKernel Q e h split hm i hi true hz.1 p.val
      ((mem_ball_one _ _ _).mpr (Or.inl hp.symm))
  · intro l hl
    apply Subtype.ext
    exact original_radical_le_ballKernel Q e h split hm i hi false hz.2 l.val
      ((mem_ball_one _ _ _).mpr (Or.inl hl))
  · have hmove : ∃ v : Vertex (TriangleGeometry.family Q), z • v ≠ v := by
      by_contra! hall
      exact hne (faithfulSMul_iff.mp (A2Source.MarkedPlane.faithful Q e h) _ hall)
    obtain ⟨⟨j,v⟩,hv⟩ := hmove
    cases j
    · exact Or.inl ⟨⟨⟨false,v⟩,rfl⟩,fun he => hv (congrArg Subtype.val he)⟩
    · exact Or.inr ⟨⟨⟨true,v⟩,rfl⟩,fun he => hv (congrArg Subtype.val he)⟩

/-- The whole radical, including the binary case, acts by elations on the same axis. -/
theorem original_radical_isElation (x : simpleRemainder Q split 1) (hx : x ≠ 1) :
    ∃ C : Point (TriangleGeometry.family Q),
      IsElation (x : X ⧸ Q.D) C (A2Source.QuotientPlane.axis Q) := by
  have hV (k : Fin 2) := (odd_linear_regularity Q e h split
    (hm ▸ (by decide : Odd 3)) i hi k).1
  have hE (k : Fin 2) := elementary_root_of_linear_factor Q e h split k
    (original_linear_factors Q e h split hm i hi k)
  obtain ⟨F,hF,hfin,hchar,_,μ,_,_⟩ := original_natural_cores Q e h split hm i hi 1
  let := Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.remainder_elementary
    Q split hm hV hE 1
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨c,hc⟩ := Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.radical_natural_coordinates
    Q split hm hV hE 1 μ
  have hI : simpleRemainder Q split 1 ⊓ simpleRemainder Q split 0 ≠ ⊥ := by
    rw [Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.radical_intersection
      Q split hm 1 0 (by decide)]
    exact rootAt_ne_bot Q split _ _
  obtain ⟨z,hz,hz1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
  change z ≠ 1 at hz1
  let zV : simpleRemainder Q split 1 := ⟨z,hz.1⟩
  have hnonzero (v : simpleRemainder Q split 1) (hv : v ≠ 1) : c (Additive.ofMul v) ≠ 0 := by
    intro he
    exact hv (congrArg Additive.toMul (c.injective (he.trans c.map_zero.symm)))
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq F (c (Additive.ofMul zV)) (c (Additive.ofMul x))
    (hnonzero zV (fun he => hz1 (congrArg Subtype.val he))) (hnonzero x hx)
  let r := μ.symm g
  have heq : radicalAction Q split 1 (hV 1) r zV = x := by
    apply Additive.ofMul.injective
    apply c.injective
    change c (Representation.elementaryRepresentation (p := 2)
      (radicalAction Q split 1 (hV 1)) r (Additive.ofMul zV)) = _
    rw [hc,show μ r = g from μ.apply_symm_apply g]
    exact hg
  have hconj : (r : X ⧸ Q.D)*z*(r : X ⧸ Q.D)⁻¹ = (x : X ⧸ Q.D) :=
    (radicalAction_apply Q split 1 (hV 1) r zV).symm.trans (congrArg Subtype.val heq)
  have haxis : (r : X ⧸ Q.D) • A2Source.QuotientPlane.axis Q = A2Source.QuotientPlane.axis Q := by
    apply Subtype.ext
    change (r : X ⧸ Q.D) • base (TriangleGeometry.family Q) true = _
    apply MulAction.mem_stabilizer_iff.mp
    rw [CosetGeometry.stabilizer_base]
    exact rankOne_le_parabolic Q split 1 r.property
  have hel := (original_intersection_isElation Q e h split hm i hi z hz hz1).conjugate (r : X ⧸ Q.D)
  rw [hconj,haxis] at hel
  exact ⟨_,hel⟩

omit e h hm i hi in
/-- The radical fixes the marked infinity line as a line. -/
theorem radical_fixes_axis (a : simpleRemainder Q split 1) :
    (a : X ⧸ Q.D) • A2Source.QuotientPlane.axis Q = A2Source.QuotientPlane.axis Q := by
  apply Subtype.ext
  change (a : X ⧸ Q.D) • base (TriangleGeometry.family Q) true = _
  apply MulAction.mem_stabilizer_iff.mp
  rw [CosetGeometry.stabilizer_base]
  exact (split.U_le.trans (Q.tits.B_le_standardParabolic _)) a.property.1

/-- The whole actual radical acts regularly on all affine points of the same
quotient plane. The equivalence is evaluation at the chosen affine origin. -/
def original_affineOrbitEquiv
    (o : {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q}) :
    simpleRemainder Q split 1 ≃
      {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q} :=
  let := original_plane Q e h split hm i hi
  affineOrbitEquiv (simpleRemainder Q split 1) (A2Source.QuotientPlane.axis Q)
    (radical_fixes_axis Q split) o (original_radical_isElation Q e h split hm i hi) (by
      rw [original_plane_order Q e h split hm i hi,
        Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.remainder_card Q split hm,
        root_card Q e h split hm i hi])

/-- Evaluation preserves the literal quotient action, independently of coordinate choices. -/
theorem original_affineOrbitEquiv_apply
    (o : {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q})
    (a : simpleRemainder Q split 1) :
    (original_affineOrbitEquiv Q e h split hm i hi o a).val = (a : X ⧸ Q.D) • o.val := rfl

/-- An affine origin exists in the constructed plane, without a new source premise. -/
theorem original_affine_origin :
    Nonempty {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q} := by
  let := original_plane Q e h split hm i hi
  obtain ⟨o,ho⟩ := Nondegenerate.exists_point (P := Point (TriangleGeometry.family Q))
    (A2Source.QuotientPlane.axis Q)
  exact ⟨⟨o,ho⟩⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TriangleStructure
