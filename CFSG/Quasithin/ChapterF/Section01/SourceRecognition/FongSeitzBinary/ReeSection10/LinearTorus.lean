module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.LinearDerived
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PinnedNatural

/-!
# The actual Suzuki Cartan acting on the linear derived radical

The marked actor detects the entire source Borel. Pinning the supplied
reflection identifies the inverse image of the matrix split torus with
an actual subgroup of H: its elements lie in both opposite Borels inside
the source Levi. The same elements centralize the perpendicular Suzuki
root, and their action on the second axis of V₂ has the exact diagonal
weight a^(2^m). The full source Cartan and R₁ normalize [U_s₁,U_s₁].

LinearLarge uses these literal actors to separate the two factors in the
p.222 graph when q>2. The construction itself includes the trivial binary
torus, without asserting a nontrivial displacement there.
Source: Fong--Seitz II (1974), the discussion after (10.5), printed p.222.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups ReeF4
open scoped Pointwise IsMulCommutative commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

include c in
theorem linearDerived_cartan_normalizes :
    Q.tits.B ⊓ Q.tits.N ≤ normalizer (linearDerived Q split : Set (X ⧸ Q.D)) := by
  have hk := remainder_le_panelKernel_of_marking Q split 0 c.linear c.linearSylow c.linearBorel
    (ReeSource.linear_normalizer_index c.linearSylow)
  intro h hh
  rw [linearDerived,mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (remainder_parabolic_normalizes Q split 0 hk
      (Q.tits.B_le_standardParabolic _ hh.1))]

include c in
theorem linearDerived_rankOne_normalizes :
    rankOne Q split 0 ≤ normalizer (linearDerived Q split : Set (X ⧸ Q.D)) := by
  have hk := remainder_le_panelKernel_of_marking Q split 0 c.linear c.linearSylow c.linearBorel
    (ReeSource.linear_normalizer_index c.linearSylow)
  intro h hh
  rw [linearDerived,mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (remainder_parabolic_normalizes Q split 0 hk
      (rankOne_le_parabolic Q split 0 hh))]

include c in
theorem perpendicular_le_linearDerived_of_shifted
    (h : positiveRoot Q split (.inr 3) ≤ linearDerived Q split) :
    positiveRoot Q split (.inr 1) ≤ linearDerived Q split := by
  let s := (c.reflections 0).val
  have hs := linearDerived_rankOne_normalizes Q split c (c.reflections 0).mem_rankOne
  have hc := comap_mono h (f := (MulAut.conj (s : X ⧸ Q.D)).toMonoidHom)
  change rightConjugate (rootAt Q split 1 (Q.simple 0*Q.simple 1)) (s : X ⧸ Q.D) ≤
    rightConjugate (linearDerived Q split) (s : X ⧸ Q.D) at hc
  rw [rootAt_right Q split 1 _ _ s (c.reflections 0).class_eq,
    rightConjugate_eq_self _ hs] at hc
  exact hc

/-- The full marked Suzuki actor detects the literal source Borel. -/
theorem suzukiActor_mem_borel_iff (r : rankOne Q split 1) :
    suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel r ∈ SuzukiBorelSubgroup m ↔
      (r : X ⧸ Q.D) ∈ Q.tits.B := by
  rw [←suzuki_root_normalizer,←c.suzukiBorel,mem_map_equiv]
  simp only [suzukiActorEquiv_apply,MulEquiv.symm_apply_apply]
  change (⟨r.val,rankOne_le_parabolic Q split 1 r.property⟩ : Endpoint Q 1) ∈
    (quotientBorel Q 1).comap (QuotientGroup.mk' (panelKernel Q 1)) ↔ _
  rw [quotientBorel_comap]
  rfl

/-- The inverse marked actor identifies the full standard torus with its
actual source Cartan subgroup, including the trivial binary torus. -/
def pinnedSuzukiTorus : SuzukiSplitTorus m →* rankOne Q split 1 :=
  (suzukiActorEquiv Q split 1 m (pinnedInput Q split c).suzuki
    (pinnedInput Q split c).suzukiBorel).symm.toMonoidHom.comp (SuzukiSplitTorus m).subtype

@[simp] theorem pinnedSuzukiTorus_model (a : SuzukiSplitTorus m) :
    suzukiActorEquiv Q split 1 m (pinnedInput Q split c).suzuki
      (pinnedInput Q split c).suzukiBorel (pinnedSuzukiTorus Q split c a) = a :=
  (suzukiActorEquiv Q split 1 m (pinnedInput Q split c).suzuki
    (pinnedInput Q split c).suzukiBorel).apply_symm_apply a

theorem pinnedSuzukiTorus_mem_cartan (a : SuzukiSplitTorus m) :
    (pinnedSuzukiTorus Q split c a : X ⧸ Q.D) ∈ Q.tits.B ⊓ Q.tits.N := by
  let c' := pinnedInput Q split c
  let r := pinnedSuzukiTorus Q split c a
  have haB : (a : SuzukiMatrixGroup m) ∈ SuzukiBorelSubgroup m := by
    rw [suzukiBorelSubgroup_eq_sup]
    exact mem_sup_right a.property
  apply UnitarySource.oppositeLevi_inf_two_borels_le_torus Q split 1
  refine ⟨UnitarySource.rootActor_le_oppositeLevi Q split 1 r.property,?_,?_⟩
  · apply (suzukiActor_mem_borel_iff Q split c' r).mp
    rw [pinnedSuzukiTorus_model]
    exact haB
  · rw [borelConjugate_eq _ (c.reflections 1).val (c.reflections 1).class_eq]
    let s : rankOne Q split 1 := ⟨(c.reflections 1).val,(c.reflections 1).mem_rankOne⟩
    change ((s*r*s⁻¹ : rankOne Q split 1) : X ⧸ Q.D) ∈ Q.tits.B
    apply (suzukiActor_mem_borel_iff Q split c' (s*r*s⁻¹)).mp
    rw [map_mul,map_mul,map_inv,pinnedInput_reflection,pinnedSuzukiTorus_model]
    have hw : (suzukiWeyl m)⁻¹ = suzukiWeyl m :=
      inv_eq_of_mul_eq_one_right (suzukiWeyl_sq m)
    rw [hw,suzukiWeyl_conj_splitTorus]
    exact (SuzukiBorelSubgroup m).inv_mem haB

/-- A diagonal torus parameter, retained inside the literal full matrix group. -/
def matrixTorusParameter (a : (CoefficientField m)ˣ) : SuzukiSplitTorus m :=
  ⟨⟨SuzukiTorusGL m a,subset_closure (Or.inr (Or.inl ⟨a,rfl⟩))⟩,
    (mem_suzukiSplitTorus_iff m _).mpr ⟨a,rfl⟩⟩

/-- The torus acts on the second natural coordinate by its exact matrix
weight. This supplies the q>2 displacement in the p.222 argument. -/
theorem pinnedSuzukiTorus_V2_second (a : (CoefficientField m)ˣ)
    (v : (V2Section Q split (pinnedInput Q split c)).numerator) :
    V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
      ((V2Section Q split (pinnedInput Q split c)).numeratorAction
        (pinnedSuzukiTorus Q split c (matrixTorusParameter a)) v))) 1 =
      (a : CoefficientField m)^(2^m) *
        V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk v)) 1 := by
  have h := V2Coordinates_source Q split (pinnedInput Q split c)
    (pinnedSuzukiTorus Q split c (matrixTorusParameter a)) v
  rw [pinnedSuzukiTorus_model] at h
  exact (congrFun h 1).trans (by
    simp [Representation.SuzukiNatural.natural_apply,matrixTorusParameter,
      SuzukiTorusGL,SuzukiTorusMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_four])

/-- The same literal actor centralizes the perpendicular Suzuki root. -/
theorem pinnedSuzukiTorus_centralizes_perpendicular (a : SuzukiSplitTorus m) :
    (pinnedSuzukiTorus Q split c a : X ⧸ Q.D) ∈
      centralizer (positiveRoot Q split (.inr 1) : Set (X ⧸ Q.D)) :=
  rankOne_centralizes_perpendicularSuzuki Q split c (pinnedSuzukiTorus Q split c a).property

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
