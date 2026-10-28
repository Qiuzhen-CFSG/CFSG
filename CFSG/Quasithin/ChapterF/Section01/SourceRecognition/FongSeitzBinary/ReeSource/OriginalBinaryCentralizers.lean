module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.BinaryRadicalBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalFrattiniRadical

/-!
# Binary source centralizers at the original endpoints

The literal endpoint map identifies centralizers in the original two-core
with centralizers in the whole source radical. This equivalence respects
arbitrary original sets and the actual Omega subgroup of the pulled-back
Suzuki root. Its generated-carrier specialization retains the literal Q.q
formula for both endpoints.

Natural linear and binary Suzuki panel markings discharge (6.3) and the
remainder-to-kernel inclusion; HypothesisF11 supplies the self-centralizing
core. The two Frattini-layer estimates then give
|C_V(U₂)| ≤ q_lin⁴ and |C_V(Ω₁(U₂))| ≤ 4 q_lin⁴, together with
4 |C_V(s₂x)| ≤ q_lin⁴ for the actual quintic reflection--involution
product. The existing common-field theorem gives the source bounds 16, 64
and the exact quintic centralizer order 4, retaining its explicit odd-degree
hypothesis and the full Borel-core faithfulness premise.

Source: Fong--Seitz I (1973), (6.1) on printed p.52 and the a=1 argument
on p.53. The proof uses V/Φ(V) and Φ(V)/Φ²(V); it does not identify Φ(V)
with [V,V]. Binary derived-section effectivity, positive-parameter (6.1),
the whole-product support argument in (6.4), and mixed-commutator equality
remain open. Pairing, odd degree, the remaining (6H), all synchronized §10
coordinates and relations, and the final full-model marked comparison
remain in the same source-construction task.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)

/-- The actual endpoint equivalence transports whole-core centralizers of any original set. -/
def originalCoreCentralizerEquiv (A : Set (parabolic L S i)) :
    (pCore 2 (parabolic L S i) ⊓ centralizer A : Subgroup (parabolic L S i)) ≃*
      (simpleRemainder Q split i ⊓ centralizer (endpointMap Q e i '' A) : Subgroup (X ⧸ Q.D)) where
  toFun x := ⟨endpointMap Q e i x.val,
    (originalRadicalEquiv Q e split i hV ⟨x,x.property.1⟩).property,
    mem_centralizer_iff.mpr (by
      rintro _ ⟨a,ha,rfl⟩
      simpa only [map_mul] using congrArg (endpointMap Q e i)
        (mem_centralizer_iff.mp x.property.2 a ha))⟩
  invFun x :=
    let v := (originalRadicalEquiv Q e split i hV).symm ⟨x,x.property.1⟩
    ⟨v.val,v.property,mem_centralizer_iff.mpr (by
      intro a ha
      apply ((Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective)
      change endpointMap Q e i (a*v.val) = endpointMap Q e i (v.val*a)
      rw [map_mul,map_mul]
      have hv : endpointMap Q e i v.val = x :=
        congrArg Subtype.val ((originalRadicalEquiv Q e split i hV).apply_symm_apply ⟨x,x.property.1⟩)
      rw [hv]
      exact mem_centralizer_iff.mp x.property.2 _ ⟨a,ha,rfl⟩)⟩
  left_inv x := by
    apply Subtype.ext
    exact congrArg (fun z : pCore 2 (parabolic L S i) => (z : parabolic L S i))
      ((originalRadicalEquiv Q e split i hV).symm_apply_apply ⟨x,x.property.1⟩)
  right_inv x := by
    apply Subtype.ext
    exact congrArg (fun z : simpleRemainder Q split i => (z : X ⧸ Q.D))
      ((originalRadicalEquiv Q e split i hV).apply_symm_apply ⟨x,x.property.1⟩)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[simp] theorem originalCoreCentralizerEquiv_apply (A : Set (parabolic L S i))
    (v : (pCore 2 (parabolic L S i) ⊓ centralizer A : Subgroup (parabolic L S i))) :
    (originalCoreCentralizerEquiv Q e split i hV A v : X ⧸ Q.D) = endpointMap Q e i v.val := rfl

private theorem original_root_image :
    ((simpleRoot Q split i).comap (endpointMap Q e i)).map (endpointMap Q e i) = simpleRoot Q split i := by
  have hr : (endpointMap Q e i).range = Endpoint Q i := by
    rw [endpointMap,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (endpoint Q e i).surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  rw [map_comap_eq,hr]
  exact inf_eq_right.mpr ((simpleRoot_le Q split i).trans
    (split.U_le.trans (Q.tits.B_le_standardParabolic _)))

private theorem original_root_image_set :
    endpointMap Q e i '' ((simpleRoot Q split i).comap (endpointMap Q e i) : Set (parabolic L S i)) =
      (simpleRoot Q split i : Set (X ⧸ Q.D)) := by
  exact congrArg (fun A : Subgroup (X ⧸ Q.D) => (A : Set (X ⧸ Q.D)))
    (original_root_image Q e split i)

private theorem original_omega_image_set :
    endpointMap Q e i '' (omegaOneAmbient ((simpleRoot Q split i).comap (endpointMap Q e i)) :
      Set (parabolic L S i)) = (omegaOneAmbient (simpleRoot Q split i) : Set (X ⧸ Q.D)) := by
  have hh := map_omegaOneAmbient_injective (endpointMap Q e i)
    ((Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective)
    ((simpleRoot Q split i).comap (endpointMap Q e i))
  rw [original_root_image Q e split i] at hh
  exact congrArg (fun A : Subgroup (X ⧸ Q.D) => (A : Set (X ⧸ Q.D))) hh

variable (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))

/-- The source's actual reflection--central-involution product in the original endpoint. -/
def originalBinaryMover : parabolic L S i :=
  (endpoint Q e i).symm ⟨frattiniMover Q split i 0 μ hB,
    rankOne_le_parabolic Q split i (frattiniMover Q split i 0 μ hB).property⟩

@[simp] theorem originalBinaryMover_endpoint :
    endpointMap Q e i (originalBinaryMover Q e split i μ hB) = frattiniMover Q split i 0 μ hB :=
  congrArg Subtype.val ((endpoint Q e i).apply_symm_apply _)

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  (j : Fin 2) (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))

include e hB ν hC in
/-- Both binary (6.1) estimates on the whole original core, using the genuine source root and Omega. -/
theorem original_binary_source_six_one
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    Nat.card (pCore 2 (parabolic L S i) ⊓
      centralizer ((simpleRoot Q split i).comap (endpointMap Q e i) : Set (parabolic L S i)) :
        Subgroup (parabolic L S i)) ≤ (Nat.card F)^4 ∧
      Nat.card (pCore 2 (parabolic L S i) ⊓
        centralizer (omegaOneAmbient ((simpleRoot Q split i).comap (endpointMap Q e i)) :
          Set (parabolic L S i)) : Subgroup (parabolic L S i)) ≤ 4*(Nat.card F)^4 := by
  let hVi := marked_suzuki_remainder_le_kernel Q split i 0 μ hB
  have hh := binary_source_six_one Q split i hVi μ hB
    (parabolic_core_selfCentralizing Q e h i) hm j hij
    (source_six_three Q split i j 0 μ hB ν T hC hm hij).2
  rw [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)] at hh
  rw [Nat.card_congr (originalCoreCentralizerEquiv Q e split i hVi
    ((simpleRoot Q split i).comap (endpointMap Q e i) : Set (parabolic L S i))).toEquiv,
    original_root_image_set,
    Nat.card_congr (originalCoreCentralizerEquiv Q e split i hVi
      (omegaOneAmbient ((simpleRoot Q split i).comap (endpointMap Q e i)) :
        Set (parabolic L S i))).toEquiv,original_omega_image_set]
  exact hh

include e hB ν hC in
/-- The quintic centralizer bound at the original endpoint, still with independent fields. -/
theorem original_binary_mover_centralizer_weighted_card_le
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    Nat.card (pCore 2 (parabolic L S i) ⊓
      centralizer ({originalBinaryMover Q e split i μ hB} : Set (parabolic L S i)) :
        Subgroup (parabolic L S i)) * 4 ≤ (Nat.card F)^4 := by
  let hVi := marked_suzuki_remainder_le_kernel Q split i 0 μ hB
  have hh := binary_mover_centralizer_weighted_card_le Q split i hVi μ hB
    (parabolic_core_selfCentralizing Q e h i) hm j hij
    (source_six_three Q split i j 0 μ hB ν T hC hm hij).2
  rw [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)] at hh
  rw [Nat.card_congr (originalCoreCentralizerEquiv Q e split i hVi
    ({originalBinaryMover Q e split i μ hB} : Set (parabolic L S i))).toEquiv,
    Set.image_singleton,originalBinaryMover_endpoint]
  exact hh

include e hB ν hC in
/-- The exact order-four centralizer used in the binary argument on p.53. -/
theorem original_binary_mover_centralizer_card
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j) (hF : Nat.card F = 2) :
    Nat.card (pCore 2 (parabolic L S i) ⊓
      centralizer ({originalBinaryMover Q e split i μ hB} : Set (parabolic L S i)) :
        Subgroup (parabolic L S i)) = 4 := by
  let hVi := marked_suzuki_remainder_le_kernel Q split i 0 μ hB
  rw [Nat.card_congr (originalCoreCentralizerEquiv Q e split i hVi
    ({originalBinaryMover Q e split i μ hB} : Set (parabolic L S i))).toEquiv,
    Set.image_singleton,originalBinaryMover_endpoint]
  apply binary_mover_centralizer_card Q split i hVi μ hB
    (parabolic_core_selfCentralizing Q e h i) hm j hij
    (source_six_three Q split i j 0 μ hB ν T hC hm hij).2
  rw [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F),hF]

omit i hV μ hB j ν T hC in
/-- The exact binary (6.1) bounds after the existing common-field theorem,
retaining its explicit odd-degree premise. -/
theorem original_binary_source_six_one_of_odd_degree
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n)
    (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))
    (hcore : Q.tits.B.normalCore = ⊥) :
    Nat.card (pCore 2 (parabolic L S 1) ⊓
      centralizer ((simpleRoot Q split 1).comap (endpointMap Q e 1) : Set (parabolic L S 1)) :
        Subgroup (parabolic L S 1)) ≤ 16 ∧
      Nat.card (pCore 2 (parabolic L S 1) ⊓
        centralizer (omegaOneAmbient ((simpleRoot Q split 1).comap (endpointMap Q e 1)) :
          Set (parabolic L S 1)) : Subgroup (parabolic L S 1)) ≤ 64 := by
  let : NeZero n := ⟨hn.pos.ne'⟩
  have he := ree_common_field_exponent Q split hm n hn 0 ν T hC μ hB
    (UnitarySource.actorReflection Q split) hcore
  have hb := original_binary_source_six_one Q e split 1 μ hB 0 ν T hC h hm (by decide)
  rw [GaloisField.card 2 n hn.pos.ne',he] at hb
  norm_num at hb
  exact hb

omit i hV μ hB j ν T hC in
/-- The preceding common-field theorem discharges the binary linear order from odd degree. -/
theorem original_binary_mover_centralizer_of_odd_degree
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n)
    (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))
    (hcore : Q.tits.B.normalCore = ⊥) :
    Nat.card (pCore 2 (parabolic L S 1) ⊓
      centralizer ({originalBinaryMover Q e split 1 μ hB} : Set (parabolic L S 1)) :
        Subgroup (parabolic L S 1)) = 4 := by
  let : NeZero n := ⟨hn.pos.ne'⟩
  have he := ree_common_field_exponent Q split hm n hn 0 ν T hC μ hB
    (UnitarySource.actorReflection Q split) hcore
  apply original_binary_mover_centralizer_card Q e split 1 μ hB 0 ν T hC h hm (by decide)
  rw [GaloisField.card 2 n hn.pos.ne',he]
  norm_num

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (i : Fin 2)

/-- The whole-core centralizer equivalence retains the literal original quotient map. -/
theorem originalCoreCentralizerEquiv_quotient
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (A : Set (parabolic L S i))
    (v : (pCore 2 (parabolic L S i) ⊓ centralizer A : Subgroup (parabolic L S i))) :
    (originalCoreCentralizerEquiv Q (originalMarkedIso Q) split i hV A v :
      (generated L S) ⧸ Q.D) = Q.q ⟨v,parabolic_le_generated i v.val.property⟩ := by
  rw [originalCoreCentralizerEquiv_apply]
  fin_cases i
  · exact originalMarkedIso_left_apply Q v.val
  · exact originalMarkedIso_right_apply Q v.val

/-- The distinguished quintic element is the image of its literal original representative. -/
theorem originalBinaryMover_quotient
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0))) :
    Q.q ⟨originalBinaryMover Q (originalMarkedIso Q) split i μ hB,
      parabolic_le_generated i (originalBinaryMover Q (originalMarkedIso Q) split i μ hB).property⟩ =
      (frattiniMover Q split i 0 μ hB : (generated L S) ⧸ Q.D) := by
  have he (g : parabolic L S i) : Q.q ⟨g,parabolic_le_generated i g.property⟩ =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) i g := by
    fin_cases i
    · exact (originalMarkedIso_left_apply Q g).symm
    · exact (originalMarkedIso_right_apply Q g).symm
  rw [he,originalBinaryMover_endpoint]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
