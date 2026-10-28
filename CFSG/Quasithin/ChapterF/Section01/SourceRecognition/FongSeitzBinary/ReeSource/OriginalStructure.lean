module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalSixHAssembly

/-!
# Intrinsic center and third-commutator identities on the original source

The injective original endpoint marking pulls [Φ(V),V]=Z(V) back to
the actual second two-core. Agreement of the endpoint and full-overlap
Sylow maps identifies its embedded center with the center of the original
Sylow subgroup. This center is elementary abelian of order q, including
q=2. No quotient-image equality is left as an assumption.
Chapter12SixH applies all three results to the literal selected pair and
Preparation, alongside the source-constructed ReeSixHData.
Source: Fong--Seitz I (1973), (6H)(f,g), pp.51,55.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

include e split ν hC μ hB hn in
/-- The original two-core's third commutator is its full center. -/
theorem original_source_radical_third_eq_center
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    ⁅frattini (pCore 2 (parabolic L S 1)),(⊤ : Subgroup (pCore 2 (parabolic L S 1)))⁆ =
      center (pCore 2 (parabolic L S 1)) := by
  let j := (endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype
  have hj : Function.Injective j :=
    ((Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective).comp
      (pCore 2 (parabolic L S 1)).subtype_injective
  apply map_injective hj
  rw [commutator_comm]
  exact (original_source_radical_third_image Q e split n hn m ν T hC μ hB h hm).trans
    (original_source_radical_center_image Q e split n hn m ν T hC μ hB h hm).symm

include e split ν hC μ hB hn in
/-- The full original Sylow and second two-core have the same ambient center. -/
theorem original_source_sylow_center_eq_radical_center
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (center S).map S.subtype =
      (center (pCore 2 (parabolic L S 1))).map
        ((parabolic L S 1).subtype.comp (pCore 2 (parabolic L S 1)).subtype) := by
  let i := inclusion (show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left)
  have hs : (endpointMap Q e 1).comp i = sylowMap Q e h := by
    ext s
    exact endpoint_sylow Q e h 1 s
  have he : (center S).map i =
      (center (pCore 2 (parabolic L S 1))).map (pCore 2 (parabolic L S 1)).subtype := by
    apply map_injective (f := endpointMap Q e 1)
      ((Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective)
    rw [map_map,map_map,hs]
    exact (original_source_sylow_center_image Q e split n hn m ν T hC μ hB h hm).trans
      (original_source_radical_center_image Q e split n hn m ν T hC μ hB h hm).symm
  have hh := congrArg (Subgroup.map (parabolic L S 1).subtype) he
  rw [map_map,map_map] at hh
  exact hh

include e split ν hC μ hB hn in
/-- The actual original two-core center is elementary abelian of order q. -/
theorem original_source_radical_center_data
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    IsElementaryAbelian 2 (center (pCore 2 (parabolic L S 1))) ∧
      Nat.card (center (pCore 2 (parabolic L S 1))) = 2^(2*m+1) := by
  let R := pCore 2 (parabolic L S 1)
  have hle : center R ≤ frattini R := by
    rw [←original_source_radical_third_eq_center Q e split n hn m ν T hC μ hB h hm]
    exact commutator_le_left _ _
  let : IsElementaryAbelian 2 (frattini R) :=
    (original_source_radical_frattini_data Q e split n hn m ν T hC μ hB h hm).1
  refine ⟨IsElementaryAbelian.of_injective (inclusion hle) (inclusion_injective hle),?_⟩
  let j := (endpointMap Q e 1).comp R.subtype
  have hj : Function.Injective j :=
    ((Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective).comp R.subtype_injective
  rw [←card_map_of_injective (K := center R) hj,
    original_source_radical_center_image Q e split n hn m ν T hC μ hB h hm]
  let a := (MulAut.conj (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D)).symm
  have he : (simpleRoot Q split 1).map a.toMonoidHom =
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) := by
    simp only [rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl
  rw [←he,←map_omegaOneAmbient_injective a.toMonoidHom a.injective,
    card_map_of_injective a.injective]
  exact suzukiOmega_card Q split 1 m μ hB

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
