module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.MovedDomain
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.SuzukiRecognition
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.JankoOneExclusion
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Eleven
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen
public import CFSG.Quasithin.ChapterK.Section01To04.OddCharacteristic.Coincidences
public import Theory.SpecificGroups.SL2.SmallOddComparisons

/-!
# Recognition of the original nonlinear moved module

The literal moved automizer has the Chapter K source hypotheses proved in
`MovedDomain`. Its component has the original L/O₂(L) marking. Intersecting
the complete nonnormal component catalogue with the genuine cubic module
classifications leaves the even PSL₂ and Suzuki rows: odd prime-field PSL₂
reduces to A₅ or SL₃(2), and J₁ contradicts the cubic displacement bound.

The rank-one recognition theorems supply actual binary intertwiners. They
are transported back through the original component projection and the
literal quotient map, preserving one marking in each row. The previously
proved central-kernel vanishing supplies whole-W coordinates; the natural
row retains its specified centralizer denominator. Excluding the actual A₅
isomorphism removes the orthogonal half-degree-one endpoint.

This proves `MovedRecognitionAt` from its exact hypotheses. The independent
separated-seed implication remains with qt-d-10-nona5-central-hall-orders.
Source: Aschbacher--Smith B.4.2/B.4.5, K.2--K.4 and 10.1.1--2,
printed pp.86--87,453--457,741--742.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
open ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion

private theorem odd_prime_parameters
    {A V : Type*} [Group A] [Finite A] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) A V} {S : Subgroup A}
    (h : ChapterK.RankOne.SourceHypotheses ρ S) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (S ⧸ center S) 2 p) : p = 5 ∨ p = 7 := by
  have hp3 : p ≠ 3 := by
    intro hp3
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
    let := h.quasisimple
    let : Group.IsPerfect (S ⧸ center S) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center S))
    let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three
      (hc.trans hp3) inferInstance
  have hlo : 4 ≤ p ^ 1 := by
    obtain ⟨k,hk⟩ := ho
    have := hp.two_le
    simp only [pow_one]
    omega
  rcases h with ⟨hsq,hfit,hquasi,hfaith,hirr,hratio⟩
  subst S
  let h : SourceAction ρ :=
    ⟨hsq,hquasi,hfaith,hirr⟩
  have hhi := RankOneSize.source_field_order_le_twentyFive
    ρ h hp ho (Or.inl rfl : 1 = 1 ∨ 1 = 2) hlo (by simpa only [pow_one] using hm) hratio
  have hcases : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 := by
    norm_num only [pow_one] at hlo hhi
    interval_cases p
    all_goals norm_num at hp
    all_goals norm_num
  rcases hcases with h5 | h7 | h11 | h13 | h17 | h19 | h23
  · exact Or.inl h5
  · exact Or.inr h7
  · subst p
    exact False.elim ((not_lt_of_ge hratio)
      (RankOneSmall.Eleven.two_lt_cubicRatio ρ h hm))
  · subst p
    exact False.elim ((not_lt_of_ge hratio)
      (RankOneSmall.source_prime_exclusion ρ h (Or.inl rfl) hm))
  · subst p
    have hd := RankOneSmall.source_seventeen_degree_eq_eight ρ h hm hratio
    exact False.elim ((not_lt_of_ge hratio)
      (RankOneSmall.Seventeen.two_lt_cubicRatio_of_degree_le_eight ρ h hm hd.le))
  · subst p
    exact False.elim ((not_lt_of_ge hratio)
      (RankOneSmall.source_prime_exclusion ρ h (Or.inr (Or.inl rfl)) hm))
  · subst p
    exact False.elim ((not_lt_of_ge hratio)
      (RankOneSmall.source_prime_exclusion ρ h (Or.inr (Or.inr rfl)) hm))

private theorem not_janko_source
    {A V : Type*} [Group A] [Finite A] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) A V} {S : Subgroup A}
    (h : ChapterK.RankOne.SourceHypotheses ρ S) (e : S ⧸ center S ≃* Janko1.Model) : False := by
  rcases h.fitting with rfl
  exact ChapterK.SporadicCatalogue.sourceExclusion_j1 ρ
    ⟨h.sqtk,h.quasisimple,h.faithful,h.irreducible,h.smallCubic⟩ ⟨e⟩

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} (c : Context D H B) (geometry : ModuleGeometry D)
attribute [local instance] localCarrierNormal localCarrierElementary localCarrierFiniteDimensional

/-- The central quotient of the actual component image is the original L/O₂(L). -/
def movedComponentCentralEquiv :
    ((movedComponentProjection D geometry).range ⧸
      center (movedComponentProjection D geometry).range) ≃* (L ⧸ pCore 2 L) := by
  let := movedComponent_simple D c geometry
  let := D.quasisimple
  let : IsQuasisimple (movedComponentProjection D geometry).range :=
    IsQuasisimple.of_mulEquiv (movedComponentEquiv D c geometry)
  exact ((QuotientGroup.quotientMulEquivOfEq
    (center_eq_bot_of_simple_perfect (G := (movedComponentProjection D geometry).range))).trans
    QuotientGroup.quotientBot).trans (movedComponentEquiv D c geometry).symm

/-- Transport a recognized component action through the literal original quotient map. -/
def sectionOfMovedModel {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) A V)
    (e : (movedComponentProjection D geometry).range ≃* A)
    (E : movedSpace D ≃ₗ[ZMod 2] V)
    (hi : ∀ (g : (movedComponentProjection D geometry).range) (v : movedSpace D),
      E (movedAction D (g : movedActor D) v) = σ (e g) (E v)) :
    BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (σ.comp (((movedComponentEquiv D c geometry).trans e).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 L)))) where
  section_le := (movedComponentSection D geometry).section_le
  kernel_le := bot_le
  normalized := (movedComponentSection D geometry).normalized
  coordinates := E.toAddEquiv.toMultiplicative.toMonoidHom.comp
    (movedComponentSection D geometry).coordinates
  onto := E.toAddEquiv.toMultiplicative.surjective.comp
    (movedComponentSection D geometry).onto
  kernel_eq := by
    ext w
    change E ((movedComponentSection D geometry).coordinates w).toAdd = 0 ↔ _
    rw [E.map_eq_zero_iff]
    exact (movedComponentSection D geometry).coordinates_eq_one_iff w
  equivariant l w := by
    change E ((movedComponentSection D geometry).coordinates _).toAdd = _
    rw [(movedComponentSection D geometry).equivariant]
    exact hi ((movedComponentProjection D geometry).rangeRestrict l)
      ((movedComponentSection D geometry).coordinates w).toAdd


local instance recognitionBinaryFixed (n : ℕ) :
    Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.fixedField n) := ZMod.algebra _ 2
local instance recognitionBinaryHermitian (n : ℕ) [NeZero n] :
    Module (ZMod 2) (OrthogonalFourMinus.FiniteModel.Space n) :=
  Module.compHom _ (algebraMap (ZMod 2) (OrthogonalFourMinus.FiniteModel.fixedField n))

/-- The even rank-one source classification on the actual moved automizer.
The excluded A₅ endpoint enforces the original orthogonal field bound. -/
theorem moduleRow_of_even_model (c : Context D H B) (geometry : ModuleGeometry D) (hmin : MovedMinimal D)
    (hlocal : SourceLocalModuleCubicBound D) {r : ℕ} (hr : 2 ≤ r)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ r)) : ModuleRow D := by
  let : Algebra (ZMod 2) (GaloisField 2 r) := ZMod.algebra _ 2
  let : Fintype (GaloisField 2 r) := Fintype.ofFinite _
  let S := (movedComponentProjection D geometry).range
  have h := movedAction_sourceHypotheses D c geometry hmin hlocal
  obtain ⟨F,_,_,hc,⟨eq⟩⟩ := hm.of_mulEquiv (movedComponentEquiv D c geometry).symm
  let : Fintype F := Fintype.ofFinite F
  have hcard : Nat.card (GaloisField 2 r) = 2 ^ r := GaloisField.card 2 r (by omega)
  let f : F ≃+* GaloisField 2 r := FiniteField.ringEquivOfCardEq (by
    simpa only [Fintype.card_eq_nat_card] using hc.trans hcard.symm)
  let e : S ≃* SL(2,GaloisField 2 r) :=
    (eq.trans (Atlas.fieldEquivPSL 2 f)).trans (Theory.PSL2.sl2QuotientEquiv _).symm
  obtain ⟨_,hn | ⟨n,_,_,hn,_,⟨M⟩⟩⟩ := h.binary_recognition e r hr hcard
  · obtain ⟨M⟩ := hn.2
    let coords := sectionOfMovedModel D c geometry SL2.BinarySmall.natural
      M.groupEquiv M.coordinates M.intertwines
    exact .natural r (by omega) ((movedComponentEquiv D c geometry).trans M.groupEquiv)
      ⟨coords.replaceKernel (sourceMovedFixed D)
        (movedFixed_eq_bot_of_central_hstar D c geometry).symm⟩
  · let : NeZero n := ⟨hn.ne'⟩
    have hn1 : n ≠ 1 := by
      intro he
      have he1 : Nonempty ((L ⧸ pCore 2 L) ≃*
          SL(2,OrthogonalFourMinus.FiniteModel.Field 1)) := by
        exact (congrArg (fun k : ℕ => Nonempty ((L ⧸ pCore 2 L) ≃*
          SL(2,OrthogonalFourMinus.FiniteModel.Field k))) he).mp
          ⟨(movedComponentEquiv D c geometry).trans M.groupEquiv⟩
      exact c.not_a5 ⟨he1.some.trans ((Theory.PSL2.sl2QuotientEquiv _).trans
        Atlas.Comparisons.Exceptional.psl2FourEquivAlt5)⟩
    exact .orthogonal n (by omega) ((movedComponentEquiv D c geometry).trans M.groupEquiv)
      ⟨sectionOfMovedModel D c geometry (SL2.BinarySmall.hermitian n)
        M.groupEquiv M.coordinates M.intertwines⟩

/-- Suzuki recognition retains its actual matrix marking and supplies whole-W
coordinates through the proved original central kernel. -/
theorem moduleRow_of_suzuki_model (c : Context D H B) (geometry : ModuleGeometry D) (hmin : MovedMinimal D)
    (hlocal : SourceLocalModuleCubicBound D) {m : ℕ} (hm : 1 ≤ m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : ModuleRow D := by
  have h := movedAction_sourceHypotheses D c geometry hmin hlocal
  let M := h.suzukiModel hm ((movedComponentCentralEquiv D c geometry).trans e)
  exact .suzuki m (by omega) ((movedComponentEquiv D c geometry).trans M.groupEquiv)
    ⟨sectionOfMovedModel D c geometry (SuzukiNatural.natural m)
      M.groupEquiv M.coordinates M.intertwines⟩

/-- Odd prime-field PSL₂ rows leave only A₅ and SL₃(2), both excluded by the
original branch hypotheses. The bound used is cubic, with threshold two. -/
theorem not_odd_prime_model (c : Context D H B) (geometry : ModuleGeometry D) (hmin : MovedMinimal D)
    (hlocal : SourceLocalModuleCubicBound D)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p) : False := by
  have h := movedAction_sourceHypotheses D c geometry hmin hlocal
  have hmc := hm.of_mulEquiv (movedComponentCentralEquiv D c geometry)
  rcases odd_prime_parameters h hp ho hmc with rfl | rfl
  · exact c.not_a5 (ChapterK.OddCharacteristic.altFive_of_psl2_five hm)
  · obtain ⟨e⟩ := ChapterK.OddCharacteristic.psl3Two_of_psl2_seven hm
    exact hnot ⟨e.trans (Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm.trans
      Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two)⟩

/-- J₁ contradicts the original moved automizer's cubic bound, including all
possible ambient outer actions. -/
theorem not_janko_model (c : Context D H B) (geometry : ModuleGeometry D) (hmin : MovedMinimal D)
    (hlocal : SourceLocalModuleCubicBound D)
    (e : (L ⧸ pCore 2 L) ≃* Janko1.Model) : False := by
  exact not_janko_source (movedAction_sourceHypotheses D c geometry hmin hlocal)
    ((movedComponentCentralEquiv D c geometry).trans e)

/-- Exhaustive recognition of the three genuine nonlinear source rows from
its exact published hypotheses, without any further recognition premise. -/
theorem source_movedRecognitionAt : MovedRecognitionAt T := by
  intro L D H B c hnot hmodels hlocal _hfull geometry hmin
  cases hmodels with
  | linear_even r hr hm => exact moduleRow_of_even_model D c geometry hmin hlocal hr hm
  | suzuki m hm he => exact moduleRow_of_suzuki_model D c geometry hmin hlocal hm he.some
  | linear_prime p hp ho hm =>
    exact (not_odd_prime_model D c geometry hmin hlocal hnot hp ho hm).elim
  | janko he => exact (not_janko_model D c geometry hmin hlocal he.some).elim

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
