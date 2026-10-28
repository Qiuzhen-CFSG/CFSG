module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.ModelExclusionsSporadic
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.ModelExclusionsSource
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Rows
public import Theory.Mathieu.M11.Properties.Order

/-!
The actual source fixed component in the sporadic catalogue. Transport through the literal composite central quotient preserves the ordinary component and its prime-field model. The intrinsic exclusions leave only J₂. The independent fixed-octad M₂₂ producer is supplied by the complete census consumer. Source: Aschbacher–Smith 2.5.19, pp.560–563.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
open ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- In the sporadic catalogue, the actual source prime fixed component
retains only J₂. The eight-fixed-point M₂₂ geometry is the sole independent
model input to this assembly. -/
theorem source_sporadic_quotient_eq_j2
    (height : ∀ (s : _root_.Sporadic.Mathieu.m22DesignAut), orderOf s = 2 →
      s.val ∉ _root_.Sporadic.Mathieu.M22 →
      (_root_.Sporadic.Mathieu.M22OuterCentralizers.fixedPoints s).card = 8 →
      ∀ B : Subgroup (_root_.Sporadic.Mathieu.M22OuterCentralizers.centralizer s),
        ¬ IsComponent (_root_.Sporadic.Mathieu.M22OuterCentralizers.centralizer s) B)
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (eK : K ≃* PSL(2,ZMod p))
    {E : Type*} [Group E] [IsQuasisimple E]
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eKB : K ≃* B) (name : SporadicName) (hj3 : name ≠ .j3)
    (e : (E ⧸ center E) ≃* name.Carrier) : name = .j2 := by
  let : Fact p.Prime := ⟨hp.1⟩
  let : IsSimpleGroup (E ⧸ center E) := IsQuasisimple.simple
  let : IsSimpleGroup name.Carrier := e.symm.isSimpleGroup
  let : Group.IsPerfect name.Carrier :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨hc,haq,hC,⟨eC⟩⟩ := PrimeRows.source_fixed_component_quotient_model
    c hG hempty hgen hb a ha B hB eKB e
  let b := MulAut.centralQuotientAction e a
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  let C := B.map (MulAut.fixedSubgroupMap a b q hc)
  let f : PSL(2,ZMod p) ≃* C := eK.symm.trans eC
  cases name with
  | m11 =>
    exact (source_small_quotient_order_exclusion_of_prime c hG hempty hgen hb hp hp7 eK
      a ha B hB eKB (Or.inl ((Nat.card_congr e.toEquiv).trans
        _root_.Sporadic.Mathieu.m11_order))).elim
  | m12 =>
    exact (source_small_quotient_order_exclusion_of_prime c hG hempty hgen hb hp hp7 eK
      a ha B hB eKB (Or.inr (Or.inl ((Nat.card_congr e.toEquiv).trans
        _root_.Sporadic.Mathieu.m12_order)))).elim
  | m22 => exact (m22_fixed_no_prime_component_of_eight height hp hp7 b haq C hC f).elim
  | m23 => exact (m23_fixed_no_component b haq C hC).elim
  | m24 => exact (m24_fixed_no_prime_component hp hp7 b haq C hC f).elim
  | j2 => rfl
  | j3 => exact (hj3 rfl).elim
  | j4 =>
    let : IsSimpleGroup Janko4.Model := e.symm.isSimpleGroup
    let : Group.IsPerfect Janko4.Model := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact (Chapter16.OtherPreliminaries.JankoFour.involution_fixed_no_component b haq C hC).elim
  | hs =>
    exact (source_hs_quotient_exclusion_of_prime c hG hempty hgen hb hp.1 hp7 eK a ha B hB eKB e).elim
  | he => exact (held_fixed_no_prime_component b haq C hC f.symm).elim
  | ru =>
    let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
    let : Group.IsPerfect Rudvalis.Model := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact (rudvalis_fixed_no_prime_injective hp.1 hp7 b haq
      (C.subtype.comp f.toMonoidHom) (C.subtype_injective.comp f.injective)).elim

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
