module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointComparison
public import Theory.GroupTheory.GeneralizedFitting.SimpleSolvableKernel
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.HighRows.Mathieu
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.OddFields

/-!
# Simple-component rows of the original point-action comparison

A simple source component forces the actual solvable-kernel map to be
injective. Its component restriction is therefore an isomorphism onto the
original offender component, commuting with the original maps. This carries
the complete B.5 component catalogue back to the source quotient.

The catalogue excludes both Mathieu rows of F.6.18. In the corrected
square-field row, a defining prime other than three gives cyclic Sylow
three-subgroups in PSL₂. The B.5 three-rank sieve and actual Sylow bound
then force an incompatible A₅ or SL₃(2) model. The remaining field has nine
elements, and its prescribed involution extension is the actual S₆ model.
Both original quotient maps and the Frobenius action are retained.

`SourceAssembly/PointSimpleComparison` applies this to the original point
span after every rechoice. The remaining component/module exclusions and
outside-centralization endgame are separate obligations.
Source: Aschbacher--Smith 13.2.12, printed p.882; B.5.1 and F.6.18.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open Chapter15.Section03.TerminalRecognition.Intersection
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u v w

variable {D : Type u} {E : Type v} [Group D] [Group E] [Finite D] [Finite E]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) E W} {g : D →* E}
    (c : PointQuotientComparison ρ g)
    (b : QuasisimpleComparison.BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))

include b in
omit [Finite D] [Finite E] in
private theorem bounded_model (e : generalizedFitting D ≃* generalizedFitting (offenderSubgroup ρ)) :
    FFAlternatives.QuasisimpleModel (generalizedFitting D) := by
  cases b.component.comap e with
  | linearTwo F _ _ e => exact .linearTwo F e
  | linearThree F _ e => exact .linearThree F e
  | alternatingSix e => exact .alternatingSix e
  | alternatingSeven e => exact .alternatingSeven e
  | tripleSix e q => exact .tripleSix e q
  | g2DerivedTwo e => exact .g2DerivedTwo e
  | linearFourTwo e => exact .linearFourTwo e

include c in
/-- The component isomorphism is the restriction of the original quotient map. -/
theorem point_simple_component_equiv
    [IsQuasisimple (generalizedFitting D)] [IsSimpleGroup (generalizedFitting D)]
    [Group.IsSolvable g.ker] :
    Function.Injective g ∧
      ∃ e : generalizedFitting D ≃* generalizedFitting (offenderSubgroup ρ),
        ∀ x, ((e x : offenderSubgroup ρ) : E) = g x := by
  have hg := injective_of_simple_fitting_of_solvable_kernel g
  obtain ⟨_,_,a,ha,hact,_⟩ := c.components
  have hi : Function.Injective a := by
    intro x y h
    apply Subtype.ext
    apply hg
    rw [←hact x,←hact y,h]
  exact ⟨hg,MulEquiv.ofBijective a ⟨hi,ha⟩,hact⟩

include c b in
/-- The actual source component inherits the B.5 models when it is simple. -/
theorem point_simple_fitting_model
    [IsQuasisimple (generalizedFitting D)] [IsSimpleGroup (generalizedFitting D)]
    [Group.IsSolvable g.ker] :
    Function.Injective g ∧ FFAlternatives.QuasisimpleModel (generalizedFitting D) := by
  obtain ⟨hg,e,_⟩ := point_simple_component_equiv c
  exact ⟨hg,bounded_model b e⟩

include c b in
/-- F.6.18(13) has an incompatible actual M₁₂ component. -/
theorem point_not_mathieu_component
    [IsQuasisimple (generalizedFitting D)] [Group.IsSolvable g.ker]
    (e : generalizedFitting D ≃* Sporadic.Mathieu.M12) : False := by
  let := Sporadic.Mathieu.m12_isSimpleGroup
  let : IsSimpleGroup (generalizedFitting D) := e.isSimpleGroup
  exact ComponentRows.HighRows.not_mathieuTwelve_model e (point_simple_fitting_model c b).2

include c b in
/-- F.6.18(12) is excluded after identifying its simple ambient component. -/
theorem point_not_mathieu_ambient
    [IsQuasisimple (generalizedFitting D)] [Group.IsSolvable g.ker]
    (e : D ≃* Sporadic.Mathieu.M12) : False := by
  let := Sporadic.Mathieu.m12_isSimpleGroup
  let : IsSimpleGroup D := e.isSimpleGroup
  have hn : generalizedFitting D ≠ ⊥ := by
    let : IsSimpleGroup (generalizedFitting D ⧸ center (generalizedFitting D)) :=
      IsQuasisimple.simple
    let : Nontrivial (generalizedFitting D) :=
      (QuotientGroup.mk'_surjective (center (generalizedFitting D))).nontrivial
    exact (nontrivial_iff_ne_bot _).mp inferInstance
  have ht := (IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (generalizedFitting D) inferInstance).resolve_left hn
  exact point_not_mathieu_component c b ((MulEquiv.subgroupCongr ht).trans (topEquiv.trans e))

include c b in
/-- Both corrected square-field congruences force the defining prime three. -/
theorem point_square_field_prime {S : Sylow 2 D}
    [Group.IsSolvable g.ker] (r : FSource.SquareFieldExtensionRow S) :
    r.field.prime = 3 := by
  by_contra hp3
  have hm := r.congruence
  have ho : Odd r.field.prime := Nat.odd_iff.mpr (by omega)
  have hc : 9 ≤ Nat.card r.field.Carrier := by
    rw [r.field.card,r.degree]
    have h3 : 3 ≤ r.field.prime := by omega
    nlinarith
  let : IsSimpleGroup PSL(2,r.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup (generalizedFitting D) := r.componentEquiv.isSimpleGroup
  let := r.quasisimple
  have hmodel := (point_simple_fitting_model c b).2
  let P : Sylow 3 PSL(2,r.field.Carrier) := default
  let : Fact r.field.prime.Prime := ⟨r.field.prime_isPrime⟩
  have hr : primeRank 3 (generalizedFitting D) ≤ 1 := by
    rw [primeRank_equiv 3 r.componentEquiv]
    apply P.primeRank_le_one_of_isCyclic
    apply GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card
      r.field.Carrier r.field.card (by omega) 3 (by decide)
    rw [r.field.card]
    exact ((Nat.coprime_primes Nat.prime_three r.field.prime_isPrime).mpr
      (Ne.symm hp3)).pow_right r.field.degree
  have hl := pslTwo_order_ge_360 (show Odd (Nat.card r.field.Carrier) by
    rw [r.field.card]; exact ho.pow) hc
  rcases quasisimple_model_rank_one hr hmodel with ⟨B,⟨eb⟩⟩ | ⟨B,hodd,⟨eb⟩⟩
  · obtain ⟨ea⟩ := odd_linearTwo_binary_alternatingFive B
      ⟨r.field.prime,r.field.degree,r.field.prime_isPrime,ho,r.field.degree_pos,r.field.card⟩
      eb r.componentEquiv
    rw [Nat.card_congr (r.componentEquiv.symm.trans ea).toEquiv,
      nat_card_alternatingGroup] at hl
    norm_num [Nat.factorial] at hl
  · have hs : Nat.card S ≤ 128 := by
      rw [Nat.card_congr r.sylow.some.toEquiv,Nat.card_prod,DihedralGroup.nat_card]
      norm_num [FSource.C]
    obtain ⟨ea⟩ := linearThree_binary_equiv (generalizedFitting D) B hodd eb S hs
    rw [Nat.card_congr (r.componentEquiv.symm.trans ea).toEquiv,Matrix.PSL3Two.card_SL] at hl
    omega

include c b in
/-- The original Frobenius extension has field order nine and ambient model S₆. -/
theorem point_square_field_models {S : Sylow 2 D}
    [Group.IsSolvable g.ker] (r : FSource.SquareFieldExtensionRow S) :
    r.field.prime = 3 ∧ Nat.card r.field.Carrier = 9 ∧
      Nonempty (D ≃* Equiv.Perm (Fin 6)) := by
  have hp := point_square_field_prime c b r
  refine ⟨hp,by rw [r.field.card,r.degree,hp]; decide,?_⟩
  exact ComponentRows.OddFields.fieldRow_nine_equiv_symmetricSix
    (r.toFieldExtension hp) hp S r.sylow.some

include c b in
/-- The original numbered field row is a specialization of the corrected row,
with its actual involution, generation and action unchanged. -/
theorem point_field_extension_models {S : Sylow 2 D}
    [IsQuasisimple (generalizedFitting D)] [Group.IsSolvable g.ker]
    (r : FSource.FieldExtensionRow (D := D))
    (hs : Nonempty (S ≃* (FSource.C 2 × DihedralGroup 4))) :
    r.field.prime = 3 ∧ Nat.card r.field.Carrier = 9 ∧
      Nonempty (D ≃* Equiv.Perm (Fin 6)) := by
  let r' : FSource.SquareFieldExtensionRow S := {
    field := r.field
    degree := r.degree
    congruence := Or.inl r.congruence
    componentEquiv := r.componentEquiv
    quasisimple := inferInstance
    sylow := hs
    automorphism := r.automorphism
    frobenius := r.frobenius
    element := r.element
    involution := r.involution
    outside := r.outside
    generated := r.generated
    action := r.action }
  exact point_square_field_models c b r'

/-- Derived simple-component comparisons on the original quotient map. These
are conclusions for the universal paired-point consumer, not source premises. -/
structure PointSimpleComparison
    {D : Type u} {E : Type v} [Group D] [Group E] [Finite D] [Finite E]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (g : D →* E) : Prop where
  component : ∀ _ : IsSimpleGroup (generalizedFitting D),
    Function.Injective g ∧
      ∃ e : generalizedFitting D ≃* generalizedFitting (offenderSubgroup ρ),
        ∀ x, ((e x : offenderSubgroup ρ) : E) = g x
  models : IsSimpleGroup (generalizedFitting D) →
    FFAlternatives.QuasisimpleModel (generalizedFitting D)
  not_mathieu : ¬ Nonempty (D ≃* Sporadic.Mathieu.M12)
  not_mathieu_component : ¬ Nonempty (generalizedFitting D ≃* Sporadic.Mathieu.M12)
  square_field : ∀ (S : Sylow 2 D) (r : FSource.SquareFieldExtensionRow S),
    r.field.prime = 3 ∧ Nat.card r.field.Carrier = 9 ∧
      Nonempty (D ≃* Equiv.Perm (Fin 6))
  field_extension : ∀ (S : Sylow 2 D) (r : FSource.FieldExtensionRow (D := D)),
    Nonempty (S ≃* (FSource.C 2 × DihedralGroup 4)) →
      r.field.prime = 3 ∧ Nat.card r.field.Carrier = 9 ∧
        Nonempty (D ≃* Equiv.Perm (Fin 6))

include c b in
/-- Construct every simple-component conclusion from the bounded action and
the previously proved comparison of the literal quotient maps. -/
theorem point_simple_comparison
    [IsQuasisimple (generalizedFitting D)] [Group.IsSolvable g.ker] :
    PointSimpleComparison ρ g := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro h
    let := h
    exact point_simple_component_equiv c
  · intro h
    let := h
    exact (point_simple_fitting_model c b).2
  · rintro ⟨e⟩
    exact point_not_mathieu_ambient c b e
  · rintro ⟨e⟩
    exact point_not_mathieu_component c b e
  · intro S r
    exact point_square_field_models c b r
  · intro S r hs
    exact point_field_extension_models c b r hs

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
