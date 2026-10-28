module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointSimpleComparison
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.HighRows.Components
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.HighRows.FullActor
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.SpecificGroups.SU3.BinaryG2Comparison
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.SU3.Quasisimplicity
/-!
# The degree-three rows of the original point-action comparison

The source component can have a cubic center, so its solvable-kernel map
is not initially assumed injective. In each degree-three row the full
center has order dividing three. A defining-prime cube therefore survives
the central quotient comparison unless that prime is three. The bounded
B.5 component orders exclude every other odd prime cube.

At prime three the original special or projective unitary model is actually
G₂(2)′. Its simplicity makes the original quotient map injective. The full
corrected B.5 action constructs an embedding of G₂(2) in the offender actor:
row (10) is too small, while row (11) has exactly the required order, so
this embedding gives an actual ambient isomorphism. The graph witness and
both original quotient projections remain available to the consumer.

The action adapter below uses the legacy contract only after excluding
its triple-six constructor by order. Thus it neither assumes nor derives
the obsolete one-dimensional offender assertion for the cubic cover.
`SourceAssembly/PointDegreeThree` applies all deductions after every original
rechoice. Cubic covers and the remaining module/endgame arguments are still
needed for outside-centralization.
Source: Aschbacher--Smith 13.2.12, printed p.882; B.5.1 and F.6.18(10),(11).
The exceptional isomorphism retains the imported Fong/ATLAS attribution.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open Chapter15.Section03.TerminalRecognition.Intersection
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

private theorem centerless {A : Type*} [Group A] [IsSimpleGroup A] [Group.IsPerfect A] :
    center A = ⊥ := by
  rcases (inferInstance : (center A).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp h)).elim

private theorem degree_center {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (h : FSource.DegreeThree p A) :
    Nat.card (center A) ∣ 3 := by
  cases h with
  | linear F hc hs e =>
    rw [Nat.card_congr (centerCongr e).toEquiv]
    exact Matrix.SL3.card_center_dvd_three F
  | projectiveLinear F hc hs e =>
    let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup A := e.isSimpleGroup
    rw [centerless,card_bot]
    exact one_dvd _
  | unitary F J hc hf hs e =>
    let : Fact p.Prime := ⟨hp⟩
    have hfixed : Nat.card {x : F // J.conj x = x} = p := by
      simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
        J.conj p 1 (by decide) (by simpa using hc) (by simpa using hf)
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      BenderSuzuki.External.huppert_II_10_13 J p hp2 hc hfixed
    let : Group.IsPerfect J.specialSubgroup := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let : Group.IsPerfect (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Group.IsPerfect.ofSurjective J.specialToProjective_surjective
    rw [Nat.card_congr (centerCongr e).toEquiv,
      ←J.specialToProjective_ker_eq_center centerless]
    exact J.card_specialToProjective_ker_dvd_three
  | projectiveUnitary F J hc hf hs e =>
    let : Fact p.Prime := ⟨hp⟩
    have hfixed : Nat.card {x : F // J.conj x = x} = p := by
      simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
        J.conj p 1 (by decide) (by simpa using hc) (by simpa using hf)
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      BenderSuzuki.External.huppert_II_10_13 J p hp2 hc hfixed
    let : IsSimpleGroup A := e.isSimpleGroup
    rw [centerless,card_bot]
    exact one_dvd _

private theorem cube_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ^ 3 ∣ 60480) : p = 3 := by
  have hd' : p ∣ 2^6 * 3^3 * 5 * 7 := (dvd_pow_self p (by decide)).trans hd
  have hdiv : p ∣ 2 * 3 * 5 * 7 := by
    rcases hp.dvd_mul.mp hd' with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · exact (hp.dvd_of_dvd_pow h).trans (by decide : 2 ∣ 2*3*5*7)
        · exact (hp.dvd_of_dvd_pow h).trans (by decide : 3 ∣ 2*3*5*7)
      · exact h.trans (by decide : 5 ∣ 2*3*5*7)
    · exact h.trans (by decide : 7 ∣ 2*3*5*7)
  have he : ((p = 2 ∨ p = 3) ∨ p = 5) ∨ p = 7 := by
    simpa only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
      Nat.prime_dvd_prime_iff_eq hp Nat.prime_three,
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)] using hdiv
  rcases he with ((h | h) | h) | h
  · exact (hp2 h).elim
  · exact h
  · subst p; norm_num at hd
  · subst p; norm_num at hd

private theorem bounded_cube_prime {A : Type*} [Group A]
    (b : QuasisimpleComparison.BoundedQuasisimpleModel A)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p^3 ∣ Nat.card A) : p = 3 := by
  apply cube_prime hp hp2
  cases b with
  | linearTwo F hlo hhi e =>
    rw [Nat.card_congr e.toEquiv] at hd
    exact (linearTwo_no_odd_prime_cube F hhi hp hp2 hd).elim
  | linearThree F hhi e =>
    have hc : Nat.card A = Nat.card F.Carrier ^ 3 *
        (Nat.card F.Carrier ^ 3 - 1) * (Nat.card F.Carrier ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv,
        Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(3,F.Carrier)),
        Atlas.ExceptionalSupport.card_sl_center,Fintype.card_fin]
      exact Matrix.PSL3.LinearThree.card_projective_mul_scalar F.Carrier
    rw [hc,F.card_eq] at hd
    have hpos := F.degree_pos
    interval_cases hh : F.degree <;> norm_num [hh] at hd ⊢
    · exact hd.trans (by decide)
    · exact hd
  | alternatingSix e =>
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
    exact hd.trans (by decide)
  | alternatingSeven e =>
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
    exact hd.trans (by decide)
  | tripleSix ez eq =>
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center A),
      Nat.card_congr ez.toEquiv,Nat.card_congr eq.toEquiv,nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
    exact hd.trans (by decide)
  | g2DerivedTwo e =>
    rw [Nat.card_congr e.toEquiv,
      Atlas.G2.LieAutomorphismExtensions.card_binaryDerived] at hd
    exact hd.trans (by decide)
  | linearFourTwo e =>
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 4
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
      Finset.prod_empty, mul_one] at hc
    have hc' : Nat.card SL(4,ZMod 2) = 20160 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(4,ZMod 2)),
        Atlas.ExceptionalSupport.card_sl_center,hc]
      norm_num
    rw [Nat.card_congr e.toEquiv,hc'] at hd
    exact hd.trans (by decide)

private theorem irreducible_legacy_of_not_cover {A W : Type*} [Group A]
    [AddCommGroup W] [Module (ZMod 2) W] {ρ : Representation (ZMod 2) A W}
    {L I : Subgroup A} (hc : Nat.card L ≠ 1080)
    (h : FFAlternatives.ProjectiveLine.IrreducibleActionCase ρ L I) :
    FFAlternatives.IrreducibleActionCase ρ L I := by
  cases h with
  | linearTwo F hg e ho hr => exact .linearTwo F hg e ho hr
  | linearThree F hg e hr => exact .linearThree F hg e hr
  | symplectic F hl hg e hr => exact .symplectic F hl hg e hr
  | symplecticTwo e hr => exact .symplecticTwo e hr
  | g2 F hl hg e ho hr => exact .g2 F hl hg e ho hr
  | g2Two e ho hr => exact .g2Two e ho hr
  | symmetric n hn e ho hr => exact .symmetric n hn e ho hr
  | alternatingSix hg e ho hr => exact .alternatingSix hg e ho hr
  | alternatingSeven hg ht e hd ho hr => exact .alternatingSeven hg ht e hd ho hr
  | tripleSix hg a hr =>
    apply (hc _).elim
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center L),
      Nat.card_congr a.centerEquiv.toEquiv,Nat.card_congr a.quotientEquiv.toEquiv,
      nat_card_alternatingGroup]
    norm_num
  | binaryLinear n hn hg e hr => exact .binaryLinear n hn hg e hr
  | orthogonalSix hg ht e ho hr => exact .orthogonalSix hg ht e ho hr
  | symmetricEight ht e hr => exact .symmetricEight ht e hr
  | exteriorFive hg ht e hd ho hr => exact .exteriorFive hg ht e hd ho hr

private theorem source_contains_g2 {A W : Type*} [Group A]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) A W)
    {L : Subgroup A} (h : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (hc : Nat.card L = 6048) :
    ∃ f : Atlas.G2.Model (ZMod 2) →* A, Function.Injective f := by
  have hcase : FFAlternatives.QuasisimpleActionCase ρ L h.sectionData := by
    cases h.clause_one with
    | irreducible hi hf hr hs he =>
      exact .irreducible hi hf hr (irreducible_legacy_of_not_cover (by omega) hs) he
    | doubleThree F hw e ho hr => exact .doubleThree F hw e ho hr
    | naturalDual n hn hw h => exact .naturalDual n hn hw h
    | repeatedNatural n r hn hp hb hw h => exact .repeatedNatural n r hn hp hb hw h
  let c : FFAlternatives.QuasisimpleSourceConclusion ρ L := {
    sectionData := h.sectionData
    fitting_eq := h.fitting_eq
    clause_one := hcase
    nonsplitting_iff := h.nonsplitting_iff
    clause_two := h.clause_two
    clause_three := h.clause_three
    clause_four := h.clause_four
    clause_five := h.clause_five
    clause_six := h.clause_six }
  exact ComponentRows.HighRows.source_contains_full_g2 ρ c hc

private theorem degree_three_binary {A : Type*} [Group A]
    (h : FSource.DegreeThree 3 A) :
    Nonempty (A ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  cases h with
  | linear F hc hs e => norm_num at hs
  | projectiveLinear F hc hs e => norm_num at hs
  | unitary F J hc hf hs e =>
    exact ⟨(e.trans (MulEquiv.ofBijective J.specialToProjective
      ⟨J.specialToProjective_injective_of_card_nine hc,J.specialToProjective_surjective⟩)).trans
        (J.projectiveEquivBinaryG2Derived hc hf)⟩
  | projectiveUnitary F J hc hf hs e =>
    exact ⟨e.trans (J.projectiveEquivBinaryG2Derived hc hf)⟩

universe u v w
variable {D : Type u} {E : Type v} [Group D] [Group E] [Finite D] [Finite E]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) E W} {g : D →* E}
    (c : PointQuotientComparison ρ g)
    (b : QuasisimpleComparison.BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))

include c b in
/-- The defining prime survives the full central quotient comparison. -/
theorem point_degree_three_prime
    [IsQuasisimple (generalizedFitting D)]
    {p : ℕ} (hp : p.Prime) (hm : p % 8 = 3 ∨ p % 8 = 5)
    (h : FSource.DegreeThree p (generalizedFitting D)) : p = 3 := by
  by_contra hp3
  have hz := degree_center hp (by omega) h
  have hcp : Nat.Coprime (p^3) (Nat.card (center (generalizedFitting D))) :=
    (((Nat.coprime_primes hp Nat.prime_three).mpr hp3).of_dvd_right hz).pow_left 3
  have hd := degreeThree_prime_cube hp h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center (generalizedFitting D))] at hd
  have hquot := hcp.dvd_of_dvd_mul_right hd
  obtain ⟨_,_,_,_,_,e,_⟩ := c.components
  rw [Nat.card_congr e.toEquiv] at hquot
  exact hp3 (bounded_cube_prime b.component hp (by omega)
    (hquot.trans (card_quotient_dvd_card _)))

include c b in
/-- Both degree-three source components are actual G₂(2)′ models; the
solvable-kernel map is consequently injective. -/
theorem point_degree_three_component
    [IsQuasisimple (generalizedFitting D)] [Group.IsSolvable g.ker]
    {p : ℕ} (hp : p.Prime) (hm : p % 8 = 3 ∨ p % 8 = 5)
    (h : FSource.DegreeThree p (generalizedFitting D)) :
    p = 3 ∧ Function.Injective g ∧
      Nonempty (generalizedFitting D ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  have hp3 := point_degree_three_prime c b hp hm h
  obtain ⟨e⟩ := degree_three_binary (hp3 ▸ h)
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) := Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup (generalizedFitting D) := e.isSimpleGroup
  exact ⟨hp3,(point_simple_component_equiv c).1,⟨e⟩⟩

private theorem degree_comap {A B : Type u} [Group A] [Group B]
    (e : A ≃* B) {p : ℕ} (h : FSource.DegreeThree p B) : FSource.DegreeThree p A := by
  cases h with
  | linear F hc hs f => exact .linear F hc hs (e.trans f)
  | projectiveLinear F hc hs f => exact .projectiveLinear F hc hs (e.trans f)
  | unitary F J hc hf hs f => exact .unitary F J hc hf hs (e.trans f)
  | projectiveUnitary F J hc hf hs f => exact .projectiveUnitary F J hc hf hs (e.trans f)

include c b in
private theorem point_full_g2_embedding
    [IsQuasisimple (generalizedFitting D)] [Group.IsSolvable g.ker]
    (e : generalizedFitting D ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ∃ f : Atlas.G2.Model (ZMod 2) →* E, Function.Injective f := by
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) := Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup (generalizedFitting D) := e.isSimpleGroup
  obtain ⟨_,a,_⟩ := point_simple_component_equiv c
  have hc : Nat.card (generalizedFitting (offenderSubgroup ρ)) = 6048 := by
    rw [Nat.card_congr (a.symm.trans e).toEquiv,
      Atlas.G2.LieAutomorphismExtensions.card_binaryDerived]
  obtain ⟨f,hf⟩ := source_contains_g2 _ b.source hc
  exact ⟨(offenderSubgroup ρ).subtype.comp f,Subtype.val_injective.comp hf⟩

include c b in
/-- F.6.18(10) cannot support the original corrected B.5 action. -/
theorem point_not_degree_three_ambient
    [IsQuasisimple (generalizedFitting D)] [Group.IsSolvable g.ker]
    (hg : Function.Surjective g)
    {p : ℕ} (hp : p.Prime) (hm : p % 8 = 3 ∨ p % 8 = 5)
    (h : FSource.DegreeThree p D) (ht : generalizedFitting D = ⊤) : False := by
  let a : generalizedFitting D ≃* D := (MulEquiv.subgroupCongr ht).trans topEquiv
  obtain ⟨_,_,⟨e⟩⟩ := point_degree_three_component c b hp hm (degree_comap a h)
  obtain ⟨f,hf⟩ := point_full_g2_embedding c b e
  have hbound := (Nat.card_le_card_of_injective f hf).trans (Nat.card_le_card_of_surjective g hg)
  rw [Nat.card_congr (a.symm.trans e).toEquiv,
    Atlas.G2.LieAutomorphismExtensions.card_binaryDerived,
    Atlas.G2.LieAutomorphismExtensions.card_binaryFull] at hbound
  omega

include c b in
/-- F.6.18(11) forces the actual full binary G₂ model through the original
quotient isomorphism, retaining the coefficient-graph source witness. -/
theorem point_graph_extension_models
    [IsQuasisimple (generalizedFitting D)] [Group.IsSolvable g.ker]
    (hg : Function.Surjective g) (r : FSource.GraphExtensionRow (D := D)) :
    r.prime = 3 ∧ Function.Injective g ∧
      Nonempty (D ≃* Atlas.G2.Model (ZMod 2)) := by
  obtain ⟨hp,hi,⟨e⟩⟩ := point_degree_three_component c b r.prime_isPrime
    r.congruence r.model.model
  let eg : D ≃* E := MulEquiv.ofBijective g ⟨hi,hg⟩
  obtain ⟨f,hf⟩ := point_full_g2_embedding c b e
  let i := eg.symm.toMonoidHom.comp f
  have hii : Function.Injective i := eg.symm.injective.comp hf
  have hc : Nat.card D = 12096 := by
    rw [←(generalizedFitting D).card_mul_index,
      ComponentRows.HighRows.graphRow_index r,Nat.card_congr e.toEquiv,
      Atlas.G2.LieAutomorphismExtensions.card_binaryDerived]
  have hib : Function.Bijective i := hii.bijective_of_nat_card_le (by
    rw [hc,Atlas.G2.LieAutomorphismExtensions.card_binaryFull])
  exact ⟨hp,hi,⟨(MulEquiv.ofBijective i hib).symm⟩⟩

/-- Derived degree-three conclusions on the original quotient map. Every
field/graph witness is retained by its caller; this record is not a source
classification premise. -/
structure PointDegreeThreeComparison
    {D : Type u} {E : Type v} [Group D] [Group E] [Finite D] [Finite E]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (g : D →* E) : Prop where
  component : ∀ p : ℕ, p.Prime → (p % 8 = 3 ∨ p % 8 = 5) →
    FSource.DegreeThree p (generalizedFitting D) →
      p = 3 ∧ Function.Injective g ∧
        Nonempty (generalizedFitting D ≃* commutator (Atlas.G2.Model (ZMod 2)))
  not_ambient : ∀ p : ℕ, p.Prime → (p % 8 = 3 ∨ p % 8 = 5) →
    FSource.DegreeThree p D → generalizedFitting D = ⊤ → False
  graph_extension : ∀ r : FSource.GraphExtensionRow (D := D),
    r.prime = 3 ∧ Function.Injective g ∧
      Nonempty (D ≃* Atlas.G2.Model (ZMod 2))

include c b in
/-- Apply the complete corrected module clauses to both degree-three rows
on the same solvable-kernel quotient map. -/
theorem point_degree_three_comparison
    [IsQuasisimple (generalizedFitting D)] [Group.IsSolvable g.ker]
    (hg : Function.Surjective g) : PointDegreeThreeComparison ρ g := by
  refine ⟨?_,?_,?_⟩
  · intro p hp hm h
    exact point_degree_three_component c b hp hm h
  · intro p hp hm h ht
    exact point_not_degree_three_ambient c b hg hp hm h ht
  · intro r
    exact point_graph_extension_models c b hg r

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
