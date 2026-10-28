module

public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.HeadFamily
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.CoreIntersection
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ParabolicAction
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ElementaryImage

public import Theory.GroupTheory.NormalizedSupCard
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Theory.SpecificGroups.Triality.TwoLocalCover
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.LocalSections

/-!
# A genuine E-member obstructing the cubic-root head family

At field order two, conjugate the head by the central simple reflection and
conjugate `tailSubgroup ⊔ levi .central` by the arms simple reflection. The
returning head A lies in the original positive Sylow U, while the resulting
local subgroup K has order 192 and positive intersection of order 64.

The proof retains all of E.1.2. Root coordinates give C_U(A) ≤ A and the ambient
two-core is trivial, so the literal tau lies in A ≤ K. Counting proves that
U ∩ K is Sylow in K. The tail is relatively normal with a Levi complement;
at q = 2 this gives a surjection K → S₃ with two-group kernel and nontrivial
actor image. The checked symmetric-three constructor proves the complete
E1 alternative, including its commutator equality and quotient rank one.
Thus K is an actual E_(3f-1)-member at f = 1. Nevertheless, K contains the
Weyl representative `sr 5`, which is outside the original central parabolic.

`not_head_confinement_for_trivial_extension` applies this to the literal
ambient head family and parabolic overgroup. `source_setup_counterexample`
also proves the simple generalized-Fitting and alignment clauses, retaining
the full SQTK hypothesis for an arbitrary class (hence for the full known-
simple class). It does not independently certify SQTK for this model.
`binary_candidate_core_intersection` applies the existing producer to the
literal embedded O₂(K), so its size and normalization clauses are retained.

This calculation obstructs the proposed head-family confinement route. It
does not refute the existential lower obstruction or E.1.14(2), and it does
not change their statements. No whole-normalizer criterion is assumed.

Source conventions: Aschbacher--Smith E.1.2 and E.1.14(2), printed pp.210,214
(`refs/quasithin.pdf`), the latter citing Asc82a Lemma 4.7; the concrete root
and parabolic conventions are those of GLS3 §§2.4--2.6.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction.RelativeConfinement
open Subgroup Theory.GroupTheory
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat _root_.Triality.Standard.PositiveCoordinates
open _root_.Triality.Standard.PositiveCoordinates.SumExchangeData
open _root_.Triality.Standard.RadicalCoordinates
open _root_.Triality.Standard.RadicalCoordinates.LeviCommutators
open _root_.Triality.Standard.Parabolics.CentralRootSquare
open _root_.Triality.Standard.Parabolics.CentralRootSquare.ElementaryImage
open _root_.Triality.Standard.Parabolics.RankOneMatrices
open _root_.Triality.Standard.TwoRank
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction

-- Adapted from HeadNormalizer/RootImages; the original private declarations are unchanged.
private def numbering : rootWeylGroup →* Equiv.Perm (Fin 24) :=
  rootEnumeration.symm.permCongrHom.toMonoidHom.comp rootWeylGroup.subtype

private lemma numbering_generator (i : Fin 4) :
    numbering (rootWeylGenerator i) = DiagramFixed.reflection i := by
  apply Equiv.ext
  intro r
  change rootEnumeration.symm ((typeDRootPairing 2).reflectionPerm
    (typeDSimpleRootIndex 2 i) (rootEnumeration r)) = reflectionTable i r
  rw [← rootEnumeration_reflectionTable, Equiv.symm_apply_apply]

private lemma representative_numbered (w : DihedralGroup 6) (r : Fin 24) :
    (rootRepresentative w).val (rootEnumeration r) =
      rootEnumeration (DiagramFixed.representativeTable w r) := by
  have h : numbering (rootRepresentative w) = DiagramFixed.representative w := by
    cases w <;> simp [rootRepresentative, DiagramFixed.representative, foldedRootReflection,
      map_mul, map_pow, numbering_generator, DiagramFixed.arm]
  have hh := congrFun (congrArg (fun e : Equiv.Perm (Fin 24) => (e : Fin 24 → Fin 24)) h) r
  change rootEnumeration.symm ((rootRepresentative w).val (rootEnumeration r)) = _ at hh
  exact (rootEnumeration.apply_symm_apply _).symm.trans
    (congrArg rootEnumeration (hh.trans (DiagramFixed.representative_apply w r)))

private theorem conjugate_curve (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) (i j : Fin 12)
    (h : DiagramFixed.representativeTable w (positiveIndex i) = positiveIndex j)
    (t : ExtensionField P) :
    splitRepresentative P hp w * curve P i t * (splitRepresentative P hp w)⁻¹ =
      curve P j t := by
  apply Subtype.ext
  change (splitRepresentative P hp w).val * _ * (splitRepresentative P hp w).val⁻¹ = _
  rw [curve_unit, splitRepresentative_rootCurveUnit_conjugation,
    ← rootEnumeration_positiveIndex, representative_numbered, h, rootEnumeration_positiveIndex]
  rfl

private theorem carrier_conjugate (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) (x y : ElementaryGroup P)
    (h : splitRepresentative P hp w * elementaryInclusion P x *
      (splitRepresentative P hp w)⁻¹ = elementaryInclusion P y) :
    weylRepresentative P hp w * toCarrier P x * (weylRepresentative P hp w)⁻¹ =
      toCarrier P y := by
  have he : weylElementary P hp w * x * (weylElementary P hp w)⁻¹ = y := by
    apply elementaryInclusion_injective P
    exact (by simpa only [map_mul, map_inv, splitRepresentative] using h)
  exact (by simpa only [map_mul, map_inv, weylRepresentative] using congrArg (toCarrier P) he)

private theorem long_image (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) (i j : Fin 3)
    (h : DiagramFixed.representativeTable w (positiveIndex (longPosition i)) =
      positiveIndex (longPosition j)) (t : fixedField P) :
    MulAut.conj (weylRepresentative P hp w) (long P hp i t) = long P hp j t :=
  carrier_conjugate P hp w _ _ (by
    simpa only [longElementary_val, longSplit] using
      conjugate_curve P hp w (longPosition i) (longPosition j) h t.val)

private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g * (x*y) * g⁻¹ = (g*x*g⁻¹)*(g*y*g⁻¹) := by group

private theorem short_central_image (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    MulAut.conj (weylRepresentative P hp (.sr 1)) (short P hp 0 t) = short P hp 1 t := by
  apply carrier_conjugate
  simp only [shortElementary_val, shortSplit, conjugate_mul]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (conjugate_curve P hp (.sr 1) 0 4 (by decide) t)
    (conjugate_curve P hp (.sr 1) 1 5 (by decide) (fieldFrobenius P t)))
    (conjugate_curve P hp (.sr 1) 2 6 (by decide) (fieldFrobenius P (fieldFrobenius P t)))

private theorem headHom_formula (P : Parameters) (hp : P.prime = 2)
    (v : Multiplicative (TailParameters P)) :
    headHom P hp v = short P hp 0 v.toAdd.1 *
      long P hp 1 (v.toAdd.2 0) * long P hp 2 (v.toAdd.2 1) := by
  change (coordinates P hp (headParameters P v.toAdd)).val = _
  rw [coordinates_val, rootElement_factorization]
  simp [headParameters, extendOrbit]

/-- The head conjugated by the central simple reflection. -/
def returningHead (P : Parameters) (hp : P.prime = 2) : Subgroup (Carrier P) :=
  (headSubgroup P hp).map (MulAut.conj (weylRepresentative P hp (.sr 1))).toMonoidHom

/-- A conjugate of the tail with its central Levi complement. -/
def candidateLocal (P : Parameters) (hp : P.prime = 2) : Subgroup (Carrier P) :=
  (tailSubgroup P hp ⊔ levi P .central).map
    (MulAut.conj (weylRepresentative P hp (.sr 0))).toMonoidHom

theorem returningHead_mem (f : ℕ) (hf : 0 < f) :
    returningHead (binaryParameters f hf) rfl ∈ headFamily f hf :=
  ⟨MulAut.conj (weylRepresentative _ rfl (.sr 1)), rfl⟩

theorem mem_returningHead_iff (P : Parameters) (hp : P.prime = 2) (x : Carrier P) :
    x ∈ returningHead P hp ↔ ∃ t : ExtensionField P, ∃ u v : fixedField P,
      x = short P hp 1 t * long P hp 1 u * long P hp 2 v := by
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨a.toAdd.1, a.toAdd.2 1, a.toAdd.2 0, ?_⟩
    change MulAut.conj (weylRepresentative P hp (.sr 1)) (headHom P hp a) = _
    rw [headHom_formula, map_mul, map_mul, short_central_image,
      long_image P hp (.sr 1) 1 2 (by decide), long_image P hp (.sr 1) 2 1 (by decide)]
    have hc : Commute (long P hp 2 (a.toAdd.2 0)) (long P hp 1 (a.toAdd.2 1)) := by
      let _ := headSubgroup_elementary P hp
      let _ : CommGroup (headSubgroup P hp) := IsMulCommutative.instCommGroup
      have h1 : long P hp 1 (a.toAdd.2 1) ∈ headSubgroup P hp := by
        refine ⟨Multiplicative.ofAdd (0, ![a.toAdd.2 1, 0]), ?_⟩
        simp [headHom_formula]
      have h2 : long P hp 2 (a.toAdd.2 0) ∈ headSubgroup P hp := by
        refine ⟨Multiplicative.ofAdd (0, ![0, a.toAdd.2 0]), ?_⟩
        simp [headHom_formula]
      exact congrArg Subtype.val
        (mul_comm (⟨_, h2⟩ : headSubgroup P hp) ⟨_, h1⟩)
    rw [mul_assoc, hc.eq, ← mul_assoc]
  · rintro ⟨t,u,v,rfl⟩
    have hx : short P hp 1 t * long P hp 1 u * long P hp 2 v =
        MulAut.conj (weylRepresentative P hp (.sr 1))
          (headHom P hp (Multiplicative.ofAdd (t, ![v,u]))) := by
      have h := (show ∀ a, (MulAut.conj (weylRepresentative P hp (.sr 1)))
        (headHom P hp a) = short P hp 1 a.toAdd.1 *
          long P hp 2 (a.toAdd.2 0) * long P hp 1 (a.toAdd.2 1) from by
        intro a
        rw [headHom_formula, map_mul, map_mul, short_central_image,
          long_image P hp (.sr 1) 1 2 (by decide), long_image P hp (.sr 1) 2 1 (by decide)])
      rw [h]
      change short P hp 1 t * long P hp 1 u * long P hp 2 v =
        short P hp 1 t * long P hp 2 v * long P hp 1 u
      have hcomm : long P hp 1 u * long P hp 2 v = long P hp 2 v * long P hp 1 u := by
        apply (FixedDescent.carrierToSplit_injective P hp)
        simp only [map_mul, long, FixedDescent.carrierToSplit_toCarrier,
          longElementary_val, longSplit]
        exact (nonsumCommute_parameters P 10 11 (by decide) (by
          rintro ⟨k,hk⟩
          have ht := (mem_sumTriples_iff 10 11 k).mpr ((root_sum_iff 10 11 k).mp hk)
          have hn : ∀ k : Fin 12, (10,11,k) ∉ sumTriples := by decide
          exact hn k ht) u.val v.val).eq
      simp only [mul_assoc, hcomm]
    rw [hx]
    exact mem_map_of_mem _ ⟨_, rfl⟩


theorem tail_le_radical (P : Parameters) (hp : P.prime = 2) :
    tailSubgroup P hp ≤ radical P .central := by
  rintro _ ⟨v,rfl⟩
  exact (tailRadicalHom P hp v).property

theorem mem_tail_iff_layer_zero (P : Parameters) (hp : P.prime = 2)
    (r : radical P .central) :
    r.val ∈ tailSubgroup P hp ↔ firstLayer P hp r = 0 := by
  constructor
  · rintro ⟨v,hv⟩
    have hr : tailRadicalHom P hp v = r := Subtype.ext hv
    rw [← hr]
    change firstLayer P hp (coordinates P hp (tailParameters P v.toAdd)) = 0
    rw [firstLayer_coordinates]
    rfl
  · intro hz
    obtain ⟨v,rfl⟩ := (coordinates P hp).surjective r
    rw [firstLayer_coordinates] at hz
    have h0 : v.1 0 = 0 := congrArg Prod.fst hz
    have h1 : v.1 1 = 0 := congrArg Prod.snd hz
    refine ⟨Multiplicative.ofAdd (v.1 2,v.2), ?_⟩
    change (coordinates P hp (tailParameters P (v.1 2,v.2))).val = _
    congr 2
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [tailParameters, h0, h1]
    · rfl

theorem parabolic_normalizes_tail (P : Parameters) (hp : P.prime = 2) :
    parabolic P .central ≤ normalizer (tailSubgroup P hp : Set (Carrier P)) := by
  intro g hg
  apply mem_normalizer_fintype
  intro x hx
  let r : radical P .central := ⟨x, tail_le_radical P hp hx⟩
  obtain ⟨m,hm⟩ := firstLayer_linear P hp (firstLayer_mul P hp) ⟨g,hg⟩
  have hz : firstLayer P hp r = 0 := (mem_tail_iff_layer_zero P hp r).mp hx
  exact (mem_tail_iff_layer_zero P hp (conjugation P ⟨g,hg⟩ r)).mpr
    (by rw [hm,hz,map_zero])


theorem candidateLocal_card (P : Parameters) (hp : P.prime = 2) :
    Nat.card (candidateLocal P hp) = P.q ^ 5 * (P.q * (P.q ^ 2 - 1)) := by
  rw [candidateLocal, Subgroup.card_map_of_injective
    (MulAut.conj (weylRepresentative P hp (.sr 0))).injective]
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    ((levi_le_parabolic P .central).trans (parabolic_normalizes_tail P hp))
    ((disjoint_radical_levi P hp .central).mono_left (tail_le_radical P hp)),
    card_tailSubgroup]
  congr 1
  rw [Nat.card_congr (leviCentralEquivPSL2 P hp).toEquiv]
  let : CharP (GaloisField P.prime P.exponent) 2 :=
    hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
  rw [← Nat.card_congr (Theory.PSL2.sl2QuotientEquiv
    (GaloisField P.prime P.exponent)).toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup, card_baseField]

theorem candidateLocal_binary_card :
    Nat.card (candidateLocal (binaryParameters 1 Nat.zero_lt_one) rfl) = 192 := by
  have h := candidateLocal_card (binaryParameters 1 Nat.zero_lt_one) rfl
  norm_num [binaryParameters_q] at h
  exact h

private theorem central_root_mem_levi (P : Parameters) (hp : P.prime = 2)
    (s : Bool) (t : fixedField P) :
    ConcreteBruhat.rootElement P hp s .central t ∈ levi P .central := by
  refine ⟨rootElementary P hp s .central t, ?_, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨1, rfl, t.val, ?_⟩
  cases s
  · exact Or.inr rfl
  · exact Or.inl rfl

private theorem central_weyl_mem_levi (P : Parameters) (hp : P.prime = 2) :
    weylRepresentative P hp (.sr 1) ∈ levi P .central := by
  change weylRepresentative P hp (relativeReflection .central) ∈ _
  rw [weylRepresentative_simple P hp .central, simpleRepresentative_eq_root_word]
  exact (levi P .central).mul_mem ((levi P .central).mul_mem
    (central_root_mem_levi P hp true 1) (central_root_mem_levi P hp false 1))
    (central_root_mem_levi P hp true 1)

theorem escape_mem_candidateLocal (P : Parameters) (hp : P.prime = 2) :
    weylRepresentative P hp (.sr 5) ∈ candidateLocal P hp := by
  refine ⟨weylRepresentative P hp (.sr 1),
    mem_sup_right (central_weyl_mem_levi P hp), ?_⟩
  change weylRepresentativeHom P hp (.sr 0) * weylRepresentativeHom P hp (.sr 1) *
    (weylRepresentativeHom P hp (.sr 0))⁻¹ = weylRepresentativeHom P hp (.sr 5)
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem escape_not_central (f : ℕ) (hf : 0 < f) :
    weylRepresentative (binaryParameters f hf) rfl (.sr 5) ∉
      parabolic (binaryParameters f hf) .central := by
  have hc : weylRepresentative (binaryParameters f hf) rfl (.sr 5) ∈
      cell (binaryParameters f hf) rfl (.sr 5) :=
    (mem_cell_iff _ _ _ _).mpr ⟨1, (borel _).one_mem, 1, (borel _).one_mem, by simp⟩
  rw [FixedDescent.mem_parabolic_iff_of_mem_cell f hf .central hc,
    FoldedCellGeometry.rootRepresentative_mem_parabolicWeyl_iff]
  decide

theorem candidateLocal_not_le_central (f : ℕ) (hf : 0 < f) :
    ¬ candidateLocal (binaryParameters f hf) rfl ≤ parabolic (binaryParameters f hf) .central :=
  fun h => escape_not_central f hf (h (escape_mem_candidateLocal _ rfl))


private theorem short_arms_image (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    MulAut.conj (weylRepresentative P hp (.sr 0)) (short P hp 2 t) =
      short P hp 1 (fieldFrobenius P t) := by
  apply carrier_conjugate
  simp only [shortElementary_val, shortSplit, conjugate_mul]
  calc
    _ = curve P 6 t * curve P 4 (fieldFrobenius P t) *
        curve P 5 (fieldFrobenius P (fieldFrobenius P t)) :=
      congrArg₂ (· * ·) (congrArg₂ (· * ·)
        (conjugate_curve P hp (.sr 0) 7 6 (by decide) t)
        (conjugate_curve P hp (.sr 0) 8 4 (by decide) (fieldFrobenius P t)))
        (conjugate_curve P hp (.sr 0) 9 5 (by decide)
          (fieldFrobenius P (fieldFrobenius P t)))
    _ = _ := by
      rw [fieldFrobenius_three]
      exact (mul_assoc _ _ _).trans
        (((shortSplit_curves_commute P 1 2 0 t (fieldFrobenius P t)).mul_right
          (shortSplit_curves_commute P 1 2 1 t (fieldFrobenius P (fieldFrobenius P t)))).eq)

private theorem tailHom_formula (P : Parameters) (hp : P.prime = 2)
    (v : Multiplicative (TailParameters P)) :
    tailHom P hp v = short P hp 2 v.toAdd.1 *
      long P hp 1 (v.toAdd.2 0) * long P hp 2 (v.toAdd.2 1) := by
  change (coordinates P hp (tailParameters P v.toAdd)).val = _
  rw [coordinates_val, rootElement_factorization]
  simp [tailParameters, extendOrbit]

private theorem short_tail (P : Parameters) (hp : P.prime = 2) (t : ExtensionField P) :
    short P hp 2 t ∈ tailSubgroup P hp := by
  refine ⟨Multiplicative.ofAdd (t,0), ?_⟩
  simp [tailHom_formula]

private theorem long_tail (P : Parameters) (hp : P.prime = 2) (i : Fin 2)
    (t : fixedField P) : long P hp i.succ t ∈ tailSubgroup P hp := by
  fin_cases i
  · refine ⟨Multiplicative.ofAdd (0,![t,0]), ?_⟩
    simp [tailHom_formula]
  · refine ⟨Multiplicative.ofAdd (0,![0,t]), ?_⟩
    simp [tailHom_formula]

private theorem long_zero_mem_levi (P : Parameters) (hp : P.prime = 2) (t : fixedField P) :
    long P hp 0 t ∈ levi P .central := by
  convert central_root_mem_levi P hp true t using 1
  apply FixedDescent.carrierToSplit_injective P hp
  simp only [long, FixedDescent.carrierToSplit_toCarrier, longElementary_val,
    ConcreteBruhat.rootElement, rootElementary]
  exact curve_simple P 1 t.val

theorem returningHead_le_candidateLocal (P : Parameters) (hp : P.prime = 2) :
    returningHead P hp ≤ candidateLocal P hp := by
  intro x hx
  obtain ⟨t,u,v,rfl⟩ := (mem_returningHead_iff P hp x).mp hx
  have hs : short P hp 1 t ∈ candidateLocal P hp := by
    have hi : short P hp 1 (fieldFrobenius P (fieldFrobenius P
        (fieldFrobenius P t))) ∈ candidateLocal P hp :=
      ⟨short P hp 2 (fieldFrobenius P (fieldFrobenius P t)),
        mem_sup_left (short_tail P hp _), short_arms_image P hp _⟩
    simpa only [fieldFrobenius_three] using hi
  have h1 : long P hp 1 u ∈ candidateLocal P hp := by
    exact ⟨long P hp 0 u, mem_sup_right (long_zero_mem_levi P hp u),
      long_image P hp (.sr 0) 0 1 (by decide) u⟩
  have h2 : long P hp 2 v ∈ candidateLocal P hp := by
    exact ⟨long P hp 2 v, mem_sup_left (long_tail P hp 1 v),
      long_image P hp (.sr 0) 2 2 (by decide) v⟩
  exact (candidateLocal P hp).mul_mem ((candidateLocal P hp).mul_mem hs h1) h2

theorem returningHead_le_unipotent (P : Parameters) (hp : P.prime = 2) :
    returningHead P hp ≤ unipotent P := by
  intro x hx
  obtain ⟨t,u,v,rfl⟩ := (mem_returningHead_iff P hp x).mp hx
  have hs : short P hp 1 t ∈ unipotent P :=
    descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .central)
      (short_mem P hp .central 1 (by trivial) t)
  have hl (i : Fin 3) (z : fixedField P) : long P hp i z ∈ unipotent P :=
    descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .arms)
      (long_mem P hp .arms i (by trivial) z)
  exact (unipotent P).mul_mem ((unipotent P).mul_mem hs (hl 1 u)) (hl 2 v)


def longZeroHom (P : Parameters) (hp : P.prime = 2) :
    Multiplicative (fixedField P) →* Carrier P where
  toFun t := long P hp 0 t.toAdd
  map_one' := long_zero P hp 0
  map_mul' a b := long_add P hp 0 a.toAdd b.toAdd

private theorem headHom_long_one (P : Parameters) (hp : P.prime = 2) (t : fixedField P) :
    headHom P hp (Multiplicative.ofAdd (0,![t,0])) = long P hp 1 t := by
  simp [headHom_formula]

theorem longZeroHom_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (longZeroHom P hp) := by
  intro s t h
  have he := congrArg (MulAut.conj (weylRepresentative P hp (.sr 0))) h
  change MulAut.conj (weylRepresentative P hp (.sr 0)) (long P hp 0 s.toAdd) =
    MulAut.conj (weylRepresentative P hp (.sr 0)) (long P hp 0 t.toAdd) at he
  rw [long_image P hp (.sr 0) 0 1 (by decide),
    long_image P hp (.sr 0) 0 1 (by decide)] at he
  have hh : headHom P hp (Multiplicative.ofAdd (0,![s.toAdd,0])) =
      headHom P hp (Multiplicative.ofAdd (0,![t.toAdd,0])) :=
    (headHom_long_one P hp s.toAdd).trans (he.trans (headHom_long_one P hp t.toAdd).symm)
  exact congrArg (fun v : Multiplicative (TailParameters P) =>
    Multiplicative.ofAdd (v.toAdd.2 0)) (headHom_injective P hp hh)

private theorem longZeroHom_range_le_levi (P : Parameters) (hp : P.prime = 2) :
    (longZeroHom P hp).range ≤ levi P .central := by
  rintro _ ⟨t,rfl⟩
  exact long_zero_mem_levi P hp t.toAdd

/-- The positive two-subgroup used to establish the original Sylow intersection. -/
def candidatePositive (P : Parameters) (hp : P.prime = 2) : Subgroup (Carrier P) :=
  (tailSubgroup P hp ⊔ (longZeroHom P hp).range).map
    (MulAut.conj (weylRepresentative P hp (.sr 0))).toMonoidHom

theorem candidatePositive_le_candidateLocal (P : Parameters) (hp : P.prime = 2) :
    candidatePositive P hp ≤ candidateLocal P hp :=
  map_mono (sup_le_sup le_rfl (longZeroHom_range_le_levi P hp))

theorem candidatePositive_card (P : Parameters) (hp : P.prime = 2) :
    Nat.card (candidatePositive P hp) = P.q ^ 6 := by
  rw [candidatePositive, card_map_of_injective
    (MulAut.conj (weylRepresentative P hp (.sr 0))).injective]
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    ((longZeroHom_range_le_levi P hp).trans
      ((levi_le_parabolic P .central).trans (parabolic_normalizes_tail P hp)))
    ((disjoint_radical_levi P hp .central).mono (tail_le_radical P hp)
      (longZeroHom_range_le_levi P hp)), card_tailSubgroup]
  rw [← Nat.card_congr (MonoidHom.ofInjective (longZeroHom_injective P hp)).toEquiv]
  change P.q ^ 5 * Nat.card (fixedField P) = _
  rw [card_fixedField, ← pow_succ]

theorem candidatePositive_le_unipotent (P : Parameters) (hp : P.prime = 2) :
    candidatePositive P hp ≤ unipotent P := by
  have hs (t : ExtensionField P) : short P hp 1 t ∈ unipotent P :=
    descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .central)
      (short_mem P hp .central 1 (by trivial) t)
  have hl (i : Fin 3) (t : fixedField P) : long P hp i t ∈ unipotent P :=
    descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .arms)
      (long_mem P hp .arms i (by trivial) t)
  rw [candidatePositive, Subgroup.map_sup]
  apply sup_le
  · rintro _ ⟨_, ⟨v,rfl⟩, rfl⟩
    change MulAut.conj (weylRepresentative P hp (.sr 0)) (tailHom P hp v) ∈ _
    rw [tailHom_formula, map_mul, map_mul, short_arms_image,
      long_image P hp (.sr 0) 1 0 (by decide), long_image P hp (.sr 0) 2 2 (by decide)]
    exact (unipotent P).mul_mem ((unipotent P).mul_mem (hs _) (hl 0 _)) (hl 2 _)
  · rintro _ ⟨_, ⟨t,rfl⟩, rfl⟩
    change MulAut.conj (weylRepresentative P hp (.sr 0)) (long P hp 0 t.toAdd) ∈ _
    rw [long_image P hp (.sr 0) 0 1 (by decide)]
    exact hl 1 _

theorem candidate_binary_relative_sylow :
    let P := binaryParameters 1 Nat.zero_lt_one
    ∃ S : Sylow 2 (candidateLocal P rfl),
      (S : Subgroup (candidateLocal P rfl)) = (unipotent P).subgroupOf (candidateLocal P rfl) := by
  let P := binaryParameters 1 Nat.zero_lt_one
  let K := candidateLocal P rfl
  let H := candidatePositive P rfl
  have hHK : H ≤ K := candidatePositive_le_candidateLocal P rfl
  have hHU : H ≤ unipotent P := candidatePositive_le_unipotent P rfl
  have hH : Nat.card H = 64 := by
    have h := candidatePositive_card P rfl
    norm_num [P,binaryParameters_q] at h
    exact h
  have hK : Nat.card K = 192 := candidateLocal_binary_card
  let R := H.subgroupOf K
  have hc : Nat.card R = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hHK).toEquiv).trans hH
  have hi : R.index = 3 := by
    have he := R.card_mul_index
    rw [hc,hK] at he
    omega
  have hR : IsPGroup 2 R :=
    ((unipotent_isPGroup_binary P rfl).to_le hHU).comap_subtype
  let S := hR.toSylow (by rw [hi]; decide)
  refine ⟨S, ?_⟩
  exact (S.is_maximal' (unipotent_isPGroup_binary P rfl).comap_subtype
    (comap_mono hHU)).symm


private theorem middle_coordinates (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) (u v : fixedField P) :
    (coordinates P hp (![0,t,0],![u,v])).val =
      short P hp 1 t * long P hp 1 u * long P hp 2 v := by
  rw [coordinates_val, rootElement_factorization]
  simp [extendOrbit]

private theorem radical_commutes_long_one (P : Parameters) (hp : P.prime = 2)
    (r : radical P .central) (t : fixedField P) : Commute r.val (long P hp 1 t) := by
  obtain ⟨v,rfl⟩ := (coordinates P hp).surjective r
  have hz : (coordinates P hp (0,![t,0])).val = long P hp 1 t := by
    rw [coordinates_val, rootElement_factorization]
    simp [extendOrbit]
  rw [← hz]
  suffices h : Commute (coordinates P hp v) (coordinates P hp (0,![t,0])) from
    h.map (radical P .central).subtype
  change coordinates P hp v * coordinates P hp (0,![t,0]) =
    coordinates P hp (0,![t,0]) * coordinates P hp v
  rw [← coordinates_multiply, ← coordinates_multiply]
  congr 1
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [multiply,higherCoefficient,-fieldFrobenius_apply]
  · funext i
    fin_cases i <;> simp [multiply,higherCoefficient,add_comm,-fieldFrobenius_apply]

private theorem positive_factorization_of_coordinates (P : Parameters) (hp : P.prime = 2)
    (x : ElementaryGroup P) (v : OrbitParameters P)
    (hv : orderedProduct P (expand P v) = elementaryInclusion P x) :
    toCarrier P x = short P hp 0 (v.1 0) * long P hp 0 (v.2 0) *
      short P hp 1 (v.1 1) * short P hp 2 (v.1 2) *
        long P hp 1 (v.2 1) * long P hp 2 (v.2 2) := by
  have he : x = shortElementary P hp 0 (v.1 0) * longElementary P hp 0 (v.2 0) *
      shortElementary P hp 1 (v.1 1) * shortElementary P hp 2 (v.1 2) *
        longElementary P hp 1 (v.2 1) * longElementary P hp 2 (v.2 2) := by
    apply elementaryInclusion_injective P
    simp only [map_mul, shortElementary_val P hp, longElementary_val P hp]
    exact hv.symm.trans (orderedProduct_expand P v)
  exact (congrArg (toCarrier P) he).trans (by simp only [map_mul]; rfl)

private theorem positive_factorization (f : ℕ) (hf : 0 < f)
    (g : BinaryCarrier f hf) (hg : g ∈ unipotent (binaryParameters f hf)) :
    let P := binaryParameters f hf
    ∃ v : OrbitParameters P,
      g = short P rfl 0 (v.1 0) * long P rfl 0 (v.2 0) *
        short P rfl 1 (v.1 1) * short P rfl 2 (v.1 2) *
          long P rfl 1 (v.2 1) * long P rfl 2 (v.2 2) := by
  let P := binaryParameters f hf
  obtain ⟨x,hx,rfl⟩ := hg
  let e := orbitPositiveEquiv_binary f hf
  let y : (positiveSubgroup P).comap (fixedSubgroup P).subtype := ⟨x.val,hx⟩
  let v := e.symm y
  have hv : orderedProduct P (expand P v) = elementaryInclusion P x :=
    (orbitPositiveEquiv_binary_val f hf v).symm.trans
      (congrArg (fun z => z.val.val) (e.apply_symm_apply y))
  refine ⟨v, ?_⟩
  exact positive_factorization_of_coordinates P rfl x v hv

private theorem short_radical (P : Parameters) (hp : P.prime = 2)
    (i : Fin 3) (t : ExtensionField P) : short P hp i t ∈ radical P .central := by
  rw [radical_eq_descendedRootSubgroup P hp]
  exact short_mem P hp .central i (by trivial) t

private theorem long_one_radical (P : Parameters) (hp : P.prime = 2)
    (t : fixedField P) : long P hp 1 t ∈ radical P .central := by
  rw [radical_eq_descendedRootSubgroup P hp]
  exact long_mem P hp .central 1 (by simp [longSupported]) t

private theorem long_two_radical (P : Parameters) (hp : P.prime = 2)
    (t : fixedField P) : long P hp 2 t ∈ radical P .central := by
  rw [radical_eq_descendedRootSubgroup P hp]
  exact long_mem P hp .central 2 (by simp [longSupported]) t

private theorem long_two_eq_one (P : Parameters) (hp : P.prime = 2)
    {t : fixedField P} (h : long P hp 2 t = 1) : t = 0 := by
  have he : headHom P hp (Multiplicative.ofAdd (0,![0,t])) =
      headHom P hp (Multiplicative.ofAdd (0,![0,0])) := by
    simpa [headHom_formula] using h
  exact congrArg (fun v : Multiplicative (TailParameters P) => v.toAdd.2 1)
    (headHom_injective P hp he)

private theorem positive_centralizer_radical_of_coordinates (P : Parameters) (hp : P.prime = 2)
    (g : Carrier P) (v : OrbitParameters P)
    (hv : g = short P hp 0 (v.1 0) * long P hp 0 (v.2 0) *
      short P hp 1 (v.1 1) * short P hp 2 (v.1 2) *
        long P hp 1 (v.2 1) * long P hp 2 (v.2 2))
    (hg : g ∈ centralizer (returningHead P hp : Set (Carrier P))) :
    g ∈ radical P .central := by
  let r := short P hp 0 (v.1 0)
  let s := short P hp 1 (v.1 1) * short P hp 2 (v.1 2) *
    long P hp 1 (v.2 1) * long P hp 2 (v.2 2)
  have hr : r ∈ radical P .central := short_radical P hp 0 _
  have hs : s ∈ radical P .central := (radical P .central).mul_mem
    ((radical P .central).mul_mem ((radical P .central).mul_mem
      (short_radical P hp 1 _) (short_radical P hp 2 _))
      (long_one_radical P hp _)) (long_two_radical P hp _)
  have hx : long P hp 1 1 ∈ returningHead P hp := by
    apply (mem_returningHead_iff P hp _).mpr
    exact ⟨0,1,0, by simp⟩
  have hc : Commute g (long P hp 1 1) :=
    (mem_centralizer_iff.mp hg _ hx).symm
  have hfac : g = r * long P hp 0 (v.2 0) * s := by
    simpa only [r,s,mul_assoc] using hv
  have hc' : Commute (r⁻¹ * g * s⁻¹) (long P hp 1 1) :=
    ((radical_commutes_long_one P hp ⟨r,hr⟩ 1).inv_left.mul_left hc).mul_left
    (radical_commutes_long_one P hp ⟨s,hs⟩ 1).inv_left
  have hb : Commute (long P hp 0 (v.2 0)) (long P hp 1 1) := by
    have heq : r⁻¹ * g * s⁻¹ = long P hp 0 (v.2 0) := by rw [hfac]; group
    rw [heq] at hc'
    exact hc'
  have he := long_zero_one_exchange P hp (v.2 0) 1
  rw [mul_one] at he
  have hz : long P hp 2 (v.2 0) = 1 :=
    mul_left_cancel (he.symm.trans (hb.eq.trans (mul_one _).symm))
  have hb0 := long_two_eq_one P hp hz
  have hgs : g = r*s := by simpa only [hb0,long_zero,mul_one] using hfac
  rw [hgs]
  exact (radical P .central).mul_mem hr hs

private theorem positive_centralizer_le_radical (f : ℕ) (hf : 0 < f) :
    let P := binaryParameters f hf
    unipotent P ⊓ centralizer (returningHead P rfl : Set (BinaryCarrier f hf)) ≤
      radical P .central := by
  dsimp only
  intro g hg
  obtain ⟨v,hv⟩ := positive_factorization f hf g hg.1
  exact positive_centralizer_radical_of_coordinates _ rfl g v hv hg.2

private theorem higherCoefficient_left_nondegenerate (P : Parameters) (hp : P.prime = 2)
    (a : ExtensionField P) (h : ∀ s, higherCoefficient P a s = 0) : a = 0 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have h1 := h 1
  simp only [higherCoefficient,map_one,mul_one] at h1
  have hF : fieldFrobenius P a = a := (CharTwo.add_eq_zero.mp h1).symm
  obtain ⟨s,hs⟩ := ElementaryCentralKernel.exists_frobenius_moved P
  have he : a * (fieldFrobenius P s + s) = 0 := by
    simpa only [higherCoefficient,hF,mul_add] using h s
  exact (mul_eq_zero.mp he).resolve_right (fun hz => hs (CharTwo.add_eq_zero.mp hz))

private theorem radical_centralizer_le_returningHead (P : Parameters) (hp : P.prime = 2) :
    radical P .central ⊓ centralizer (returningHead P hp : Set (Carrier P)) ≤
      returningHead P hp := by
  rintro g ⟨hg,hc⟩
  obtain ⟨v,hv⟩ := (coordinates P hp).surjective ⟨g,hg⟩
  have hval : (coordinates P hp v).val = g := congrArg Subtype.val hv
  have he (s : ExtensionField P) :
      multiply P v (![0,s,0],![0,0]) = multiply P (![0,s,0],![0,0]) v := by
    apply (coordinates P hp).injective
    rw [coordinates_multiply,coordinates_multiply]
    apply Subtype.ext
    have hm : short P hp 1 s ∈ returningHead P hp :=
      (mem_returningHead_iff P hp _).mpr ⟨s,0,0,by simp⟩
    have hh := (mem_centralizer_iff.mp hc _ hm).symm
    change (coordinates P hp v).val * (coordinates P hp (![0,s,0],![0,0])).val =
      (coordinates P hp (![0,s,0],![0,0])).val * (coordinates P hp v).val
    simp only [hval,middle_coordinates P hp s 0 0,long_zero,mul_one]
    exact hh
  have h0 : v.1 0 = 0 := by
    apply higherCoefficient_left_nondegenerate P hp
    intro s
    have hh := congrArg (fun z : RootOrbitParameters P .central => z.1 2) (he s)
    simpa [multiply,higherCoefficient,-fieldFrobenius_apply] using hh.symm
  have h2 : v.1 2 = 0 := by
    apply Centers.armsPairing_right_nondegenerate P hp
    intro s
    have hh := congrArg (fun z : RootOrbitParameters P .central => z.2 1) (he s)
    simpa [multiply,h0,higherCoefficient,-fieldFrobenius_apply] using hh
  apply (mem_returningHead_iff P hp g).mpr
  refine ⟨v.1 1,v.2 0,v.2 1, ?_⟩
  rw [← hval, coordinates_val,rootElement_factorization]
  simp [extendOrbit,h0,h2]

theorem returningHead_positive_centralizer (f : ℕ) (hf : 0 < f) :
    let P := binaryParameters f hf
    unipotent P ⊓ centralizer (returningHead P rfl : Set (BinaryCarrier f hf)) ≤
      returningHead P rfl :=
  fun _ h => radical_centralizer_le_returningHead _ rfl
    ⟨positive_centralizer_le_radical f hf h,h.2⟩


/-- The conjugated tail, a relatively normal two-subgroup of the candidate. -/
def candidateCore (P : Parameters) (hp : P.prime = 2) : Subgroup (Carrier P) :=
  (tailSubgroup P hp).map (MulAut.conj (weylRepresentative P hp (.sr 0))).toMonoidHom

/-- The conjugated central Levi complement. -/
def candidateLevi (P : Parameters) (hp : P.prime = 2) : Subgroup (Carrier P) :=
  (levi P .central).map (MulAut.conj (weylRepresentative P hp (.sr 0))).toMonoidHom

private theorem candidate_sup (P : Parameters) (hp : P.prime = 2) :
    candidateCore P hp ⊔ candidateLevi P hp = candidateLocal P hp :=
  (Subgroup.map_sup _ _ _).symm

private theorem candidate_disjoint (P : Parameters) (hp : P.prime = 2) :
    Disjoint (candidateCore P hp) (candidateLevi P hp) :=
  Subgroup.disjoint_map (MulAut.conj (weylRepresentative P hp (.sr 0))).injective
    ((disjoint_radical_levi P hp .central).mono_left (tail_le_radical P hp))

private theorem candidate_core_le (P : Parameters) (hp : P.prime = 2) :
    candidateCore P hp ≤ candidateLocal P hp := map_mono le_sup_left

private theorem candidate_levi_le (P : Parameters) (hp : P.prime = 2) :
    candidateLevi P hp ≤ candidateLocal P hp := map_mono le_sup_right

private theorem candidate_core_normal (P : Parameters) (hp : P.prime = 2) :
    ((candidateCore P hp).subgroupOf (candidateLocal P hp)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [← candidate_sup]
  apply sup_le (candidateCore P hp).le_normalizer
  exact (map_mono ((levi_le_parabolic P .central).trans (parabolic_normalizes_tail P hp))).trans
    (le_normalizer_map (MulAut.conj (weylRepresentative P hp (.sr 0))).toMonoidHom)

private theorem candidate_core_two (P : Parameters) (hp : P.prime = 2) :
    IsPGroup 2 (candidateCore P hp) := by
  let _ := tailSubgroup_elementary P hp
  exact (IsElementaryAbelian.isPGroup 2 (tailSubgroup P hp)).map _

private theorem long_zero_one_ne_one (P : Parameters) (hp : P.prime = 2) :
    long P hp 0 1 ≠ 1 := by
  intro hz
  have hh : longZeroHom P hp (Multiplicative.ofAdd (1 : fixedField P)) =
      longZeroHom P hp (Multiplicative.ofAdd (0 : fixedField P)) := by
    change long P hp 0 1 = long P hp 0 0
    rw [long_zero]
    exact hz
  have h10 : (1 : fixedField P) = 0 :=
    congrArg (fun x : Multiplicative (fixedField P) => x.toAdd) (longZeroHom_injective P hp hh)
  exact one_ne_zero h10

private theorem long_zero_one_not_tail (P : Parameters) (hp : P.prime = 2) :
    long P hp 0 1 ∉ tailSubgroup P hp := by
  intro ht
  exact long_zero_one_ne_one P hp (Subgroup.disjoint_def.mp
    ((disjoint_radical_levi P hp .central).mono_left (tail_le_radical P hp))
    ht (long_zero_mem_levi P hp 1))

private theorem returningHead_not_le_candidateCore (P : Parameters) (hp : P.prime = 2) :
    ¬ returningHead P hp ≤ candidateCore P hp := by
  intro h
  have hx : long P hp 1 1 ∈ returningHead P hp :=
    (mem_returningHead_iff P hp _).mpr ⟨0,1,0,by simp⟩
  have hm : long P hp 1 1 ∈ (tailSubgroup P hp).map
      (MulAut.conj (weylRepresentative P hp (.sr 0))).toMonoidHom := h hx
  obtain ⟨r,hr,he⟩ := hm
  have he' : r = long P hp 0 1 :=
    (MulAut.conj (weylRepresentative P hp (.sr 0))).injective
      (he.trans (long_image P hp (.sr 0) 0 1 (by decide) 1).symm)
  apply long_zero_one_not_tail P hp
  exact he' ▸ hr

private theorem binary_candidate_symmetricThree_quotient :
    let P := binaryParameters 1 Nat.zero_lt_one
    let K := candidateLocal P rfl
    ∃ φ : K →* Equiv.Perm (Fin 3), Function.Surjective φ ∧ IsPGroup 2 φ.ker ∧
      ¬ (returningHead P rfl).subgroupOf K ≤ φ.ker := by
  let P := binaryParameters 1 Nat.zero_lt_one
  let K := candidateLocal P rfl
  let R := candidateCore P rfl
  let C := candidateLevi P rfl
  let _ : (R.subgroupOf K).Normal := candidate_core_normal P rfl
  let π : K →* C := relativeComplementProjection (candidate_core_le P rfl)
    (candidate_levi_le P rfl) (candidate_sup P rfl) (candidate_disjoint P rfl)
  have hπ : Function.Surjective π := relativeComplementProjection_surjective
    (candidate_core_le P rfl) (candidate_levi_le P rfl)
    (candidate_sup P rfl) (candidate_disjoint P rfl)
  have hker : π.ker = R.subgroupOf K := relativeComplementProjection_ker
    (candidate_core_le P rfl) (candidate_levi_le P rfl)
    (candidate_sup P rfl) (candidate_disjoint P rfl)
  obtain ⟨e₃⟩ := BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two
    (K := GaloisField P.prime P.exponent) (by rw [card_baseField]; norm_num [P,binaryParameters_q])
  let e : C ≃* Equiv.Perm (Fin 3) :=
    ((levi P .central).equivMapOfInjective
      (MulAut.conj (weylRepresentative P rfl (.sr 0))).toMonoidHom
      (MulAut.conj (weylRepresentative P rfl (.sr 0))).injective).symm.trans
      ((leviCentralEquivPSL2 P rfl).trans e₃)
  let φ := e.toMonoidHom.comp π
  have hk : φ.ker = R.subgroupOf K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,hker]
  refine ⟨φ,e.surjective.comp hπ, ?_, ?_⟩
  · rw [hk]
    exact (candidate_core_two P rfl).comap_subtype
  · rw [hk]
    intro h
    apply returningHead_not_le_candidateCore P rfl
    intro x hx
    exact h (show (⟨x,returningHead_le_candidateLocal P rfl hx⟩ : K) ∈
      (returningHead P rfl).subgroupOf K from hx)

private theorem carrier_twoCore_bot (f : ℕ) (hf : 0 < f) :
    pCore 2 (BinaryCarrier f hf) = ⊥ := by
  by_contra h
  obtain ⟨g,a,ha⟩ := _root_.Triality.Standard.TwoLocalCover.normalizer_cover f hf
    (pCore 2 (BinaryCarrier f hf)) h pCore_isPGroup
  rw [normalizer_eq_top, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at ha
  exact parabolic_ne_top_binary (binaryParameters f hf) rfl a (top_unique ha)

theorem returningHead_tau_le (f : ℕ) (hf : 0 < f) :
    let P := binaryParameters f hf
    tau (unipotent P) (returningHead P rfl) ≤ returningHead P rfl := by
  dsimp only
  intro g hg
  obtain ⟨hgU,hgC⟩ := mem_centralizerModulo_iff.mp hg
  apply returningHead_positive_centralizer f hf
  refine ⟨hgU,mem_centralizer_iff.mpr ?_⟩
  intro a ha
  have h := hgC a ha
  rw [carrier_twoCore_bot f hf,mem_bot,commutatorElement_eq_one_iff_mul_comm] at h
  exact h

/-- Full E0 and E1 for the actual candidate, at the requested predecessor bound. -/
theorem binary_candidate_isEMemberAt :
    let P := binaryParameters 1 Nat.zero_lt_one
    IsEMemberAt (3*1-1) (unipotent P) (returningHead P rfl) (candidateLocal P rfl) := by
  let P := binaryParameters 1 Nat.zero_lt_one
  obtain ⟨φ,hφ,hker,ha⟩ := binary_candidate_symmetricThree_quotient
  have hm := ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.isEMemberAt_of_symmetricThree_quotient
    (unipotent P) (returningHead P rfl) (candidateLocal P rfl)
    (headFamily_elementary (returningHead_mem 1 Nat.zero_lt_one))
    (returningHead_le_unipotent P rfl) (returningHead_le_candidateLocal P rfl)
    ((returningHead_tau_le 1 Nat.zero_lt_one).trans (returningHead_le_candidateLocal P rfl))
    candidate_binary_relative_sylow φ hφ hker ha
  refine ⟨hm.1, ?_⟩
  rcases hm.2 with ⟨ho,hr⟩ | ⟨hc,hr⟩
  · exact Or.inl ⟨ho,hr.trans (by decide)⟩
  · exact Or.inr ⟨hc,hr.trans (by decide)⟩


/-- At q = 2, a returning actor admits a genuine ranked E-member outside
    the original central parabolic. E0 and every clause of E1 are retained. -/
theorem binary_head_member_counterexample :
    let P := binaryParameters 1 Nat.zero_lt_one
    ∃ A K : Subgroup (BinaryCarrier 1 Nat.zero_lt_one),
      A ∈ headFamily 1 Nat.zero_lt_one ∧ A ≤ unipotent P ∧
      IsEMemberAt (3*1-1) (unipotent P) A K ∧ ¬ K ≤ parabolic P .central := by
  exact ⟨returningHead _ rfl, candidateLocal _ rfl, returningHead_mem 1 Nat.zero_lt_one,
    returningHead_le_unipotent _ rfl, binary_candidate_isEMemberAt,
    candidateLocal_not_le_central 1 Nat.zero_lt_one⟩

/-- The literal ambient family and parabolic overgroup in the trivial outer
    extension already fail the proposed E-member confinement statement. -/
theorem not_head_confinement_for_trivial_extension :
    let T := unipotentSylow (binaryParameters 1 Nat.zero_lt_one) (binaryParameters_prime 1 Nat.zero_lt_one)
    let e : (⊤ : Subgroup (BinaryCarrier 1 Nat.zero_lt_one)) ≃*
      BinaryCarrier 1 Nat.zero_lt_one := Subgroup.topEquiv
    ¬ (∀ A ∈ ambientHeadFamily ⊤ e, A ≤ (T : Subgroup (BinaryCarrier 1 Nat.zero_lt_one)) →
      ∀ K, IsEMemberAt (3*1-1) (T : Subgroup (BinaryCarrier 1 Nat.zero_lt_one)) A K →
        K ≤ parabolicOvergroup ⊤ T e .central) := by
  dsimp only
  intro h
  have hι : modelEmbedding (⊤ : Subgroup (BinaryCarrier 1 Nat.zero_lt_one)) Subgroup.topEquiv =
      MonoidHom.id (BinaryCarrier 1 Nat.zero_lt_one) := by ext x; rfl
  have hP : parabolicOvergroup (⊤ : Subgroup (BinaryCarrier 1 Nat.zero_lt_one))
      (unipotentSylow (binaryParameters 1 Nat.zero_lt_one) (binaryParameters_prime 1 Nat.zero_lt_one))
      Subgroup.topEquiv .central = parabolic (binaryParameters 1 Nat.zero_lt_one) .central := by
    rw [parabolicOvergroup, ambientParabolic, hι, Subgroup.map_id, coe_unipotentSylow]
    exact sup_eq_left.mpr
      ((unipotent_le_borel _).trans (borel_le_parabolic _ .central))
  obtain ⟨A,K,hA,hAT,hK,hbad⟩ := binary_head_member_counterexample
  have hAm : A ∈ ambientHeadFamily (⊤ : Subgroup (BinaryCarrier 1 Nat.zero_lt_one))
      Subgroup.topEquiv := by
    refine ⟨A,hA,?_⟩
    rw [hι,Subgroup.map_id]
  exact hbad (hP ▸ h A hAm hAT K hK)


/-- The trivial outer extension has exactly the generalized Fitting subgroup
required by the source. No model-family tag is used here. -/
theorem binary_generalizedFitting_eq_top :
    generalizedFitting (BinaryCarrier 1 Nat.zero_lt_one) = ⊤ := by
  let G := BinaryCarrier 1 Nat.zero_lt_one
  have hz : center G = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative G (center_eq_top_iff.mp h))
  let _ : Theory.GroupTheory.IsQuasisimple G :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
  exact Theory.GroupTheory.generalizedFitting_eq_top_of_quasisimple

/-- The failure persists in the source's simple generalized-Fitting setup.
The full SQTK input is retained as a source hypothesis, for any class C and in
particular the full known-simple class; this theorem does not certify that
separate global hypothesis for the model. All geometry and E-membership are
proved without it. -/
theorem source_setup_counterexample (C : GroupClass)
    (hSQTK : IsSQTK C (BinaryCarrier 1 Nat.zero_lt_one)) :
    let G := BinaryCarrier 1 Nat.zero_lt_one
    let L := generalizedFitting G
    let T := unipotentSylow (binaryParameters 1 Nat.zero_lt_one) (binaryParameters_prime 1 Nat.zero_lt_one)
    ∃ e : L ≃* G,
      IsSimpleGroup L ∧ L ⊔ (T : Subgroup G) = ⊤ ∧ IsSQTK C G ∧
      ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
        unipotent (binaryParameters 1 Nat.zero_lt_one) ∧
      ∃ A K : Subgroup G, A ∈ ambientHeadFamily L e ∧ A ≤ (T : Subgroup G) ∧
        IsEMemberAt (3*1-1) (T : Subgroup G) A K ∧
        ¬ K ≤ parabolicOvergroup L T e .central := by
  dsimp only
  rw [binary_generalizedFitting_eq_top]
  refine ⟨Subgroup.topEquiv, Subgroup.topEquiv.isSimpleGroup,
    top_sup_eq _, hSQTK, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,mem_top x⟩,hx,rfl⟩
  · obtain ⟨A,K,hA,hAT,hK,hbad⟩ := binary_head_member_counterexample
    have hι : modelEmbedding (⊤ : Subgroup (BinaryCarrier 1 Nat.zero_lt_one)) Subgroup.topEquiv =
        MonoidHom.id (BinaryCarrier 1 Nat.zero_lt_one) := by ext x; rfl
    have hP : parabolicOvergroup (⊤ : Subgroup (BinaryCarrier 1 Nat.zero_lt_one))
        (unipotentSylow (binaryParameters 1 Nat.zero_lt_one) (binaryParameters_prime 1 Nat.zero_lt_one))
        Subgroup.topEquiv .central = parabolic (binaryParameters 1 Nat.zero_lt_one) .central := by
      rw [parabolicOvergroup, ambientParabolic, hι, Subgroup.map_id, coe_unipotentSylow]
      exact sup_eq_left.mpr
        ((unipotent_le_borel _).trans (borel_le_parabolic _ .central))
    refine ⟨A,K,?_,hAT,hK,?_⟩
    · refine ⟨A,hA,?_⟩
      rw [hι,Subgroup.map_id]
    · simpa only [hP] using hbad


/-- The escaping genuine E-member also satisfies the published literal
O₂(K) intersection interface; none of its clauses repairs confinement. -/
theorem binary_candidate_core_intersection :
    let P := binaryParameters 1 Nat.zero_lt_one
    let T := unipotentSylow P (binaryParameters_prime 1 Nat.zero_lt_one)
    let A := returningHead P rfl
    let K := candidateLocal P rfl
    let Q := ((pCore 2 K).map K.subtype) ⊓ (⊤ : Subgroup (Carrier P))
    Q ≤ (T : Subgroup (Carrier P)) ⊓ ⊤ ∧
      K ≤ normalizer (Q : Set (Carrier P)) ∧
      2 ^ (2*1) < Nat.card (Q ⊓ A : Subgroup (Carrier P)) ∧ ¬ A ≤ Q := by
  apply head_member_core_intersection (⊤ : Subgroup (BinaryCarrier 1 Nat.zero_lt_one))
    (unipotentSylow (binaryParameters 1 Nat.zero_lt_one) (binaryParameters_prime 1 Nat.zero_lt_one))
    Subgroup.topEquiv
  · refine ⟨returningHead _ rfl,returningHead_mem 1 Nat.zero_lt_one,?_⟩
    have hι : modelEmbedding (⊤ : Subgroup (BinaryCarrier 1 Nat.zero_lt_one)) Subgroup.topEquiv =
        MonoidHom.id (BinaryCarrier 1 Nat.zero_lt_one) := by ext x; rfl
    rw [hι,Subgroup.map_id]
  · exact binary_candidate_isEMemberAt

end CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction.RelativeConfinement
