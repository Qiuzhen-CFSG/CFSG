module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Complete
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs.Cohomology
public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The actual quasisimple FF table for the Chapter15 sieves

The FF input already has a normal quasisimple component and the precise
B.5.1 hypotheses. Apply the corrected quasisimple source theorem and
transport its actual moved section and fixed quotient back to the original
module. All four B.5.1 branches and all irreducible rows are retained.
This adapter uses neither the legacy general B.5.6 conclusion nor its
incorrect exceptional splitting clause.

Source: Aschbacher–Smith B.4.2 and B.5.1(1), pp.86,99–103.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs.FFClassification
open RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open Chapter2.ComponentRefinement.LieType.Binary
universe u v
variable {K : Type u} {V : Type v} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) K V} {L : Subgroup K}

private theorem moved_coinvariants : moved ρ L = Coinvariants.ker (ρ.comp L.subtype) := by
  unfold moved subspaceCommutator Coinvariants.ker
  congr 1
  ext v
  constructor
  · rintro ⟨g,hg,w,_,rfl⟩
    exact ⟨(⟨g,hg⟩,w),rfl⟩
  · rintro ⟨⟨g,w⟩,rfl⟩
    exact ⟨g,g.property,w,Submodule.mem_top,rfl⟩

private def wholeSpace (s : MovedSection ρ L)
    (hfull : Coinvariants.ker (ρ.comp L.subtype) = ⊤) :
    V ≃ₗ[ZMod 2] s.space.toSubmodule :=
  (LinearEquiv.ofBijective s.space.toSubmodule.subtype ⟨Subtype.val_injective,by
    intro v
    refine ⟨⟨v,?_⟩,rfl⟩
    rw [s.space_eq,moved_coinvariants,hfull]
    trivial⟩).symm

private theorem wholeSpace_val (s : MovedSection ρ L)
    (hfull : Coinvariants.ker (ρ.comp L.subtype) = ⊤) (v : V) :
    (wholeSpace s hfull v : V) = v :=
  by
    change (wholeSpace s hfull).symm (wholeSpace s hfull v) = v
    exact (wholeSpace s hfull).symm_apply_apply v

private theorem wholeSpace_action (s : MovedSection ρ L)
    (hfull : Coinvariants.ker (ρ.comp L.subtype) = ⊤) (g : K) (v : V) :
    wholeSpace s hfull (ρ g v) = s.space.toRepresentation g (wholeSpace s hfull v) := by
  apply Subtype.ext
  change (wholeSpace s hfull (ρ g v) : V) = ρ g (wholeSpace s hfull v : V)
  rw [wholeSpace_val,wholeSpace_val]

private def fixedQuotient (s : MovedSection ρ L)
    (hfull : Coinvariants.ker (ρ.comp L.subtype) = ⊤) :
    (V ⧸ fixedSpace ρ L) ≃ₗ[ZMod 2] s.space.toSubmodule ⧸ s.central.toSubmodule :=
  Submodule.Quotient.equiv _ _ (wholeSpace s hfull) (by
    rw [s.central_eq]
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩ l
      change s.space.toRepresentation l (wholeSpace s hfull w) = wholeSpace s hfull w
      rw [←wholeSpace_action]
      exact congrArg (wholeSpace s hfull) (hw l)
    · intro hv
      refine ⟨(wholeSpace s hfull).symm v,?_,(wholeSpace s hfull).apply_symm_apply v⟩
      intro l
      apply (wholeSpace s hfull).injective
      change wholeSpace s hfull (ρ l ((wholeSpace s hfull).symm v)) =
        wholeSpace s hfull ((wholeSpace s hfull).symm v)
      rw [wholeSpace_action,(wholeSpace s hfull).apply_symm_apply]
      exact hv l)

private theorem fixedQuotient_action (s : MovedSection ρ L)
    (hfull : Coinvariants.ker (ρ.comp L.subtype) = ⊤) (g : K) (v : V) :
    fixedQuotient s hfull ((fixedSpace ρ L).mkQ (ρ g v)) =
      s.central.quotientRepresentation g (fixedQuotient s hfull ((fixedSpace ρ L).mkQ v)) := by
  change Submodule.Quotient.mk (wholeSpace s hfull (ρ g v)) =
    Submodule.Quotient.mk (s.space.toRepresentation g (wholeSpace s hfull v))
  rw [wholeSpace_action]

private def canonicalField (F : BinaryField) : F.Carrier ≃+* Sieve.BinaryField F.degree := by
  let := Fintype.ofFinite F.Carrier
  let := Fintype.ofFinite (Sieve.BinaryField F.degree)
  apply FiniteField.ringEquivOfCardEq
  simpa only [←Nat.card_eq_fintype_card] using
    F.card_eq.trans (GaloisField.card 2 F.degree (by have := F.degree_pos; omega)).symm

private def vectorField {F E : Type*} [Field F] [Field E]
    [Module (ZMod 2) F] [Module (ZMod 2) E]
    (f : F ≃+* E) (n : ℕ) : (Fin n → F) ≃ₗ[ZMod 2] (Fin n → E) where
  toFun v i := f (v i)
  invFun v i := f.symm (v i)
  left_inv v := by ext i; exact f.symm_apply_apply _
  right_inv v := by ext i; exact f.apply_symm_apply _
  map_add' v w := by ext i; exact f.map_add _ _
  map_smul' c v := by ext i; exact ZMod.map_smul f c (v i)

private theorem vectorField_action {F E : Type*} [Field F] [Field E]
    [Module (ZMod 2) F] [Module (ZMod 2) E]
    (f : F ≃+* E) (n : ℕ) (g : Matrix.SpecialLinearGroup (Fin n) F) (v : Fin n → F) :
    vectorField f n (specialLinearNatural n g v) =
      specialLinearNatural n (Atlas.fieldEquivSL n f g) (vectorField f n v) := by
  ext i
  change f (∑ j, g.val i j * v j) = ∑ j, f (g.val i j) * f (v j)
  simp only [map_sum,map_mul]

private def derivedEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    commutator A ≃* commutator B :=
  (e.subgroupMap (commutator A)).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective,←_root_.commutator_def]))

private theorem natural_project (n : ℕ) [NeZero n]
    (g : SL n) (v : Vector n) :
    Sieve.natural n (slEquivPSL n g) v = linearNatural BinaryField.two n g v := by
  exact pslEquivLinear_project n g v

private theorem naturalDual_project (n : ℕ) [NeZero n]
    (g : SL n) (v : Vector n × Module.Dual (ZMod 2) (Vector n)) :
    ((Sieve.natural n).prod (Sieve.natural n).dual) (slEquivPSL n g) v =
      naturalPlusDual n g v := by
  apply Prod.ext
  · exact natural_project n g v.1
  · apply LinearMap.ext
    intro w
    change v.2 (Sieve.natural n ((slEquivPSL n g)⁻¹) w) =
      v.2 (linearNatural BinaryField.two n g⁻¹ w)
    rw [←map_inv,natural_project]
    rfl

private theorem irreducibleTable (s : MovedSection ρ L)
    (hfull : Coinvariants.ker (ρ.comp L.subtype) = ⊤)
    (a : ProjectiveLine.IrreducibleActionCase s.action L (offenderSubgroup s.action)) :
    Sieve.IrreducibleTable ρ L := by
  cases a with
  | linearTwo F _ e _ _ =>
    exact Or.inl (.linearTwo F.degree F.degree_pos (e.groupEquiv.trans (Atlas.fieldEquivSL 2 (canonicalField F))))
  | linearThree F _ e _ =>
    exact Or.inl (.linearThree F.degree F.degree_pos (e.groupEquiv.trans (Atlas.fieldEquivSL 3 (canonicalField F))))
  | symplectic F hd _ e _ =>
    exact Or.inl (.symplecticLarge F.degree hd (e.groupEquiv.trans
      (Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivSp (canonicalField F))))
  | symplecticTwo e _ =>
    exact Or.inl (.symplecticSmall (e.subgroupEquiv.trans (derivedEquiv
      (Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivSp (canonicalField BinaryField.two)))))
  | g2 F hd _ e _ _ =>
    exact Or.inl (.g2Large F.degree hd (e.groupEquiv.trans (Atlas.G2.fieldEquiv (canonicalField F))))
  | g2Two e _ _ =>
    exact Or.inl (.g2Small (e.subgroupEquiv.trans (derivedEquiv (Atlas.G2.fieldEquiv
      (canonicalField BinaryField.two)))))
  | symmetric n hn e _ _ =>
    rcases hn with rfl | rfl
    · exact Or.inl (.alternatingFive e.subgroupEquiv)
    · exact Or.inl (.alternatingSeven e.subgroupEquiv)
  | alternatingSix _ e _ _ => exact Or.inl (.alternatingSix e.groupEquiv)
  | alternatingSeven _ _ e _ _ _ => exact Or.inl (.alternatingSeven e)
  | tripleSix _ a _ =>
    let f := a.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (center L))
    have hk : f.ker = center L := by
      ext x
      exact a.quotientEquiv.map_eq_one_iff.trans (QuotientGroup.eq_one_iff x)
    exact Or.inl (.tripleSix f (a.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
      hk.le (by rw [hk,Nat.card_congr a.centerEquiv.toEquiv]; exact Nat.card_zmod 3))
  | binaryLinear n hn _ e _ =>
    let : NeZero n := ⟨by rcases hn with rfl | rfl <;> decide⟩
    have h : Nonempty (Sieve.NaturalQuotient ρ L n) := by
      refine ⟨⟨e.groupEquiv.trans (slEquivPSL n),(fixedQuotient s hfull).trans e.linearEquiv,?_⟩⟩
      intro l v
      change e.linearEquiv (fixedQuotient s hfull ((fixedSpace ρ L).mkQ (ρ l v))) = _
      rw [fixedQuotient_action]
      exact (e.intertwines l _).trans (natural_project n (e.groupEquiv l) _).symm
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  | orthogonalSix _ _ e _ _ =>
    refine Or.inr (Or.inr (Or.inr ⟨⟨e.groupEquiv,(fixedQuotient s hfull).trans e.linearEquiv,?_⟩⟩))
    intro l v
    change e.linearEquiv (fixedQuotient s hfull ((fixedSpace ρ L).mkQ (ρ l v))) = _
    rw [fixedQuotient_action]
    exact e.intertwines l _
  | symmetricEight _ e _ =>
    refine Or.inr (Or.inr (Or.inr ⟨⟨e.subgroupEquiv,(fixedQuotient s hfull).trans e.action.linearEquiv,?_⟩⟩))
    intro l v
    change e.action.linearEquiv (fixedQuotient s hfull ((fixedSpace ρ L).mkQ (ρ l v))) = _
    rw [fixedQuotient_action]
    exact (e.action.intertwines ⟨l,e.contained l.property⟩ _).trans (by rw [e.compatible]; rfl)
  | exteriorFive _ _ e _ _ _ => exact Or.inl (.linearFive (e.trans (slEquivPSL 5)))

/-- The corrected, proved quasisimple B.5 theorem supplies the exact table
on the original FF actor and its original module. -/
theorem sourceCases [Finite K] [Finite V]
    (hFF : FFInput KnownSimple.IsKnownSimple ρ L) : Sieve.SourceCases ρ L := by
  obtain ⟨s⟩ := SourceB5.classification.quasisimple K V ρ L
    ⟨inferInstance,hFF.faithful,hFF.quasisimple,hFF.sqtk,hFF.generalizedFitting,hFF.twoCore,hFF.offenders⟩
  cases s.clause_one with
  | irreducible _ _ _ a _ => exact Or.inl (irreducibleTable s.sectionData hFF.full a)
  | doubleThree F _ e _ _ =>
    let v := vectorField (canonicalField F) 3
    refine Or.inr (Or.inl ⟨F.degree,F.degree_pos,⟨{
      model := e.groupEquiv.trans (Atlas.fieldEquivSL 3 (canonicalField F))
      coordinates := ((wholeSpace s.sectionData hFF.full).trans e.linearEquiv).trans
        (LinearEquiv.piCongrRight (fun _ => v))
      equivariant := ?_ }⟩⟩)
    intro l w i
    change v (e.linearEquiv (wholeSpace s.sectionData hFF.full (ρ l w)) i) = _
    rw [wholeSpace_action]
    exact (congrArg (fun x => v (x i)) (e.intertwines l _)).trans
      (vectorField_action (canonicalField F) 3 _ _)
  | naturalDual n hn _ h =>
    obtain ⟨e⟩ := h
    let : NeZero n := ⟨by rcases hn with rfl | rfl <;> decide⟩
    have hcase : Nonempty (Sieve.NaturalAndDual ρ L n) := by
      refine ⟨⟨e.groupEquiv.trans (slEquivPSL n),(wholeSpace s.sectionData hFF.full).trans e.linearEquiv,?_⟩⟩
      intro l w
      change e.linearEquiv (wholeSpace s.sectionData hFF.full (ρ l w)) = _
      rw [wholeSpace_action]
      exact (e.intertwines l _).trans (naturalDual_project n (e.groupEquiv l) _).symm
    apply Or.inr ∘ Or.inr ∘ Or.inl
    rcases hn with rfl | rfl
    · exact Or.inl hcase
    · exact Or.inr hcase
  | repeatedNatural n r hn hr hb _ h =>
    obtain ⟨e⟩ := h
    let : NeZero n := ⟨by rcases hn with rfl | rfl <;> decide⟩
    have hcase : Nonempty (Sieve.IsomorphicNaturals ρ L n r) := by
      refine ⟨⟨e.groupEquiv.trans (slEquivPSL n),(wholeSpace s.sectionData hFF.full).trans e.linearEquiv,?_⟩⟩
      intro l w i
      change e.linearEquiv (wholeSpace s.sectionData hFF.full (ρ l w)) i = _
      rw [wholeSpace_action]
      exact (congrArg (fun x => x i) (e.intertwines l _)).trans
        (natural_project n (e.groupEquiv l) _).symm
    apply Or.inr ∘ Or.inr ∘ Or.inr
    rcases hn with rfl | rfl
    · exact Or.inl ⟨r,hr,hb,hcase⟩
    · exact Or.inr ⟨r,hr,hb,hcase⟩

/-- The existing degree-four, degree-five and degree-eight consumers can
use the proved table without a further source hypothesis. -/
theorem classification : Sieve.UniversalFFClassification.{u,v} := by
  intro K V _ _ _ _ _ ρ L h
  exact sourceCases h

/-- Actual application to the marked degree-eight offender component. -/
theorem degreeEight_unmarkedCases [Finite K] [Finite V]
    (hFF : FFInput KnownSimple.IsKnownSimple ρ L)
    (e : L ≃* alternatingGroup (Fin 8)) : UnmarkedCases ρ L :=
  Sieve.unmarkedCases classification universalNaturalCohomology hFF e

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs.FFClassification
