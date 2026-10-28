module

public import Theory.GroupTheory.NoncentralChiefRefinement.CentralQuotient
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Sections

/-!
# Chief sections inside an intersection layer

Let R be normal in J and suppose J/R has only central binary chief factors.
The diamond isomorphism and chief minimality show that every noncentral binary
chief interval survives in its intersection with R, with the full J-action.
No normality of J in a larger group is required.

For a homomorphism from R with kernel central in J, choose representatives of
two ordered chief sections in R and multiply their images. Reduction modulo
the later lower endpoint recovers the later coordinate; cancellation then
recovers the earlier one. This gives a literal set embedding without cardinal
estimates. The section isomorphisms preserve conjugation; the representative
choices in the product embedding need not be equivariant.

Source application: Aschbacher--Smith, combined manuscript (1 March 2004),
14.7.68(2), printed pp.1071--1072. The application R = J intersect U(E)
requires a separate proof of the central-chief quotient hypothesis.
-/

@[expose] public section

open Subgroup
namespace NoncentralChiefRefinement
variable {J M : Type*} [Group J] [Group M]

theorem chief_inf_center_le (A B : NormalNode J) (hAB : A ⋖ B)
    (hn : ¬ IsCentral A B) : B.val ⊓ center J ≤ A.val := by
  let Z : NormalNode J := ⟨center J, inferInstanceAs (center J).Normal⟩
  obtain he | he := hAB.eq_or_eq (c := A ⊔ (B ⊓ Z)) le_sup_left
    (sup_le hAB.le inf_le_left)
  · exact he ▸ (show B ⊓ Z ≤ A ⊔ (B ⊓ Z) from le_sup_right)
  · exfalso
    apply hn
    intro x hx
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' : b ∈ A.val ⊔ (B.val ⊓ center J) := by
      change b ∈ (A ⊔ (B ⊓ Z)).val
      rw [he]
      exact hb
    obtain ⟨a, ha, z, hz, rfl⟩ := mem_sup_of_normal_right.mp hb'
    have ha' : QuotientGroup.mk' A.val a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
    rw [map_mul, ha', one_mul]
    apply mem_center_iff.mpr
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective A.val q
    simpa only [← map_mul] using congrArg (QuotientGroup.mk' A.val)
      (mem_center_iff.mp hz.2 j)

def ambientSectionMap (A B : NormalNode J) : Section A B →* J ⧸ A.val :=
  QuotientGroup.lift _ ((QuotientGroup.mk' A.val).comp B.val.subtype) (by
    intro b hb
    exact (QuotientGroup.eq_one_iff _).mpr hb)

theorem ambientSectionMap_injective (A B : NormalNode J) :
    Function.Injective (ambientSectionMap A B) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  ext b
  exact (QuotientGroup.eq_one_iff (N := A.val) (b : J)).symm

@[simp] theorem ambientSectionMap_mk (A B : NormalNode J) (b : B.val) :
    ambientSectionMap A B (QuotientGroup.mk' _ b) = QuotientGroup.mk' A.val (b : J) := rfl

theorem restrictionSectionMap_surjective_of_sup (R A B : NormalNode J)
    (hAB : A ≤ B) (hs : B ≤ A ⊔ R) :
    Function.Surjective (restrictionSectionMap R.val A B) := by
  intro x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (A.val.subgroupOf B.val) x
  have hb : (b : J) ∈ A.val ⊔ (R.val ⊓ B.val) := by
    have he : (A ⊔ R) ⊓ B = A ⊔ (R ⊓ B) := sup_inf_assoc_of_le R hAB
    change (b : J) ∈ (A ⊔ (R ⊓ B)).val
    rw [← he]
    exact ⟨hs b.property, b.property⟩
  obtain ⟨a, ha, c, hc, hac⟩ := mem_sup_of_normal_right.mp hb
  refine ⟨QuotientGroup.mk' _ ⟨⟨c, hc.1⟩, hc.2⟩, ?_⟩
  rw [restrictionSectionMap_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  change c / (b : J) ∈ A.val
  rw [← hac]
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_inv_cancel_left] using A.val.inv_mem ha

noncomputable def intersectionRepresentative (R A B : NormalNode J)
    (hAB : A ≤ B) (hs : B ≤ A ⊔ R) (x : Section A B) :
    (restrictNormalNode R.val B).val :=
  (Function.surjInv (restrictionSectionMap_surjective_of_sup R A B hAB hs) x).out

theorem intersectionRepresentative_spec (R A B : NormalNode J)
    (hAB : A ≤ B) (hs : B ≤ A ⊔ R) (x : Section A B) :
    QuotientGroup.mk' A.val (intersectionRepresentative R A B hAB hs x).val.val =
      ambientSectionMap A B x := by
  have h := Function.surjInv_eq
    (restrictionSectionMap_surjective_of_sup R A B hAB hs) x
  have ho := QuotientGroup.out_eq'
    (Function.surjInv (restrictionSectionMap_surjective_of_sup R A B hAB hs) x)
  rw [← ho] at h
  change restrictionSectionMap R.val A B
    (QuotientGroup.mk' _ (intersectionRepresentative R A B hAB hs x)) = x at h
  rw [restrictionSectionMap_mk] at h
  exact congrArg (ambientSectionMap A B) h

private theorem quotient_eq_of_map_eq (R A B : NormalNode J) (hAB : A ⋖ B)
    (hn : ¬ IsCentral A B) (f : R.val →* M)
    (hk : ∀ r : R.val, f r = 1 → (r : J) ∈ center J)
    (r t : R.val) (hr : (r : J) ∈ B.val) (ht : (t : J) ∈ B.val)
    (he : f r = f t) : QuotientGroup.mk' A.val (r : J) =
      QuotientGroup.mk' A.val (t : J) := by
  apply QuotientGroup.eq_iff_div_mem.mpr
  exact chief_inf_center_le A B hAB hn
    ⟨B.val.div_mem hr ht, hk (r / t) (by simp only [map_div, he, div_self'])⟩

noncomputable def intersectionPairMap (R A B C D : NormalNode J)
    (hAB : A ≤ B) (hCD : C ≤ D) (hsB : B ≤ A ⊔ R) (hsD : D ≤ C ⊔ R)
    (f : R.val →* M) (x : Section A B × Section C D) : M :=
  f (intersectionRepresentative R A B hAB hsB x.1).val *
    f (intersectionRepresentative R C D hCD hsD x.2).val

theorem intersectionPairMap_injective (R A B C D : NormalNode J)
    (hAB : A ⋖ B) (hCD : C ⋖ D) (hBC : B ≤ C)
    (hnB : ¬ IsCentral A B) (hnD : ¬ IsCentral C D)
    (hsB : B ≤ A ⊔ R) (hsD : D ≤ C ⊔ R)
    (f : R.val →* M) (hk : ∀ r : R.val, f r = 1 → (r : J) ∈ center J) :
    Function.Injective (intersectionPairMap R A B C D hAB.le hCD.le hsB hsD f) := by
  intro x y he
  let a := intersectionRepresentative R A B hAB.le hsB x.1
  let b := intersectionRepresentative R C D hCD.le hsD x.2
  let c := intersectionRepresentative R A B hAB.le hsB y.1
  let d := intersectionRepresentative R C D hCD.le hsD y.2
  have hab : f (a.val * b.val) = f (c.val * d.val) := by
    change f a.val * f b.val = f c.val * f d.val at he
    simpa only [map_mul] using he
  have hq := quotient_eq_of_map_eq R C D hCD hnD f hk (a.val * b.val)
    (c.val * d.val) (D.val.mul_mem (hCD.le (hBC a.property)) b.property)
      (D.val.mul_mem (hCD.le (hBC c.property)) d.property) hab
  have ha : QuotientGroup.mk' C.val (a.val.val) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hBC a.property)
  have hc : QuotientGroup.mk' C.val (c.val.val) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hBC c.property)
  change QuotientGroup.mk' C.val (a.val.val * b.val.val) =
    QuotientGroup.mk' C.val (c.val.val * d.val.val) at hq
  simp only [map_mul, ha, hc, one_mul] at hq
  have hxy2 : x.2 = y.2 := by
    apply ambientSectionMap_injective C D
    simpa only [b, d, intersectionRepresentative_spec] using hq
  have hbd : b = d := by simp only [b, d, hxy2]
  have hac : f a.val = f c.val := by
    rw [map_mul, map_mul, hbd] at hab
    exact mul_right_cancel hab
  have hq1 := quotient_eq_of_map_eq R A B hAB hnB f hk a.val c.val
    a.property c.property hac
  have hxy1 : x.1 = y.1 := by
    apply ambientSectionMap_injective A B
    simpa only [a, c, intersectionRepresentative_spec] using hq1
  exact Prod.ext hxy1 hxy2

/-- Intersection preserves the original actor, not just the subgroup actor. -/
noncomputable def intersectionSectionEquiv (R A B : NormalNode J)
    (hAB : A ≤ B) (hs : B ≤ A ⊔ R) :
    SectionEquiv (A ⊓ R) (B ⊓ R) A B := by
  have hu : A ⊔ (B ⊓ R) = B := by
    rw [inf_comm B R, ← sup_inf_assoc_of_le R hAB, inf_eq_right.mpr hs]
  have hl : A ⊓ (B ⊓ R) = A ⊓ R := by rw [← inf_assoc, inf_eq_left.mpr hAB]
  have e := diamondInverse A (B ⊓ R)
  rw [hu, hl] at e
  exact e

/-- Central binary chief factors above R force every counted section into R. -/
theorem chief_le_sup_of_central_quotient (R A B : NormalNode J)
    (hR : HasCentralPChiefFactors 2 (J ⧸ R.val))
    (hAB : A ⋖ B) (hn : IsNoncentralTwo A B) : B ≤ A ⊔ R := by
  by_contra hs
  have hl : (A ⊔ R) ⊓ B = A := by
    obtain he | he := hAB.eq_or_eq (c := (A ⊔ R) ⊓ B)
      (le_inf le_sup_left hAB.le) inf_le_right
    · exact he
    · exact (hs (he ▸ (show (A ⊔ R) ⊓ B ≤ A ⊔ R from inf_le_left))).elim
  have hc : (A ⊔ R) ⋖ (A ⊔ R) ⊔ B :=
    covBy_sup_of_inf_covBy_right (by rw [hl]; exact hAB)
  have e : SectionEquiv A B (A ⊔ R) ((A ⊔ R) ⊔ B) := by
    have e := diamondInverse (A ⊔ R) B
    rw [hl] at e
    exact e
  have hRQ : R ≤ A ⊔ R := le_sup_right
  have hRD : R ≤ (A ⊔ R) ⊔ B := hRQ.trans le_sup_left
  have hq := (quotientImage_covBy_iff R _ _ hRQ hRD).mpr hc
  have hchief := (covBy_iff_isChief _ _).mp hq
  have hp := ((e.isPGroup_iff 2).mp hn.1).of_equiv
    (quotientSectionEquiv R _ _ hRQ)
  have hz : IsCentral (quotientImage R (A ⊔ R))
      (quotientImage R ((A ⊔ R) ⊔ B)) :=
    hR _ _ inferInstance inferInstance hchief.lt hchief.minimal hp
  exact hn.2 (e.isCentral_iff.mpr ((quotient_isCentral_iff R _ _ hRQ).mp hz))

/-- Intersect the original chief series with R, retaining the original actor J.
Repeated terms are allowed. -/
def ChiefSeries.intersectionFiltration (s : ChiefSeries J) (R : NormalNode J) :
    Filtration J s.length where
  term i := s i ⊓ R
  monotone := fun _ _ h => inf_le_inf_right R (s.strictMono.monotone h)

/-- Each counted interval survives equivariantly in the literal intersection filtration. -/
noncomputable def ChiefSeries.intersectionFactorEquiv (s : ChiefSeries J)
    (R : NormalNode J) (hR : HasCentralPChiefFactors 2 (J ⧸ R.val))
    (i : Fin s.length) (hi : IsNoncentralTwo (s i.castSucc) (s i.succ)) :
    SectionEquiv ((s.intersectionFiltration R).term i.castSucc)
      ((s.intersectionFiltration R).term i.succ) (s i.castSucc) (s i.succ) :=
  intersectionSectionEquiv R _ _ (s.step i).le
    (chief_le_sup_of_central_quotient R _ _ hR (s.step i) hi)

/-- The ordered representatives also embed pairs from arbitrary chief-series indices. -/
noncomputable def ChiefSeries.intersectionPairEmbedding (s : ChiefSeries J)
    (R : NormalNode J) (hR : HasCentralPChiefFactors 2 (J ⧸ R.val))
    (f : R.val →* M) (hk : ∀ r : R.val, f r = 1 → (r : J) ∈ center J)
    (i j : Fin s.length) (hij : i ≠ j)
    (hi : IsNoncentralTwo (s i.castSucc) (s i.succ))
    (hj : IsNoncentralTwo (s j.castSucc) (s j.succ)) :
    Section (s i.castSucc) (s i.succ) × Section (s j.castSucc) (s j.succ) ↪ M := by
  have hsi := chief_le_sup_of_central_quotient R _ _ hR (s.step i) hi
  have hsj := chief_le_sup_of_central_quotient R _ _ hR (s.step j) hj
  by_cases hlt : i < j
  · have hmid : s i.succ ≤ s j.castSucc := s.strictMono.monotone (by
      change i.val + 1 ≤ j.val
      exact hlt)
    exact ⟨intersectionPairMap R _ _ _ _ (s.step i).le (s.step j).le hsi hsj f,
      intersectionPairMap_injective R _ _ _ _ (s.step i) (s.step j) hmid
        hi.2 hj.2 hsi hsj f hk⟩
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
    have hmid : s j.succ ≤ s i.castSucc := s.strictMono.monotone (by
      change j.val + 1 ≤ i.val
      exact hji)
    exact (Equiv.prodComm _ _).toEmbedding.trans
      ⟨intersectionPairMap R _ _ _ _ (s.step j).le (s.step i).le hsj hsi f,
        intersectionPairMap_injective R _ _ _ _ (s.step j) (s.step i) hmid
          hj.2 hi.2 hsj hsi f hk⟩

end NoncentralChiefRefinement
