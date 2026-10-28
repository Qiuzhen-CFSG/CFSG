module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData

/-!
# Ordered coordinates for the root-defined Ree subgroups

An ordering of a root support defines an actual product of the corresponding
split F₄ root matrices. Its fixed parameter locus uses equality under the
concrete Ree twist, so it retains all corrections caused by noncommuting
root factors. Unique split factorization identifies this locus with the
fixed subgroup. No factorization or dimension assertion is assumed in the
definitions.

The positive support and the two radical supports share this construction.
The intended fixed dimensions are 12, 10 and 11, respectively; these numbers
only specify the targets of the remaining coordinate calculations.
Source: the root construction for Aschbacher–Smith F.1.12(I)(5), printed
p.263 (PDF p.274) of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics.RadicalCoordinates

open LargeLocalSeeds Subgroup
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

/-- The two field maps on a dual pair are inverse, including at `m = 0`. -/
theorem rootFieldEnd_twice (m : ℕ) (r : F4Chevalley.Root)
    (t : CoefficientField m) :
    rootFieldEnd m (exceptionalRootPermutation r) (rootFieldEnd m r t) = t := by
  classical
  by_cases hr : IsLongRoot r
  · have hs := (exceptionalRootPermutation_long_iff r).mp hr
    simp only [rootFieldEnd, if_pos hr, if_neg hs, titsEnd_apply,
      iterateFrobenius_def, ← pow_mul, ← pow_add]
    convert field_pow m t using 1
    congr 2
    omega
  · have hs := (exceptionalRootPermutation_short_iff r).mp hr
    simp only [rootFieldEnd, if_neg hr, if_pos hs, titsEnd_apply,
      iterateFrobenius_def, ← pow_mul, ← pow_add]
    convert field_pow m t using 1
    congr 2
    omega

/-- Scalar fixed equations for one dual pair. This is not a group parametrization:
noncommuting root factors can contribute additional correction terms. -/
def PairedParameters (m : ℕ) (r : F4Chevalley.Root) :=
  {p : CoefficientField m × CoefficientField m //
    rootFieldEnd m r p.1 = p.2 ∧
    rootFieldEnd m (exceptionalRootPermutation r) p.2 = p.1}

/-- One freely chosen scalar determines the pair of compatible scalars. -/
def pairedParametersEquiv (m : ℕ) (r : F4Chevalley.Root) :
    CoefficientField m ≃ PairedParameters m r where
  toFun t := ⟨(t, rootFieldEnd m r t), rfl, rootFieldEnd_twice m r t⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext rfl p.property.1)

theorem card_pairedParameters (m : ℕ) (r : F4Chevalley.Root) :
    Nat.card (PairedParameters m r) = 2 ^ (2 * m + 1) :=
  (Nat.card_congr (pairedParametersEquiv m r).symm).trans (field_card m)

/-- The three closed positive-root supports needed by the local order calculation. -/
inductive Support where
  | positive
  | radical (side : Side)

def Supported : Support → F4Chevalley.Root → Prop
  | .positive, r => typeF4RootPairing_base.IsPos r
  | .radical s, r => IsRadicalRoot s r

abbrev Root (k : Support) := {r : F4Chevalley.Root // Supported k r}

/-- Every supported root occurs exactly once in an ordering. -/
abbrev RootOrder (k : Support) := Fin (Nat.card (Root k)) ≃ Root k

theorem rootOrder_nonempty (k : Support) : Nonempty (RootOrder k) :=
  ⟨(Finite.equivFin (Root k)).symm⟩

abbrev Parameters (m : ℕ) (k : Support) := Root k → CoefficientField m

def splitSubgroup (m : ℕ) : Support → Subgroup (SplitGroup m)
  | .positive => splitUnipotent m
  | .radical s => splitRadical m s

def fixedSubgroup (m : ℕ) (k : Support) : Subgroup (Model m) :=
  (splitSubgroup m k).comap (toSplitGroup m)

@[simp] theorem fixedSubgroup_positive (m : ℕ) :
    fixedSubgroup m .positive = unipotent m := rfl

@[simp] theorem fixedSubgroup_radical (m : ℕ) (s : Side) :
    fixedSubgroup m (.radical s) = radical m s := rfl

/-- Target dimensions, whose realization requires the fixed-coordinate calculation. -/
def fixedDimension : Support → ℕ
  | .positive => 12
  | .radical .suzuki => 10
  | .radical .linear => 11

def word (m : ℕ) {k : Support} (e : RootOrder k) (t : Parameters m k) : SplitGroup m :=
  (List.ofFn fun i => rootGeneratorInGroup m (e i).val (t (e i))).prod

theorem word_mem (m : ℕ) {k : Support} (e : RootOrder k) (t : Parameters m k) :
    word m e t ∈ splitSubgroup m k := by
  apply (splitSubgroup m k).list_prod_mem
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  cases k <;> exact Subgroup.subset_closure ⟨_, _, (e i).property, rfl⟩

def wordInSubgroup (m : ℕ) {k : Support} (e : RootOrder k) :
    Parameters m k → splitSubgroup m k := fun t => ⟨word m e t, word_mem m e t⟩

/-- This formula preserves the word order; it performs no implicit collection. -/
theorem reeTwist_word (m : ℕ) {k : Support} (e : RootOrder k) (t : Parameters m k) :
    reeTwist m (word m e t) =
      (List.ofFn fun i => rootGeneratorInGroup m (exceptionalRootPermutation (e i).val)
        (rootFieldEnd m (e i).val (t (e i)))).prod := by
  rw [word, map_list_prod, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact (reeTwist_rootGenerator m _ _).trans
    (congrArg (rootGeneratorInGroup m _) (rootFieldEnd_apply m _ _).symm)

/-- The fixed locus of the actual product, including its commutator corrections. -/
def FixedParameters (m : ℕ) {k : Support} (e : RootOrder k) :=
  {t : Parameters m k // reeTwist m (word m e t) = word m e t}

def fixedWord (m : ℕ) {k : Support} (e : RootOrder k) :
    FixedParameters m e → fixedSubgroup m k :=
  fun t => ⟨⟨word m e t.val, (ReeF4.mem_fixedSubgroup m _).mpr t.property⟩, by
    change toSplitGroup m _ ∈ splitSubgroup m k
    rw [toSplitGroup_apply]
    exact word_mem m e t.val⟩

@[simp] theorem fixedWord_coe (m : ℕ) {k : Support} (e : RootOrder k)
    (t : FixedParameters m e) : toSplitGroup m (fixedWord m e t) = word m e t.val := by
  rw [toSplitGroup_apply]
  rfl

/-- Unique split coordinates restrict to unique coordinates on the fixed locus. -/
theorem fixedWord_bijective (m : ℕ) {k : Support} (e : RootOrder k)
    (h : Function.Bijective (wordInSubgroup m e)) : Function.Bijective (fixedWord m e) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply h.1
    exact Subtype.ext (congrArg (fun z : fixedSubgroup m k => z.val.val) hxy)
  · intro x
    obtain ⟨t, ht⟩ := h.2 ⟨x.val.val, by
      simpa only [fixedSubgroup, mem_comap, toSplitGroup_apply] using x.property⟩
    have hw : word m e t = x.val.val := congrArg Subtype.val ht
    have hf : reeTwist m (word m e t) = word m e t := by
      rw [hw]
      exact (ReeF4.mem_fixedSubgroup m _).mp x.val.property
    exact ⟨⟨t, hf⟩, Subtype.ext (Subtype.ext hw)⟩

def fixedEquiv (m : ℕ) {k : Support} (e : RootOrder k)
    (h : Function.Bijective (wordInSubgroup m e)) :
    FixedParameters m e ≃ fixedSubgroup m k :=
  Equiv.ofBijective (fixedWord m e) (fixedWord_bijective m e h)

/-- One may solve the fixed equations in any ordering with unique split coordinates. -/
def changeOrder (m : ℕ) {k : Support} (e f : RootOrder k)
    (he : Function.Bijective (wordInSubgroup m e))
    (hf : Function.Bijective (wordInSubgroup m f)) :
    FixedParameters m e ≃ FixedParameters m f :=
  (fixedEquiv m e he).trans (fixedEquiv m f hf).symm

theorem card_fixedSubgroup (m : ℕ) {k : Support} (e : RootOrder k)
    (h : Function.Bijective (wordInSubgroup m e)) :
    Nat.card (fixedSubgroup m k) = Nat.card (FixedParameters m e) :=
  (Nat.card_congr (fixedEquiv m e h)).symm

end ReeF4.Parabolics.RadicalCoordinates
