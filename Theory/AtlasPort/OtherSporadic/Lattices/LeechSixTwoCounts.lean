/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechSixTwoCounts.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechSixTwo

/-!
Parametrization and counting of the six-two vector family.
Recovery of the distinguished coordinate, support, and signs proves injectivity.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem supportWord_injective : Function.Injective supportWord := by
  intro T U h
  have hh := congrArg support h
  simpa [supportWord,support] using hh

theorem sixTwo_support_six (T : Finset Omega) (a : T) (s : T → Bit) :
    evenMagnitudeSupport (sixTwoVector T a s) 6 = {a.val} := by
  ext i
  simp only [evenMagnitudeSupport]
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ,true_and,Finset.mem_singleton,sixTwoVector,signedSupport]
  by_cases hi : i = a.val
  · subst i
    simp only [a.prop,dif_pos,ite_true]
    split_ifs <;> norm_num
  · split_ifs <;> simp_all

theorem sixTwo_signs_injective (T : Finset Omega) (a : T) : Function.Injective (sixTwoVector T a) := by
  intro s t h
  funext i
  have hi := congrFun h i.val
  simp only [sixTwoVector,signedSupport,dif_pos i.prop] at hi
  rcases bit_cases (s i) with hs | hs <;> rcases bit_cases (t i) with ht | ht <;>
    simp_all <;> split_ifs at hi

instance (T : Finset Omega) (b : Bit) : Fintype (ParitySigns T b) :=
  inferInstanceAs (Fintype {s : T → Bit // ∑ i, s i = b})

abbrev SixTwoParameters := (T : CodeSupports 8) × (T.val × ParitySigns T.val 1)
instance : Fintype SixTwoParameters :=
  inferInstanceAs (Fintype ((T : CodeSupports 8) × (T.val × {s : T.val → Bit // ∑ i, s i = 1})))

def sixTwoFamilyVector (p : SixTwoParameters) := sixTwoVector p.1.val p.2.1 p.2.2.val

theorem sixTwoFamilyVector_injective : Function.Injective sixTwoFamilyVector := by
  rintro ⟨⟨T,hT⟩,a,s⟩ ⟨⟨U,hU⟩,b,t⟩ h
  have hr := congrArg (fun x => halfResidue x 0) h
  simp only [sixTwoFamilyVector,sixTwo_residue] at hr
  have ht := supportWord_injective hr
  cases ht
  have ha := congrArg (fun x => evenMagnitudeSupport x 6) h
  simp only [sixTwoFamilyVector,sixTwo_support_six] at ha
  have hab : a = b := Subtype.ext (Finset.singleton_injective ha)
  cases hab
  have hs : s = t := Subtype.ext (sixTwo_signs_injective T a h)
  cases hs
  rfl

theorem sixTwoParameters_card : Nat.card SixTwoParameters = 777216 := by
  rw [Nat.card_sigma]
  have hh (T : CodeSupports 8) : Nat.card (T.val × ParitySigns T.val 1) = 1024 := by
    rw [Nat.card_prod,paritySigns_card T.val 1 (by simp [T.prop.2]),Nat.card_eq_fintype_card]
    simp [T.prop.2]
  simp_rw [hh]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card,codeSupports_card,golay_weight_distribution]
  norm_num

def sixTwoFamily : Finset IntegerCoordinates := Finset.univ.image sixTwoFamilyVector

theorem sixTwoFamily_card : sixTwoFamily.card = 777216 := by
  rw [sixTwoFamily,Finset.card_image_of_injective _ sixTwoFamilyVector_injective,
    Finset.card_univ,← Nat.card_eq_fintype_card,sixTwoParameters_card]

theorem sixTwoFamily_properties (x : IntegerCoordinates) (hx : x ∈ sixTwoFamily) :
    x ∈ leech ∧ (∀ i, x i % 2 = 0) ∧ integerDot x x = 64 := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
  refine ⟨(sixTwo_mem_iff _ _ _ p.1.prop.1).mpr p.2.2.prop,sixTwo_parity _ _ _,?_⟩
  change integerDot (sixTwoVector _ _ _) (sixTwoVector _ _ _) = _
  rw [sixTwo_norm,p.1.prop.2]
  norm_num

end Atlas.Lattices
