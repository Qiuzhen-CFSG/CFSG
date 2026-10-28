module
public import Theory.SpecificGroups.ClassicalOrthogonal.A02ParabolicSections.SourceGeometry
public import Theory.SpecificGroups.ClassicalOrthogonal.TwoRankLower.PlusOdd
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.Tactic.FinCases

/-!
# Elementary eights in all split orthogonal carriers

Three binary Siegel parameters give a faithful elementary eight in the split
six-space. Literal tail maps preserve it in larger binary spaces; in odd
characteristic the five-space block proved in `PlusOdd` gives the same bound.
Source: GLS3 §2.7; Aschbacher–Smith A.2.12, printed p.36.
-/
@[expose] public noncomputable section
namespace ClassicalOrthogonal.TwoRank
open A02ParabolicSections TheoremDRootNormalizer
variable {F : Type} [Field F] [CharP F 2]

def evenParameters (v : Fin 3 → ZMod 2) : VectorD 3 F :=
  (ZMod.castHom (dvd_refl 2) F) (v 0) • e 1 +
  (ZMod.castHom (dvd_refl 2) F) (v 1) • f 1 +
  (ZMod.castHom (dvd_refl 2) F) (v 2) • e 2

theorem evenParameters_perp (v : Fin 3 → ZMod 2) :
    (formD 3 F).polarBilin (e 0) (evenParameters v) = 0 := by
  simp only [evenParameters,map_add,map_smul,smul_eq_mul,
    polarD_e,polarD_f]
  simp [e]

def evenParameterHom : (Fin 3 → ZMod 2) →+ ((formD 3 F).polarBilin (e 0)).ker where
  toFun v := ⟨evenParameters v,evenParameters_perp v⟩
  map_zero' := by apply Subtype.ext; simp [evenParameters]
  map_add' v w := by
    apply Subtype.ext
    change evenParameters (v+w) = evenParameters v + evenParameters w
    simp only [evenParameters,Pi.add_apply,map_add,add_smul]
    abel

def evenEight : Multiplicative (Fin 3 → ZMod 2) →* OmegaPlus 3 F :=
  (ClassicalOrthogonal.A02ParabolicSections.rootHom (formD 3 F) (e 0) (formD_e 0)).comp evenParameterHom.toMultiplicative

theorem evenEight_injective : Function.Injective (evenEight (F:=F)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro v hv
  have he := congrArg (fun g : OmegaPlus 3 F => g.val.val (f 0)) hv
  change Quadratic.siegel (formD 3 F) (e 0) (evenParameters v.toAdd) (f 0) = f 0 at he
  simp only [Quadratic.siegel] at he
  rw [polarD_e] at he
  have h1 := congrFun he (.inl 1)
  have h2 := congrFun he (.inr 1)
  have h3 := congrFun he (.inl 2)
  have hc0 : (ZMod.castHom (dvd_refl 2) F) (v.toAdd 0) = 0 := by
    simpa [Quadratic.siegel,evenParameters,polarD_e,polarD_f,e,f] using h1
  have hc1 : (ZMod.castHom (dvd_refl 2) F) (v.toAdd 1) = 0 := by
    simpa [Quadratic.siegel,evenParameters,polarD_e,polarD_f,e,f] using h2
  have hc2 : (ZMod.castHom (dvd_refl 2) F) (v.toAdd 2) = 0 := by
    simpa [Quadratic.siegel,evenParameters,polarD_e,polarD_f,e,f] using h3
  apply Multiplicative.toAdd.injective
  funext i
  change v.toAdd i = 0
  apply ZMod.castHom_injective F
  rw [map_zero]
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2

/-- Three singular-root parameters give an elementary eight in the actual split six-space. -/
theorem plus_even_three_le [Finite F] : 3 ≤ primeRank 2 (POmegaPlus 3 F) := by
  let j := (projectiveElementaryMap (formD 3 F)).comp (evenEight (F:=F))
  have hj : Function.Injective j := (ClassicalOrthogonal.TheoremDRootNormalizer.elementaryProjective_injective _).comp evenEight_injective
  apply primeRank_ge_of_elementary_embedding (f:=j) (hf:=hj)
  · intro v
    apply Multiplicative.toAdd.injective
    funext i
    exact ZModModule.char_nsmul_eq_zero 2 (v.toAdd i)
  · simp [Nat.card_eq_fintype_card]
/-- The actual elementary eight embeds in all higher split ranks. -/
theorem plus_binary_three_le [Finite F] {r : ℕ} (hr : 3 ≤ r) :
    3 ≤ primeRank 2 (POmegaPlus r F) := by
  by_cases h3 : r=3
  · subst r
    exact plus_even_three_le
  obtain ⟨n,rfl⟩ : ∃ n, r=3+n+1 := ⟨r-4,by omega⟩
  exact (plus_even_three_le (F:=F)).trans (Theory.GroupTheory.primeRank_le_of_injective 2
    (ClassicalOrthogonal.A02ParabolicSections.projectiveTail 3 n)
    (ClassicalOrthogonal.A02ParabolicSections.projectiveTail_injective 3 n))

omit [CharP F 2] in
/-- Every actual split orthogonal carrier in the catalogue range contains an elementary eight. -/
theorem plus_three_le [Finite F] {r : ℕ} (hr : 3 ≤ r) :
    3 ≤ primeRank 2 (POmegaPlus r F) := by
  by_cases h2 : (2:F)=0
  · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2
    exact plus_binary_three_le hr
  · exact plus_odd_three_le h2 hr
end ClassicalOrthogonal.TwoRank
