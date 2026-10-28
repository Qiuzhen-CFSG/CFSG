module
public import Theory.SpecificGroups.ClassicalOrthogonal.TwoRankLower.Plus
public import Theory.SpecificGroups.ClassicalOrthogonal.A02ParabolicSections.SourceGeometry.OmegaRoot
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.MinusEmbedding

/-!
# Elementary eights in binary minus orthogonal carriers of rank at least four

Each of three split Siegel directions is an explicit commutator, using a
spare hyperbolic pair. Their additive elementary eight embeds through full
orthogonal tail maps and extension by the anisotropic plane. The literal
minus scalar quotient is injective in characteristic two.
Source: GLS3 §2.7; Aschbacher–Smith A.2.12, printed p.36.
-/
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace ClassicalOrthogonal.TwoRank
open Theory.AlgebraicGroup A02ParabolicSections TheoremDRootNormalizer
variable {F : Type} [Field F]

theorem root_e_commutator (a : F) {i j k : Fin 3}
    (_hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (A02ParabolicSections.root (formD 3 F) (e i) (a • e j) (formD_e i)
      (by simp only [map_smul,smul_eq_mul,polarD_e]; simp [e])).val ∈ commutator (quadraticIsometrySubgroup (formD 3 F)) := by
  apply singular_root_mem_omega (formD 3 F) (e i) (a • e j) (e k) (f k)
    (formD_e i) (by rw [QuadraticMap.map_smul,formD_e]; simp) (formD_f k)
  all_goals simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,polarD_e,polarD_f]
  all_goals simp [e,f,Ne.symm _hij,Ne.symm hik,Ne.symm hjk]

theorem root_f_commutator (a : F) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (A02ParabolicSections.root (formD 3 F) (e i) (a • f j) (formD_e i)
      (by simp only [map_smul,smul_eq_mul,polarD_f]; simp [e,Ne.symm hij])).val ∈ commutator (quadraticIsometrySubgroup (formD 3 F)) := by
  apply singular_root_mem_omega (formD 3 F) (e i) (a • f j) (e k) (f k)
    (formD_e i) (by rw [QuadraticMap.map_smul,formD_f]; simp) (formD_f k)
  all_goals simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,polarD_e,polarD_f]
  all_goals simp [e,f,Ne.symm hij,Ne.symm hik,Ne.symm hjk]

variable [CharP F 2]
theorem evenEight_mem_commutator (v : Multiplicative (Fin 3 → ZMod 2)) :
    (evenEight (F:=F) v).val ∈ commutator (quadraticIsometrySubgroup (formD 3 F)) := by
  let a : F := ZMod.castHom (dvd_refl 2) F (v.toAdd 0)
  let b : F := ZMod.castHom (dvd_refl 2) F (v.toAdd 1)
  let c : F := ZMod.castHom (dvd_refl 2) F (v.toAdd 2)
  have ha : (formD 3 F).polarBilin (e 0) (a • e 1)=0 := by simp only [map_smul,smul_eq_mul,polarD_e]; simp [e]
  have hb : (formD 3 F).polarBilin (e 0) (b • f 1)=0 := by simp only [map_smul,smul_eq_mul,polarD_f]; simp [e]
  have hc : (formD 3 F).polarBilin (e 0) (c • e 2)=0 := by simp only [map_smul,smul_eq_mul,polarD_e]; simp [e]
  have hab : (formD 3 F).polarBilin (e 0) (a • e 1+b • f 1)=0 := by rw [map_add,ha,hb,add_zero]
  have he : evenEight (F:=F) v =
      (A02ParabolicSections.root (formD 3 F) (e 0) (a • e 1) (formD_e 0) ha *
       A02ParabolicSections.root (formD 3 F) (e 0) (b • f 1) (formD_e 0) hb) *
       A02ParabolicSections.root (formD 3 F) (e 0) (c • e 2) (formD_e 0) hc := by
    change A02ParabolicSections.root (formD 3 F) (e 0) (a • e 1+b • f 1+c • e 2) _ _ = _
    rw [root_add _ _ _ _ _ hab hc,root_add _ _ _ _ _ ha hb]
  rw [he]
  apply Subgroup.mul_mem _
  · apply Subgroup.mul_mem _
    · exact root_e_commutator a (k:=2) (by decide) (by decide) (by decide)
    · exact root_f_commutator b (k:=2) (by decide) (by decide) (by decide)
  · exact root_e_commutator c (k:=1) (by decide) (by decide) (by decide)

def evenEightCommutator : Multiplicative (Fin 3 → ZMod 2) →*
    commutator (quadraticIsometrySubgroup (formD 3 F)) :=
  ((elementarySubgroup (formD 3 F)).subtype.comp (evenEight (F:=F))).codRestrict _ (evenEight_mem_commutator (F:=F))

theorem evenEightCommutator_injective : Function.Injective (evenEightCommutator (F:=F)) := by
  intro v w h
  apply evenEight_injective (F:=F)
  apply Subtype.ext
  exact congrArg (fun g : commutator (quadraticIsometrySubgroup (formD 3 F)) => g.val) h

omit [CharP F 2] in
def splitFullTail : (n : ℕ) → quadraticIsometrySubgroup (formD 3 F) →*
    quadraticIsometrySubgroup (formD (3+n) F)
  | 0 => MonoidHom.id _
  | n+1 => (A02ParabolicSections.tailFull (3+n)).comp (splitFullTail n)

omit [CharP F 2] in
theorem splitFullTail_injective (n : ℕ) : Function.Injective (splitFullTail (F:=F) n) := by
  induction n with
  | zero => exact Function.injective_id
  | succ n ih => exact (A02ParabolicSections.tailFull_injective _).comp ih

omit [CharP F 2] in
def splitCommutatorTail (n : ℕ) : commutator (quadraticIsometrySubgroup (formD 3 F)) →*
    commutator (quadraticIsometrySubgroup (formD (3+n) F)) :=
  ((splitFullTail n).comp (commutator (quadraticIsometrySubgroup (formD 3 F))).subtype).codRestrict _ (by
    intro g
    have hm := Subgroup.mem_map_of_mem (splitFullTail n) g.prop
    rw [map_commutator_eq] at hm
    exact Subgroup.commutator_mono le_top le_top hm)

omit [CharP F 2] in
theorem splitCommutatorTail_injective (n : ℕ) : Function.Injective (splitCommutatorTail (F:=F) n) := by
  intro x y h
  apply Subtype.ext
  exact splitFullTail_injective n (congrArg
    (fun g : commutator (quadraticIsometrySubgroup (formD (3+n) F)) => g.val) h)

/-- Three actual split-root commutators survive extension by the anisotropic plane. -/
theorem minus_binary_four_le [Finite F] {r : ℕ} (hr : 4 ≤ r) :
    3 ≤ primeRank 2 (ClassicalGroup.POmegaMinus r F) := by
  obtain ⟨n,rfl⟩ : ∃ n, r=3+n+1 := ⟨r-4,by omega⟩
  let j := (HigherRanks.minusProjectiveHom (F:=F) (3+n+1)).comp
    ((splitCommutatorTail n).comp (evenEightCommutator (F:=F)))
  have hj : Function.Injective j := (HigherRanks.minusProjectiveHom_injective _).comp
    ((splitCommutatorTail_injective n).comp evenEightCommutator_injective)
  apply primeRank_ge_of_elementary_embedding (f:=j) (hf:=hj)
  · intro v
    apply Multiplicative.toAdd.injective
    funext i
    exact ZModModule.char_nsmul_eq_zero 2 (v.toAdd i)
  · simp [Nat.card_eq_fintype_card]
end ClassicalOrthogonal.TwoRank
