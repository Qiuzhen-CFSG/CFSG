module

public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.CharacterGram
public import Theory.Character.AntiRealCoefficients
public import Theory.Character.Generalized
public import Theory.Character.IrreducibleDegrees

/-!
# Extracting the common constituent of the four virtual rows

The coefficient vectors are taken in the actual complete irreducible basis
of the ambient group. Generalized-character integrality and the proved Gram
calculation supply five distinct irreducibles. Orthogonality to the principal
character excludes it from each of the five positions.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion

/-- The signed common-constituent extraction for four actual generalized
characters. The numerical hypotheses concern the original functions. -/
theorem exists_common_irreducible_of_four_rows
    {G : Type*} [Group G] [Finite G]
    (β : Fin 4 → ClassFunction G)
    (hβ : ∀ i, IsGeneralizedCharacter (β i))
    (hdegree : ∀ i, β i 1 = -1)
    (hprod : ∀ i k, scalarProduct G (β i) (β k) = 1 + if i = k then 1 else 0)
    (hprincipal : ∀ i, scalarProduct G (β i) 1 = 0) :
    ∃ (ε : ℤ) (ψ : ClassFunction G) (μ : Fin 4 → ClassFunction G),
      (ε = 1 ∨ ε = -1) ∧ IsIrreducibleCharacter ψ ∧
      (∀ i, IsIrreducibleCharacter (μ i)) ∧ Function.Injective μ ∧
      (∀ i, ψ ≠ μ i) ∧ ψ ≠ 1 ∧ (∀ i, μ i ≠ 1) ∧
      ∀ i, β i = (ε : ℂ) • (ψ - μ i) := by
  classical
  obtain ⟨J, hJ, ξ, hξ, _b, _hb⟩ := irreducible_characters_form_basis (G := G)
  let : Fintype J := hJ
  let θ : J → ClassFunction G := fun j => ofConjClassFunction (ξ j)
  have hirr (j : J) : IsIrreducibleCharacter (θ j) := by
    obtain ⟨⟨n, ρ, he⟩, hn⟩ := hξ.1 j
    refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
    · rwa [he] at hn
    · change ofConjClassFunction (ξ j) = ρ.character
      rw [he, ofConjClassFunction_characterClassFunction]
  have hinj : Function.Injective θ := by
    intro j k hjk
    apply hξ.2.2
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    exact congrFun hjk g
  choose v hv using fun i j => (hβ i).scalarProduct_irreducible_int (hirr j)
  let Φ := fun i => toConjClassFunction (β i) (hβ i).isClassFunction
  have hinner (i : Fin 4) (j : J) :
      classFunctionInner (Φ i) (ξ j) = (v i j : ℂ) :=
    (classFunctionInner_toConjClassFunction_right (β i) (hβ i).isClassFunction (ξ j)).trans (hv i j)
  have hreverse (i : Fin 4) (j : J) :
      scalarProduct G (θ j) (β i) = (v i j : ℂ) := by
    rw [← scalarProduct_conj, hv, star_intCast]
  have hexpand (i : Fin 4) : (∑ j, (v i j : ℂ) • ξ j) = Φ i := by
    simpa only [hinner] using completeFamily_sum_inner_smul_eq hξ (Φ i)
  have heval (i : Fin 4) (g : G) : β i g = ∑ j, (v i j : ℂ) * θ j g := by
    simpa only [Φ, θ, ofConjClassFunction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      toConjClassFunction_apply] using (congrFun (hexpand i) (ConjClasses.mk g)).symm
  have hdot (i k : Fin 4) : ∑ j, v i j * v k j = 1 + if i = k then 1 else 0 := by
    have h := congrArg (fun f => classFunctionInner f (Φ k)) (hexpand i)
    rw [classFunctionInner_sum_left] at h
    simp only [smul_eq_mul] at h
    change ∑ j, (v i j : ℂ) * scalarProduct G (θ j) (β k) = scalarProduct G (β i) (β k) at h
    rw [hprod] at h
    simp only [hreverse] at h
    split_ifs at h ⊢ <;> exact_mod_cast h
  let d := fun j => (hirr j).degree
  have hd (j : J) : θ j 1 = (d j : ℂ) := (hirr j).degree_eq
  have hw (i : Fin 4) : ∑ j, v i j * (d j : ℤ) = -1 := by
    have h := heval i 1
    rw [hdegree] at h
    simp only [hd] at h
    exact_mod_cast h.symm
  obtain ⟨ε,a,b,hε,hbinj,hab,hvab⟩ := four_rows_common_constituent v d
    (fun j => (hirr j).degree_pos)
    (fun i => by simpa [pow_two] using hdot i i) hw
    (fun i k hik => by simpa only [if_neg hik, add_zero] using hdot i k)
  have hvA (i : Fin 4) : v i a = ε := by simp [hvab, hab i]
  have hvB (i : Fin 4) : v i (b i) = -ε := by simp [hvab, (hab i).symm]
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  refine ⟨ε, θ a, fun i => θ (b i), hε, hirr a, fun i => hirr (b i),
    hinj.comp hbinj, fun i he => hab i (hinj he), ?_, ?_, ?_⟩
  · intro he
    have h := hv 0 a
    rw [he, hprincipal, hvA] at h
    exact hε0 (by exact_mod_cast h.symm)
  · intro i he
    change θ (b i) = 1 at he
    have h := hv i (b i)
    rw [he, hprincipal, hvB] at h
    have hz : -ε = 0 := by exact_mod_cast h.symm
    exact hε0 (neg_eq_zero.mp hz)
  · intro i
    ext g
    rw [heval]
    simp only [hvab, Int.cast_mul, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero,
      mul_sub, sub_mul, Finset.sum_sub_distrib]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    ring

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion
