module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.Construction.StandardEmbedding.Relations

/-!
# Descent of projective unitary generator calculations to the Ree group

Assume the explicit unitary rank-one presentation and a realization of its
generators in the split F4 matrix group. Fixedness on generators implies
fixedness on every word. The defining relations make evaluation descend to
the actual projective unitary matrix image. Reduction to the two Bruhat
forms, together with identity separation in the Ree matrices, proves the
descended map injective. An actual change-of-form equivalence then gives
an embedding from the prescribed identity-Gram `StandardPGU`.

`standardProjectiveEmbeddings_of_generator_calculations` is conditional.
Neither `UnitaryPresentation` nor `ReeRealizations` is proved here; both
remain prerequisites of `standardProjectiveEmbeddings`. In particular,
the full diagonal torus, its fixedness and its relations still have to be
realized in the Ree root matrices.

Source: Malle, *The maximal subgroups of ²F₄(q²)*, Section 2.5, manuscript
pp.10–11, J. Algebra 139 (1991), 52–69, DOI 10.1016/0021-8693(91)90283-E.
Only the existence of the projective unitary subgroup is addressed by
this reduction; no normalizer or conjugacy hypothesis is used.
-/

public noncomputable section

namespace ReeF4.MaximalSubgroups.SimpleNormal.Construction

namespace StandardEmbedding

/-- The checked defining relations kill their entire normal closure. -/
theorem relations_le_ree_ker {m : ℕ} (d : ReeGeneratorData m) (hr : d.Relations) :
    relationSubgroup m ≤ d.eval.ker :=
  Subgroup.normalClosure_le_normal (fun w hw => MonoidHom.mem_ker.mpr (hr w hw))

theorem ree_eval_fixed {m : ℕ} (d : ReeGeneratorData m) (hf : d.Fixed) (w : Word m) :
    reeTwist m (d.eval w) = d.eval w := by
  have he : (reeTwist m).comp d.eval = d.eval := by
    apply FreeGroup.ext_hom
    intro g
    change reeTwist m (FreeGroup.lift d.generator (FreeGroup.of g)) =
      FreeGroup.lift d.generator (FreeGroup.of g)
    simpa only [FreeGroup.lift_apply_of] using hf g
  exact DFunLike.congr_fun he w

/-- Evaluation in the actual Ree fixed subgroup. -/
def reeWordHom {m : ℕ} (d : ReeGeneratorData m) (hf : d.Fixed) : Word m →* Model m :=
  d.eval.codRestrict (fixedSubgroup m)
    (fun w => (mem_fixedSubgroup m _).mpr (ree_eval_fixed d hf w))

theorem unitary_normal_eq_one_of_ree {m : ℕ} (d : ReeGeneratorData m) (hs : d.Separated)
    (n : NormalForm m) (h : d.eval (normalWord n) = 1) :
    unitaryEval m (normalWord n) = 1 := by
  cases n with
  | small p t =>
    have hd : d.rootImage p * d.torusImage t = 1 := by
      simpa only [normalWord, map_mul, rootWord, torusWord, ReeGeneratorData.eval,
        FreeGroup.lift_apply_of, ReeGeneratorData.generator] using h
    obtain ⟨ha, hb, ht⟩ := hs.1 p t hd
    have hp : p = RootParameter.zero m := by
      cases p
      simp_all [RootParameter.zero]
    subst p
    subst t
    simp only [normalWord, map_mul, rootWord, torusWord, unitaryEval,
      FreeGroup.lift_apply_of, unitaryGenerator, root_zero, torus_one, mul_one]
  | big p t q =>
    apply False.elim
    apply hs.2 p t q
    simpa only [normalWord, map_mul, rootWord, torusWord, weylWord, ReeGeneratorData.eval,
      FreeGroup.lift_apply_of, ReeGeneratorData.generator] using h

theorem ree_ker_le_unitary_ker {m : ℕ} (d : ReeGeneratorData m) (hr : d.Relations)
    (hs : d.Separated) (hk : (unitaryEval m).ker = relationSubgroup m)
    (hn : ∀ w : Word m, ∃ n : NormalForm m, w * (normalWord n)⁻¹ ∈ relationSubgroup m) :
    d.eval.ker ≤ (unitaryEval m).ker := by
  intro w hw
  have hw1 : d.eval w = 1 := hw
  obtain ⟨n, hn⟩ := hn w
  have hd : d.eval (w * (normalWord n)⁻¹) = 1 := relations_le_ree_ker d hr hn
  have hdn : d.eval (normalWord n) = 1 := by
    simpa only [map_mul, map_inv, hw1, one_mul, inv_eq_one] using hd
  have hu : unitaryEval m (normalWord n) = 1 := unitary_normal_eq_one_of_ree d hs n hdn
  have hd' : unitaryEval m (w * (normalWord n)⁻¹) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hk]
    exact hn
  simpa only [MonoidHom.mem_ker, map_mul, map_inv, hu, inv_one, mul_one] using hd'

theorem unitary_ker_le_reeWordHom_ker {m : ℕ} (d : ReeGeneratorData m)
    (hf : d.Fixed) (hr : d.Relations) (hk : (unitaryEval m).ker = relationSubgroup m) :
    (unitaryEval m).ker ≤ (reeWordHom d hf).ker := by
  intro w hw
  apply Subtype.ext
  exact relations_le_ree_ker d hr (hk ▸ hw)

/-- Descent through the actual full projective unitary matrix image. -/
def descendedHom {m : ℕ} (d : ReeGeneratorData m) (hf : d.Fixed) (hr : d.Relations)
    (hu : Function.Surjective (unitaryEval m))
    (hk : (unitaryEval m).ker = relationSubgroup m) : WittPGU m →* Model m :=
  (unitaryEval m).liftOfSurjective hu
    ⟨reeWordHom d hf, unitary_ker_le_reeWordHom_ker d hf hr hk⟩

theorem descendedHom_word {m : ℕ} (d : ReeGeneratorData m) (hf : d.Fixed) (hr : d.Relations)
    (hu : Function.Surjective (unitaryEval m))
    (hk : (unitaryEval m).ker = relationSubgroup m) (w : Word m) :
    descendedHom d hf hr hu hk (unitaryEval m w) = reeWordHom d hf w := by
  unfold descendedHom
  rw [MonoidHom.liftOfRightInverse_comp_apply]

theorem descendedHom_injective {m : ℕ} (d : ReeGeneratorData m)
    (hf : d.Fixed) (hr : d.Relations) (hs : d.Separated)
    (hu : Function.Surjective (unitaryEval m))
    (hk : (unitaryEval m).ker = relationSubgroup m)
    (hn : ∀ w : Word m, ∃ n : NormalForm m, w * (normalWord n)⁻¹ ∈ relationSubgroup m) :
    Function.Injective (descendedHom d hf hr hu hk) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := hu x
  obtain ⟨b, rfl⟩ := hu y
  rw [descendedHom_word, descendedHom_word] at hxy
  have he : d.eval a = d.eval b := congrArg Subtype.val hxy
  have hd : a * b⁻¹ ∈ d.eval.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  have he' := ree_ker_le_unitary_ker d hr hs hk hn hd
  simpa only [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] using he'

end StandardEmbedding

open StandardEmbedding

/-- Conditional assembly. Both independent generator calculations must be
discharged before this establishes the unconditional standard embedding. -/
theorem standardProjectiveEmbeddings_of_generator_calculations
    (hu : UnitaryPresentation) (hr : ReeRealizations) : StandardProjectiveEmbeddings := by
  intro m hm
  obtain ⟨hsurj, hker, hnormal⟩ := hu m hm
  obtain ⟨d, hfixed, hrelations, hseparated⟩ := hr m hm
  let j := descendedHom d hfixed hrelations hsurj hker
  refine ⟨j.comp (wittProjectiveEquiv m).symm.toMonoidHom, ?_⟩
  exact (descendedHom_injective d hfixed hrelations hseparated hsurj hker hnormal).comp
    (wittProjectiveEquiv m).symm.injective

end ReeF4.MaximalSubgroups.SimpleNormal.Construction
