module
public import Theory.SpecificGroups.SU3.BinaryPRegularClasses

/-!
# Odd-order class bound for the small unitary actor

The full SU₃(2) actor has at most four odd-order conjugacy classes.
Equal traces yield linear conjugacy. Adjoint correction makes the conjugator
unitary; normal centralizer witnesses then correct its determinant.
The reducible spectral argument is adapted from
`SU3/BinaryPRegularClasses/CentralizerDeterminant/ReducibleNormal`, whose
public assembly starts at field degree two. Here the scalar case uses the
literal middle coordinate of the antidiagonal form, and the remaining
argument includes degree one without perfectness.

This supplies the class bound for the small natural-section realization
in Fong--Seitz I (4D), (6A)(c), and II (8C), pp.203--204.
-/

public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource.SmallClasses
open _root_.Module.End Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.SU3.BinaryPRegularClasses
open Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant
set_option linter.unnecessarySimpa false
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private theorem eigenspace_complement (f : Module.End F V) (hf : f.IsSemisimple) (μ : F) :
    IsCompl (f.eigenspace μ) (LinearMap.range (f - μ • 1)) := by
  have hdisj : Disjoint (f.eigenspace μ) (LinearMap.range (f - μ • 1)) := by
    rw [Submodule.disjoint_def]
    intro x hx hy
    obtain ⟨y, rfl⟩ := hy
    have hy2 : y ∈ f.genEigenspace μ (2 : ℕ∞) := by
      rw [show (2 : ℕ∞) = (2 : ℕ) by rfl, mem_genEigenspace_nat]
      change ((f - μ • 1) ^ 2 : Module.End F V) y = 0
      rw [pow_two, Module.End.mul_apply]
      change f ((f - μ • 1) y) - μ • (f - μ • 1) y = 0
      exact sub_eq_zero.mpr (mem_eigenspace_iff.mp hx)
    rw [hf.isFinitelySemisimple.genEigenspace_eq_eigenspace μ (by norm_num)] at hy2
    change f y - μ • y = 0
    exact sub_eq_zero.mpr (mem_eigenspace_iff.mp hy2)
  apply (Submodule.isCompl_iff_disjoint _ _ ?_).mpr hdisj
  rw [eigenspace_def, add_comm, LinearMap.finrank_range_add_finrank_ker]

private theorem scaling_commutes (U W : Submodule F V) (hcomp : IsCompl U W)
    (t : F) : ∃ c : Module.End F V,
      LinearMap.det c = t ^ Module.finrank F U ∧
      ∀ b : Module.End F V, U ∈ b.invtSubmodule → W ∈ b.invtSubmodule → Commute c b := by
  let e := U.prodEquivOfIsCompl W hcomp
  let a : Module.End F (U × W) := (t • LinearMap.id).prodMap LinearMap.id
  let c : Module.End F V := e.toLinearMap.comp (a.comp e.symm.toLinearMap)
  refine ⟨c, ?_, ?_⟩
  · have hconj : LinearMap.det c = LinearMap.det a := by
      simpa [c, LinearMap.comp_assoc] using LinearMap.det_conj a e
    rw [hconj, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id]
    simp
  · intro b hU hW
    let brU : Module.End F U := b.restrict hU
    let brW : Module.End F W := b.restrict hW
    let bp := brU.prodMap brW
    have heq : b.comp e.toLinearMap = e.toLinearMap.comp bp := by
      apply LinearMap.ext
      intro z
      rcases z with ⟨x, y⟩
      change b ((x : V) + (y : V)) = (brU x : V) + (brW y : V)
      rw [map_add]
      rfl
    have hacomm : a.comp bp = bp.comp a := by
      apply LinearMap.ext
      intro z
      rcases z with ⟨x, y⟩
      change (t • brU x, brW y) = (brU (t • x), brW y)
      simp
    change c.comp b = b.comp c
    ext v
    have heq' := congrArg e.symm (LinearMap.congr_fun heq (e.symm v))
    have heq'' : e.symm (b v) = bp (e.symm v) := by simpa using heq'
    simp only [c, LinearMap.comp_apply]
    calc
      e (a (e.symm (b v))) = e (a (bp (e.symm v))) := by rw [heq'']
      _ = e (bp (a (e.symm v))) := congrArg e (LinearMap.congr_fun hacomm _)
      _ = b (e (a (e.symm v))) := (LinearMap.congr_fun heq _).symm
      _ = b (c v) := rfl

private theorem eigen_scaling (f : Module.End F V) (hf : f.IsSemisimple) (μ t : F) :
    ∃ c : Module.End F V,
      LinearMap.det c = t ^ Module.finrank F (f.eigenspace μ) ∧
      ∀ b : Module.End F V, Commute b f → Commute c b := by
  obtain ⟨c, hdet, hc⟩ := scaling_commutes (f.eigenspace μ)
    (LinearMap.range (f - μ • 1)) (eigenspace_complement f hf μ) t
  refine ⟨c, hdet, fun b hb => hc b ?_ ?_⟩
  · rw [mem_invtSubmodule]
    intro x hx
    change b x ∈ f.eigenspace μ
    rw [mem_eigenspace_iff] at hx ⊢
    rw [← Module.End.mul_apply, ← hb.eq, Module.End.mul_apply, hx, map_smul]
  · rw [mem_invtSubmodule]
    rintro _ ⟨x, rfl⟩
    refine ⟨b x, ?_⟩
    have hb' : Commute b (f - μ • 1) :=
      hb.sub_right ((Commute.one_right b).smul_right μ)
    exact (LinearMap.congr_fun hb'.eq x).symm

private theorem nonscalar_spectral [Finite F] [CharP F 2] (f : Module.End F (Fin 3 → F))
    (hf : f.IsSemisimple) (hscalar : ∀ μ : F, f ≠ μ • 1)
    (hred : ¬ Irreducible f.charpoly) (d : F) :
    ∃ c : Module.End F (Fin 3 → F), LinearMap.det c = d ∧
      ∀ b : Module.End F (Fin 3 → F), Commute b f → Commute c b := by
  have hroot : ∃ μ : F, f.HasEigenvalue μ := by
    by_contra h
    push Not at h
    apply hred
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · simp [LinearMap.charpoly_natDegree]
    · intro μ hμ
      exact h μ ((hasEigenvalue_iff_isRoot_charpoly f μ).mpr hμ)
  obtain ⟨μ, hμ⟩ := hroot
  have hpos : 0 < Module.finrank F (f.eigenspace μ) := by
    exact Nat.pos_of_ne_zero (fun hz => hμ (Submodule.finrank_eq_zero.mp hz))
  have hlt : Module.finrank F (f.eigenspace μ) < 3 := by
    have htop : f.eigenspace μ ≠ ⊤ := by
      intro ht
      apply hscalar μ
      apply LinearMap.ext
      intro x
      exact mem_eigenspace_iff.mp (ht ▸ Submodule.mem_top)
    simpa using Submodule.finrank_lt htop
  have hdim : Module.finrank F (f.eigenspace μ) = 1 ∨
      Module.finrank F (f.eigenspace μ) = 2 := by omega
  rcases hdim with hn | hn
  · obtain ⟨c, hc, hb⟩ := eigen_scaling f hf μ d
    exact ⟨c, by simpa [hn] using hc, hb⟩
  · obtain ⟨t, ht⟩ := Finite.surjective_of_injective (frobenius_inj F 2) d
    obtain ⟨c, hc, hb⟩ := eigen_scaling f hf μ t
    rw [hn] at hc
    exact ⟨c, hc.trans (by simpa [frobenius_def] using ht), hb⟩

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant

private theorem normal_nonscalar [Finite F] [CharP F 2] (J : HermitianForm 3 F) (g : J.unitarySubgroup)
    (hf : Module.End.IsSemisimple (Matrix.toLin' g.val.val))
    (hscalar : ∀ μ : F, g.val.val ≠ μ • 1)
    (hred : ¬ Irreducible g.val.val.charpoly) (d : Fˣ) :
    ∃ A : GL (Fin 3) F, Commute A g.val ∧ Commute A (adjoint J A) ∧
      GeneralLinearGroup.det A = d := by
  classical
  let f := Matrix.toLin' g.val.val
  have hns : ∀ μ : F, f ≠ μ • 1 := by
    intro μ he
    apply hscalar μ
    have hh := congrArg LinearMap.toMatrix' he
    simpa [f] using hh
  have hredf : ¬ Irreducible f.charpoly := by
    simpa [f, Matrix.charpoly_toLin'] using hred
  obtain ⟨c, hc, hcb⟩ := nonscalar_spectral f hf hns hredf (d : F)
  have hdet : (LinearMap.toMatrix' c).det = (d : F) := by
    rw [← LinearMap.det_toLin', Matrix.toLin'_toMatrix', hc]
  let A : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero (LinearMap.toMatrix' c)
    (hdet ▸ d.ne_zero)
  have hcomm (B : GL (Fin 3) F) (hB : Commute B g.val) : Commute A B := by
    have hb : Commute (Matrix.toLin' B.val) f := by
      change (Matrix.toLin' B.val).comp (Matrix.toLin' g.val.val) =
        (Matrix.toLin' g.val.val).comp (Matrix.toLin' B.val)
      have hh := congrArg Matrix.toLin' (congrArg Units.val hB.eq)
      simpa only [Units.val_mul, Matrix.toLin'_mul] using hh
    apply Units.ext
    change LinearMap.toMatrix' c * B.val = B.val * LinearMap.toMatrix' c
    have hh := congrArg LinearMap.toMatrix' (hcb _ hb).eq
    simpa only [Module.End.mul_eq_comp, LinearMap.toMatrix'_comp,
      LinearMap.toMatrix'_toLin'] using hh
  have hAg := hcomm g.val (Commute.refl _)
  exact ⟨A, hAg, hcomm (adjoint J A) (commute_adjoint J g A hAg), Units.ext hdet⟩


private theorem scalar_witness (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (g : GL (Fin 3) F) (μ : F) (hg : g.val = μ • 1)
    (d : Fˣ) (hd : J.conj (d : F) * (d : F) = 1) :
    ∃ A : GL (Fin 3) F, Commute A g ∧ Commute A (adjoint J A) ∧
      GeneralLinearGroup.det A = d := by
  classical
  let D : Matrix (Fin 3) (Fin 3) F := diagonal ![1,(d : F),1]
  have hdet : D.det = (d : F) := by simp [D,det_diagonal,Fin.prod_univ_three]
  let A : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero D (hdet ▸ d.ne_zero)
  have hA : A ∈ J.unitarySubgroup := by
    rw [J.mem_unitarySubgroup_iff]
    change J.conjTranspose D * J.form * D = J.form
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D,HermitianForm.conjTranspose,Matrix.mul_apply,Fin.sum_univ_three,hd]
  refine ⟨A,?_,?_,Units.ext hdet⟩
  · apply Units.ext
    change A.val * g.val = g.val * A.val
    rw [hg]
    simp
  · rw [(mem_unitary_iff_adjoint J A).mp hA]
    exact (Commute.refl A).inv_right

private theorem small_centralizer_det [Finite F] [CharP F 2]
    (J : HermitianForm 3 F) (hcard : Nat.card F = (2^1)^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (g : J.specialSubgroup) (hg : ¬ 2 ∣ orderOf g)
    (d : Fˣ) (hd : J.conj (d : F) * (d : F) = 1) :
    ∃ C : J.unitarySubgroup, Commute C.val g.val ∧ GeneralLinearGroup.det C.val = d := by
  classical
  have hn : ∃ A : GL (Fin 3) F, Commute A g.val ∧ Commute A (adjoint J A) ∧
      GeneralLinearGroup.det A = d := by
    by_cases hirr : Irreducible g.val.val.charpoly
    · exact exists_normal_centralizer_det_of_irreducible J g hirr d
    by_cases hscalar : ∃ μ : F, g.val.val = μ • 1
    · obtain ⟨μ,hμ⟩ := hscalar
      exact scalar_witness J hJ g.val μ hμ d hd
    · push Not at hscalar
      exact normal_nonscalar J ⟨g.val,J.specialSubgroup_le_unitarySubgroup g.property⟩
        (isSemisimple_of_pRegular J g hg) hscalar hirr d
  obtain ⟨A,hAg,hAn,hAd⟩ := hn
  exact exists_unitary_commuting_det_of_normal J
    ⟨g.val,J.specialSubgroup_le_unitarySubgroup g.property⟩ 1 (by decide)
    hcard d hd A hAg hAn hAd

private theorem small_trace_one [Finite F] [CharP F 2]
    (J : HermitianForm 3 F) (hcard : Nat.card F = (2^1)^2)
    (hpow : ∀ x : F, J.conj x = x^(2^1)) :
    ∃ t : F, J.conj t + t = 1 := by
  classical
  let := Fintype.ofFinite F
  have hex : ∃ x : F, J.conj x ≠ x := by
    by_contra! hall
    have he : (Polynomial.X : Polynomial F)^2 = Polynomial.X := by
      apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ Function.injective_id
      · intro x
        simpa only [id_eq,Polynomial.eval_pow,Polynomial.eval_X,pow_one] using
          (hpow x).symm.trans (hall x)
      · rw [Polynomial.natDegree_X_pow,Polynomial.natDegree_X,
          ←Nat.card_eq_fintype_card,hcard]
        decide
    have hd := congrArg Polynomial.natDegree he
    simp only [Polynomial.natDegree_X_pow,Polynomial.natDegree_X] at hd
    omega
  obtain ⟨x,hx⟩ := hex
  have hd : J.conj x + x ≠ 0 := by
    intro hh
    apply hx
    have he := congrArg (fun z : F => z + x) hh
    simpa only [add_assoc,CharTwo.add_self_eq_zero,add_zero,zero_add] using he
  refine ⟨x / (J.conj x + x),?_⟩
  rw [map_div₀,map_add,J.conj_involutive,add_comm x (J.conj x),←add_div,div_self hd]

/-- The small full SU₃ actor, with its scalar center retained, has at most
four odd-order classes. This is the exact bound used by the small catalogue. -/
theorem card_pRegularConjClasses_le [Finite F] [CharP F 2]
    (J : HermitianForm 3 F) (hcard : Nat.card F = (2^1)^2)
    (hconj : ∀ x, J.conj x = x^(2^1))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    Nat.card (ConjClasses.mk '' {g : J.specialSubgroup | ¬ 2 ∣ orderOf g}) ≤ Nat.card F := by
  obtain ⟨t,ht⟩ := small_trace_one J hcard hconj
  apply card_pRegularConjClasses_le_of_unitary_corrections J
  · intro g h _ _ D hD
    exact UnitaryIntertwiner.correction_of_trace_one J t ht
      ⟨g.val,J.specialSubgroup_le_unitarySubgroup g.property⟩
      ⟨h.val,J.specialSubgroup_le_unitarySubgroup h.property⟩ D hD
  · exact small_centralizer_det J hcard hJ

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource.SmallClasses
