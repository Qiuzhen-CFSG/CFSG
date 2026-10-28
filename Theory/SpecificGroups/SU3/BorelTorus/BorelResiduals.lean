module

public import Theory.SpecificGroups.SU3.BorelTorus.Basic
public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.RootGeneration
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# Two-residuals of the full unitary Borel groups

The full diagonal torus has odd order over an even field. Its elements
therefore belong to the two-residual. A norm-one element with nontrivial
cubic action then generates the whole root group in that normal subgroup,
including its central layer. This proves the assertion for both actual
matrix homomorphisms, without replacing the full torus by its norm-one part.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954; the root action
and the norm-one element are those of Huppert II.10.12.
-/

public section
open Matrix Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
variable {E : Type*} [Field E]
variable (J : HermitianForm 3 E)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

/-- The full matrix torus, with its codomain restricted to the special Borel. -/
@[expose] def specialTorusIn : Eˣ →* specialBorel J hJ :=
  (hermitianTorusSU J hJ).codRestrict _
    (fun k => (show specialTorus J hJ ≤ specialBorel J hJ from le_sup_right) ⟨k, rfl⟩)

/-- The full projective matrix torus, with codomain restricted to its Borel. -/
@[expose] def projectiveTorusIn : Eˣ →* projectiveBorel J hJ :=
  (hermitianTorusPSU J hJ).codRestrict _
    (fun k => (show projectiveTorus J hJ ≤ projectiveBorel J hJ from le_sup_right) ⟨k, rfl⟩)

variable [Finite E] [CharP E 2]

include hJ in
private theorem root_torus_twoResidual {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (hq : 2 < q) (hodd : Odd (Nat.card E - 1))
    {G : Type*} [Group G]
    (r : hermitianUnipotentCoord J →* G) (t : Eˣ →* G)
    (hact : ∀ k z, t k * r z * (t k)⁻¹ = r (hermitianTorusAction J k z)) :
    pResidual 2 (r.range ⊔ t.range : Subgroup G) = ⊤ := by
  let B := r.range ⊔ t.range
  let f : hermitianUnipotentCoord J →* B :=
    r.codRestrict B (fun z => (show r.range ≤ B from le_sup_left) ⟨z, rfl⟩)
  let d : Eˣ →* B :=
    t.codRestrict B (fun k => (show t.range ≤ B from le_sup_right) ⟨k, rfl⟩)
  let N := pResidual 2 B
  have ht (k : Eˣ) : d k ∈ N := by
    apply mem_pResidual_of_orderOf_coprime
    have hc : Nat.Coprime 2 (Nat.card Eˣ) := by
      rw [Nat.card_units]
      exact hodd.coprime_two_left
    exact hc.of_dvd_right ((orderOf_map_dvd d k).trans (orderOf_dvd_natCard k))
  obtain ⟨k, _, hk3, _, hk⟩ :=
    exists_hermitian_norm_one_torus_cube_ne_one J q hcard hfixed hJ hq
  have hr : f.range ≤ N :=
    EvenInner.root_le_normal J hcard hfixed f N (d k) (ht k) k hk hk3
      (fun z => Subtype.ext (hact k z))
  have hroot : r.range ≤ N.map B.subtype := by
    rintro _ ⟨z, rfl⟩
    exact ⟨f z, hr ⟨z, rfl⟩, rfl⟩
  have htorus : t.range ≤ N.map B.subtype := by
    rintro _ ⟨k, rfl⟩
    exact ⟨d k, ht k, rfl⟩
  apply top_unique
  intro b _
  obtain ⟨c, hc, he⟩ := (sup_le hroot htorus) b.property
  exact (Subtype.ext he : c = b) ▸ hc

/-- The full special unitary Borel is its own two-residual when q > 2. -/
theorem specialBorel_twoResidual {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (hq : 2 < q) (hodd : Odd (Nat.card E - 1)) :
    pResidual 2 (specialBorel J hJ) = ⊤ := by
  apply root_torus_twoResidual J hJ hcard hfixed hq hodd
    (hermitianUnipotentSU J hJ) (hermitianTorusSU J hJ)
  intro k z
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  exact hermitianTorusGL_mul_unipotent J k z

/-- The full projective unitary Borel is its own two-residual when q > 2. -/
theorem projectiveBorel_twoResidual {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (hq : 2 < q) (hodd : Odd (Nat.card E - 1)) :
    pResidual 2 (projectiveBorel J hJ) = ⊤ :=
  root_torus_twoResidual J hJ hcard hfixed hq hodd
    (hermitianUnipotentPSU J hJ) (hermitianTorusPSU J hJ)
    (EvenInner.projective_torus_action J hJ)

end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
