module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Residual
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Source
public import CFSG.Quasithin.ChapterA.Section03.RankThreeSylow
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.SpecificGroups.SU3.ProjectiveInvolution

/-!
# Projective unitary involution residuals

Every involution centralizer in the actual PSU₃(q), for an odd prime q > 3,
has solvable residual isomorphic to SL₂(q). An involution lifts through the
central scalar kernel of exponent three. Its centralizer maps onto the
projective centralizer, and the kernel meets the perfect SL₂ residual trivially
because the center of SL₂ has order two.

The form comparison retains the matrix-field order q² and the stored
q-Frobenius conjugation. We also transport the single involution class and
the cyclic Sylow center from the special unitary model. These are intrinsic
model calculations; they do not position the source's cyclic factors.

Source: Aschbacher–Smith, A.3.21(a)–(b), printed p.55, and the canonical
choice in the proof of 1.3.4, printed pp.510–511.
-/

public section
open Subgroup
open CFSG.Quasithin.ChapterA.Section03
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
variable {G H : Type*} [Group G] [Group H]

private theorem cube_eq_self_of_sq_eq_one {x : G} (hx : x ^ 2 = 1) : x ^ 3 = x := by
  rw [pow_succ, hx, one_mul]

private theorem involution_lift (f : G →* H) (hf : Function.Surjective f)
    (hc : ∀ x ∈ f.ker, x ^ 3 = 1) (y : H) (hy : orderOf y = 2) :
    ∃ z : G, orderOf z = 2 ∧ f z = y := by
  obtain ⟨x, rfl⟩ := hf y
  have hy2 : (f x) ^ 2 = 1 := hy ▸ pow_orderOf_eq_one (f x)
  have hx6 := hc (x ^ 2) (by simpa only [MonoidHom.mem_ker, map_pow] using hy2)
  have hx3 : (x ^ 3) ^ 2 = 1 := by simpa only [← pow_mul] using hx6
  refine ⟨x ^ 3, orderOf_eq_prime hx3 ?_, ?_⟩
  · intro he
    have : f x = 1 := by
      simpa only [map_pow, cube_eq_self_of_sq_eq_one hy2, map_one] using congrArg f he
    simp [this] at hy
  · exact (map_pow f x 3).trans (cube_eq_self_of_sq_eq_one hy2)

private theorem centralizer_comap (f : G →* H)
    (hZ : f.ker ≤ center G) (hc : ∀ x ∈ f.ker, x ^ 3 = 1)
    (z : G) (hz : z ^ 2 = 1) :
    (centralizer ({f z} : Set H)).comap f = centralizer ({z} : Set G) := by
  ext x
  change f x ∈ centralizer ({f z} : Set H) ↔ x ∈ centralizer ({z} : Set G)
  simp only [mem_centralizer_singleton_iff]
  constructor
  · intro hx
    let c := x * z * x⁻¹ * z⁻¹
    have hk : c ∈ f.ker := by
      change f (x * z * x⁻¹ * z⁻¹) = 1
      simp only [map_mul, map_inv]
      rw [hx]
      group
    have hcz : Commute c z := (mem_center_iff.mp (hZ hk) z).symm
    have hc3 : c ^ 3 = 1 := hc c hk
    have hcx : c * z = x * z * x⁻¹ := by simp [c]
    have hconj2 : (x * z * x⁻¹) ^ 2 = 1 := by
      change (MulAut.conj x z) ^ 2 = 1
      rw [← map_pow, hz, map_one]
    have he : x * z * x⁻¹ = z := by
      calc
        x * z * x⁻¹ = (x * z * x⁻¹) ^ 3 := (cube_eq_self_of_sq_eq_one hconj2).symm
        _ = (c * z) ^ 3 := by rw [hcx]
        _ = z := by rw [hcz.mul_pow, hc3, one_mul, cube_eq_self_of_sq_eq_one hz]
    exact (mul_inv_eq_iff_eq_mul).mp he
  · intro hx
    simpa only [map_mul] using congrArg f hx

private def centralizerHom (f : G →* H) (z : G) :
    centralizer ({z} : Set G) →* centralizer ({f z} : Set H) :=
  (f.comp (centralizer ({z} : Set G)).subtype).codRestrict _ (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, MonoidHom.comp_apply, Subgroup.coe_subtype] using
      congrArg f (mem_centralizer_singleton_iff.mp x.property))

private theorem centralizerHom_surjective (f : G →* H) (hf : Function.Surjective f)
    (hZ : f.ker ≤ center G) (hc : ∀ x ∈ f.ker, x ^ 3 = 1)
    (z : G) (hz : z ^ 2 = 1) : Function.Surjective (centralizerHom f z) := by
  intro y
  obtain ⟨x, hx⟩ := hf y
  have hxc : x ∈ centralizer ({z} : Set G) := by
    rw [← centralizer_comap f hZ hc z hz]
    change f x ∈ centralizer ({f z} : Set H)
    rw [hx]
    exact y.property
  exact ⟨⟨x, hxc⟩, Subtype.ext hx⟩

private theorem residualHom_injective (q : ℕ) [Fact q.Prime] (hq : Odd q)
    (f : G →* H) (hZ : f.ker ≤ center G) (hc : ∀ x ∈ f.ker, x ^ 3 = 1)
    (z : G)
    (e : solvableResidual (centralizer ({z} : Set G)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) :
    Function.Injective ((centralizerHom f z).comp
      (solvableResidual (centralizer ({z} : Set G))).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hxk : (x.val : G) ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  have hxZ : e x ∈ center (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    apply congrArg e
    apply Subtype.ext
    apply Subtype.ext
    exact mem_center_iff.mp (hZ hxk) y.val.val
  have hcenter : Nat.card (center (Matrix.SpecialLinearGroup (Fin 2) (ZMod q))) = 2 := by
    simpa only [GorensteinWalter.sl2ProjectiveProjection_ker] using
      GorensteinWalter.sl2ProjectiveProjection_ker_card (ZMod q) (by
        simpa only [Nat.card_eq_fintype_card, ZMod.card] using hq)
  have hx2 : (e x) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨e x, hxZ⟩ : center _))
    rw [hcenter] at hh
    exact congrArg Subtype.val hh
  have hx3 : (e x) ^ 3 = 1 := by
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (Subtype.ext (hc _ hxk))
    rw [this, map_one]
  rw [pow_succ, hx2, one_mul] at hx3
  exact mem_bot.mpr (e.injective (hx3.trans (map_one e).symm))

private noncomputable def residualEquiv [Finite G] (e : G ≃* H) :
    solvableResidual G ≃* solvableResidual H :=
  (e.subgroupMap (solvableResidual G)).trans
    (MulEquiv.subgroupCongr (map_solvableResidual_eq e.toMonoidHom e.surjective))

private theorem projective_residual_of_cover [Finite G]
    (q : ℕ) [Fact q.Prime] (hq : Odd q)
    (f : G →* H) (hf : Function.Surjective f)
    (hZ : f.ker ≤ center G) (hc : ∀ x ∈ f.ker, x ^ 3 = 1)
    (hr : ∀ z : G, orderOf z = 2 → Nonempty
      (solvableResidual (centralizer ({z} : Set G)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod q)))
    (y : H) (hy : orderOf y = 2) :
    Nonempty (solvableResidual (centralizer ({y} : Set H)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) := by
  obtain ⟨z, hz, rfl⟩ := involution_lift f hf hc y hy
  obtain ⟨e⟩ := hr z hz
  let g := centralizerHom f z
  have hg : Function.Surjective g :=
    centralizerHom_surjective f hf hZ hc z (hz ▸ pow_orderOf_eq_one z)
  let R := solvableResidual (centralizer ({z} : Set G))
  let er : R ≃* R.map g := MulEquiv.ofBijective (g.subgroupMap R)
    ⟨fun x y h => residualHom_injective q hq f hZ hc z e
      (congrArg Subtype.val h), g.subgroupMap_surjective R⟩
  let es := er.trans (MulEquiv.subgroupCongr (map_solvableResidual_eq g hg))
  exact ⟨es.symm.trans e⟩

private noncomputable def centralizerEquiv (e : G ≃* H) (x : G) :
    centralizer ({x} : Set G) ≃* centralizer ({e x} : Set H) where
  toFun y := ⟨e y, mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp y.property))⟩
  invFun y := ⟨e.symm y, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp y.property)⟩
  left_inv y := Subtype.ext (e.symm_apply_apply y)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' y z := Subtype.ext (e.map_mul y z)

/-- Normalize the actual Hermitian form and coefficient field to the standard SU₃ model. -/
theorem specialUnitary_equiv_rankThreeSU
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (q : ℕ) [Fact q.Prime] (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) : Nonempty (J.specialSubgroup ≃* RankThreeSU q) := by
  let _ := Fintype.ofFinite F
  let _ : CharP F q := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  have hs : ∀ x, (ABG.unitaryForm 3 q 1 (by decide)).conj x = x ^ q := by
    intro x
    simp only [ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]
  exact J.nonempty_specialEquiv_of_card (ABG.unitaryForm 3 q 1 (by decide)) q
    hcard (J.card_fixed_of_prime_frobenius hconj)
    (GaloisField.card q (2 * 1) (by decide))
    ((ABG.unitaryForm 3 q 1 (by decide)).card_fixed_of_prime_frobenius hs)

/-- The residual in the actual projective matrix image is SL₂ over the fixed prime field. -/
theorem projectiveUnitary_involution_solvableResidual
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (q : ℕ) [Fact q.Prime] (hq : Odd q) (hlarge : 3 < q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (z : ProjectiveSpecialUnitaryMatrixGroup J) (hz : orderOf z = 2) :
    Nonempty (solvableResidual (centralizer ({z} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) := by
  obtain ⟨e⟩ := specialUnitary_equiv_rankThreeSU J q hcard hconj
  apply projective_residual_of_cover q hq J.specialToProjective
    J.specialToProjective_surjective J.specialToProjective_ker_le_center
    (fun x hx => congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x, hx⟩)) _ z hz
  intro w hw
  exact ⟨(residualEquiv (centralizerEquiv e w)).trans
    (su3_involution_solvableResidual_equiv q hq hlarge (e w) ((e.orderOf_eq w).trans hw))⟩

/-- Transport the projective residual calculation through the supplied PSU₃ isomorphism. -/
theorem isPSU_involution_solvableResidual
    [Finite G] (q : ℕ) [Fact q.Prime] (hq : Odd q) (hlarge : 3 < q)
    (hmodel : ClassicalGroup.IsPSU G 3 q) (z : G) (hz : orderOf z = 2) :
    Nonempty (solvableResidual (centralizer ({z} : Set G)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  obtain ⟨er⟩ := projectiveUnitary_involution_solvableResidual J q hq hlarge hcard hconj
    (e z) ((e.orderOf_eq z).trans hz)
  exact ⟨(residualEquiv (centralizerEquiv e z)).trans er⟩

/-- All involutions in the projective unitary matrix image are conjugate. -/
theorem projectiveUnitary_involutions_isConj
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (q : ℕ) [Fact q.Prime] (hq : Odd q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (z w : ProjectiveSpecialUnitaryMatrixGroup J) (hz : orderOf z = 2) (hw : orderOf w = 2) :
    IsConj z w := by
  obtain ⟨e⟩ := specialUnitary_equiv_rankThreeSU J q hcard hconj
  have hc : ∀ x ∈ J.specialToProjective.ker, x ^ 3 = 1 :=
    fun x hx => congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x, hx⟩)
  obtain ⟨a, ha, rfl⟩ := involution_lift J.specialToProjective J.specialToProjective_surjective hc z hz
  obtain ⟨b, hb, rfl⟩ := involution_lift J.specialToProjective J.specialToProjective_surjective hc w hw
  apply J.specialToProjective.map_isConj
  have h := e.symm.toMonoidHom.map_isConj
    (su3_involutions_isConj q hq (e a) (e b) ((e.orderOf_eq a).trans ha) ((e.orderOf_eq b).trans hb))
  simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using h

/-- Every actual PSU₃ model has one conjugacy class of involutions. -/
theorem isPSU_involutions_isConj
    (q : ℕ) [Fact q.Prime] (hq : Odd q) (hmodel : ClassicalGroup.IsPSU G 3 q)
    (z w : G) (hz : orderOf z = 2) (hw : orderOf w = 2) : IsConj z w := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  have h := e.symm.toMonoidHom.map_isConj
    (projectiveUnitary_involutions_isConj J q hq hcard hconj
      (e z) (e w) ((e.orderOf_eq z).trans hz) ((e.orderOf_eq w).trans hw))
  simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using h

/-- Each involution centralizer in PSU₃ has odd index. -/
theorem isPSU_involutionCentralizer_odd_index [Finite G]
    (q : ℕ) [Fact q.Prime] (hq : Odd q) (hmodel : ClassicalGroup.IsPSU G 3 q)
    (z : G) (hz : orderOf z = 2) : Odd (centralizer ({z} : Set G)).index :=
  odd_index_centralizer_of_one_involution_class z hz
    (fun w hw => isPSU_involutions_isConj q hq hmodel w z hw hz)

/-- The odd scalar kernel preserves the actual Sylow two-subgroup isomorphism type. -/
theorem projectiveUnitary_sylow_equiv
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (q : ℕ) [Fact q.Prime] (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ P : Sylow 2 (RankThreeSU q), Nonempty (T ≃* P) := by
  obtain ⟨e⟩ := specialUnitary_equiv_rankThreeSU J q hcard hconj
  obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective J.specialToProjective_surjective 2 T
  let P := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hi := injective_comp_subtype_of_coprime_ker J.specialToProjective
    (Nat.coprime_two_left.mpr J.odd_card_specialToProjective_ker) (Q : Subgroup J.specialSubgroup)
    Q.isPGroup'
  let ep : Q ≃* Q.mapSurjective J.specialToProjective_surjective :=
    MulEquiv.ofBijective (J.specialToProjective.subgroupMap (Q : Subgroup J.specialSubgroup))
      ⟨fun x y h => hi (congrArg Subtype.val h),
        J.specialToProjective.subgroupMap_surjective (Q : Subgroup J.specialSubgroup)⟩
  exact ⟨P, ⟨ep.symm.trans (e.subgroupMap (Q : Subgroup J.specialSubgroup))⟩⟩

/-- The center of each Sylow two-subgroup of an actual PSU₃ model is cyclic. -/
theorem isPSU_sylow_center_cyclic [Finite G]
    (q : ℕ) [Fact q.Prime] (hq : Odd q) (hmodel : ClassicalGroup.IsPSU G 3 q)
    (T : Sylow 2 G) : IsCyclic (center T) := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  obtain ⟨P, ⟨ep⟩⟩ := projectiveUnitary_sylow_equiv J q hcard hconj
    (T.mapSurjective (f := e.toMonoidHom) e.surjective)
  let et : T ≃* P := (e.subgroupMap (T : Subgroup G)).trans ep
  let _ := su3_sylow_center_cyclic q hq P
  exact isCyclic_of_injective (centerCongr et).toMonoidHom (centerCongr et).injective

/-- An actual PSU₃ model in odd characteristic has even order. -/
theorem isPSU_two_dvd_card (q : ℕ) [Fact q.Prime] (hq : Odd q)
    (hmodel : ClassicalGroup.IsPSU G 3 q) : 2 ∣ Nat.card G := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  rw [Nat.card_congr e.toEquiv]
  exact Matrix.SU3.two_dvd_projective_card_of_prime_frobenius J q Fact.out hq hcard hconj


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
