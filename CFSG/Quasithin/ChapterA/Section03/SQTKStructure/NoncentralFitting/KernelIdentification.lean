module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.QuotientConsequences
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.GroupTheory.PGroup.SupercriticalAutomorphisms
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.CyclicNormalCentralizer
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Nilpotence

/-!
# Identifying the noncentral Fitting action kernel

For each noncentral odd core Oₚ(L), choose an actual supercritical subgroup X.
Supercritical automorphism detection and perfectness make its action nontrivial;
the SQT bound and cyclic-normal centralization give rank two. A.1.29 then
constructs a surjection onto SL₂(r), with r prime and greater than three.

Cover rigidity identifies these kernels. The action of the common kernel on
each active Oₚ(L) lies in the p-group kernel of Aut(Oₚ(L)) → Aut(X/Φ(X)).
Thus its p-residual centralizes that core. Inactive cores are central already,
so A.1.4 proves the kernel nilpotent. The odd Fitting subgroup maps trivially
to SL₂(r), giving equality with the kernel and the required actual quotient.
The final consumer deduces F(L) = O(L) and quasisimplicity of L/F(L).

Only `PrimeSL2CoverRigidity` remains explicit, as authorized by the source
assembly boundary. No common-kernel, nilpotence, or classification premise
is assumed. All actions use the literal subgroup inclusions and Frattini quotients.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Proposition A.3.6, printed pp.43–44; A.1.4, A.1.21, and A.1.29(1).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.RankActions
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.KernelIdentification
universe u
variable {A : Type u} [Group A] [Finite A]

omit [Finite A] in
private theorem perfect_hom_eq_one_of_pgroup_range
    [Group.IsPerfect A] {B : Type*} [Group B] [Finite B] {p : ℕ} [Fact p.Prime]
    (a : A →* B) (hp : IsPGroup p a.range) : a = 1 := by
  let : Group.IsNilpotent a.range := hp.isNilpotent
  let : Group.IsPerfect a.range := Group.IsPerfect.range a
  have hs : Subsingleton a.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent a.range inferInstance
  ext x
  exact congrArg Subtype.val (Subsingleton.elim (a.rangeRestrict x) 1)

omit [Finite A] in
private theorem restriction_frattini_fixed
    (S : Subgroup A) [S.Characteristic] (X : Subgroup S) [X.Characteristic]
    (g : A)
    (hg : (⟨g, mem_top g⟩ : (⊤ : Subgroup A)) ∈
      frattiniCentralizer (X.map S.subtype) ⊤) :
    quotientAut (frattini X) (MulAut.characteristic X (MulAut.conjNormal g)) = 1 := by
  let P := X.map S.subtype
  let e : X ≃* P := X.equivMapOfInjective S.subtype S.subtype_injective
  have he (x : X) : MulAut.conjNormal g (e x) =
      e (MulAut.characteristic X (MulAut.conjNormal g) x) := by
    apply Subtype.ext
    rfl
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini X) q
  rw [quotientAut_apply_mk, MulAut.one_apply]
  have hx := (mem_frattiniCentralizer_iff P ⊤ ⟨g, mem_top g⟩).mp hg (e x)
  rw [he] at hx
  have hm := (frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective)
    (QuotientGroup.eq.mp hx)
  apply QuotientGroup.eq.mpr
  simpa only [mem_comap, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    map_mul, map_inv, MulEquiv.symm_apply_apply] using hm

private theorem core_action_pgroup_of_frattini_fixed
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (S : Subgroup A) [S.Characteristic] (hS : IsPGroup p S)
    (X : Subgroup S) (hX : IsSupercriticalPSubgroup p X)
    (N : Subgroup A)
    (hf : letI : X.Characteristic := hX.characteristic
      ∀ n : N, (⟨(n : A), mem_top _⟩ : (⊤ : Subgroup A)) ∈
        frattiniCentralizer (X.map S.subtype) ⊤) :
    IsPGroup p ((MulAut.conjNormal : A →* MulAut S).comp N.subtype).range := by
  let : X.Characteristic := hX.characteristic
  apply (hX.isPGroup_frattini_action_kernel hS hp).to_le
  rintro _ ⟨n, rfl⟩
  exact restriction_frattini_fixed S X n (hf n)

private theorem noncentral_supercritical
    [Group.IsPerfect A] {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (S : Subgroup A) [S.Characteristic] (hS : IsPGroup p S)
    (X : Subgroup S) (hX : IsSupercriticalPSubgroup p X)
    (hn : ¬ S ≤ center A) : ¬ X.map S.subtype ≤ center A := by
  let : X.Characteristic := hX.characteristic
  intro hc
  have hf (g : (⊤ : Subgroup A)) : g ∈ frattiniCentralizer (X.map S.subtype) ⊤ := by
    apply (mem_frattiniCentralizer_iff _ _ g).mpr
    intro x
    congr 1
    apply Subtype.ext
    change (g : A) * (x : A) * (g : A)⁻¹ = x
    rw [mem_center_iff.mp (hc x.property) g, mul_inv_cancel_right]
  have hpg := core_action_pgroup_of_frattini_fixed hp S hS X hX ⊤ hf
  have ht := perfect_hom_eq_one_of_pgroup_range
    ((MulAut.conjNormal : A →* MulAut S).comp (⊤ : Subgroup A).subtype) hpg
  apply hn
  intro x hx
  apply mem_center_iff.mpr
  intro g
  have he := congrArg (fun a : MulAut S => (a ⟨x,hx⟩ : A))
    (DFunLike.congr_fun ht (⟨g, mem_top g⟩ : (⊤ : Subgroup A)))
  change g * x * g⁻¹ = x at he
  exact mul_inv_eq_iff_eq_mul.mp he

private theorem supercritical_rank_two
    [Group.IsPerfect A] {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (S : Subgroup A) [S.Characteristic] (hS : IsPGroup p S)
    (X : Subgroup S) (hX : IsSupercriticalPSubgroup p X)
    (hr : primeRank p A ≤ 2) (hn : ¬ S ≤ center A) :
    primeRank p (X.map S.subtype) = 2 := by
  let : X.Characteristic := hX.characteristic
  let P := X.map S.subtype
  have hP : IsPGroup p P := (hS.to_subgroup X).map S.subtype
  have hle : primeRank p P ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective p P.subtype P.subtype_injective).trans hr
  have hgt : 1 < primeRank p P := by
    by_contra! hh
    let : IsCyclic P := hP.isCyclic_of_odd_of_elementary_card_le hp
      (fun E hE => by
        let : IsElementaryAbelian p E := hE
        exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hh E)
    have hc : (⊤ : Subgroup A) ≤ centralizer (P : Set A) := by
      simpa only [Group.IsPerfect.commutator_eq_top] using
        commutator_le_centralizer_of_isCyclic_normal P
    apply noncentral_supercritical hp S hS X hX hn
    intro x hx
    apply mem_center_iff.mpr
    intro g
    exact (hc (mem_top g) x hx).symm
  exact le_antisymm hle hgt

private theorem residual_centralizes_core_of_frattini_fixed
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (X : Subgroup (pCore p A)) (hX : IsSupercriticalPSubgroup p X)
    (N : Subgroup A) [N.Normal]
    (hf : letI : X.Characteristic := hX.characteristic
      ∀ n : N, (⟨(n : A), mem_top _⟩ : (⊤ : Subgroup A)) ∈
        frattiniCentralizer (X.map (pCore p A).subtype) ⊤) :
    pResidual p N ≤ centralizer (pCore p N : Set N) := by
  let a : N →* MulAut (pCore p A) :=
    (MulAut.conjNormal : A →* MulAut (pCore p A)).comp N.subtype
  have ha : IsPGroup p a.range :=
    core_action_pgroup_of_frattini_fixed hp _ pCore_isPGroup X hX N hf
  have hres : pResidual p N ≤ a.ker :=
    sInf_le ⟨inferInstance, ha.of_equiv (QuotientGroup.quotientKerEquivRange a).symm⟩
  intro n hn
  rw [mem_centralizer_iff]
  intro y hy
  have hy' : (y : A) ∈ pCore p A := by
    rw [pCore_subnormal_eq_comap p (inferInstance : N.Normal).isSubnormal] at hy
    exact hy
  have he := congrArg (fun f : MulAut (pCore p A) => (f ⟨y, hy'⟩ : A))
    (MonoidHom.mem_ker.mp (hres hn))
  change (n : A) * (y : A) * (n : A)⁻¹ = y at he
  apply Subtype.ext
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- An active odd core produces a prime-field SL₂ quotient whose kernel's
p-residual centralizes its p-core. The kernel is the actual supercritical
Frattini-action kernel, transported from the top subgroup to the group. -/
theorem exists_core_action_model
    [Group.IsPerfect A] (hA : CFSG.Quasithin.IsStronglyQuasithin A)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hn : ¬ pCore p A ≤ center A) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧
      ∃ f : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r),
        Function.Surjective f ∧
        pResidual p f.ker ≤ centralizer (pCore p f.ker : Set f.ker) := by
  have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨k, hk⟩ := hp; omega
  obtain ⟨X, hX⟩ := (pCore_isPGroup (p := p) (G := A)).exists_supercriticalPSubgroup hp2
  let : X.Characteristic := hX.characteristic
  let P := X.map (pCore p A).subtype
  let e : X ≃* P := X.equivMapOfInjective _ (pCore p A).subtype_injective
  have hP : IsPGroup p P := (pCore_isPGroup.to_subgroup X).map (pCore p A).subtype
  have ho : omega₁ P (p := p) = ⊤ := by
    apply top_unique
    intro y _
    apply Subgroup.subset_closure
    change y ^ (p ^ 1) = 1
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [pow_one, ← map_pow, map_one] using congrArg e (hX.pow_eq_one x)
  have hc : _root_.commutator P ≤ center P := by
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    apply mem_center_iff.mpr
    intro z
    apply e.symm.injective
    have hh := mem_center_iff.mp (hX.derived_le_center
      (commutator_mem_commutator (mem_top (e.symm x)) (mem_top (e.symm y)))) (e.symm z)
    simpa only [map_mul, map_commutatorElement] using hh
  have hr : primeRank p P = 2 :=
    supercritical_rank_two hp _ pCore_isPGroup X hX (hA p Fact.out hp) hn
  have hnon : ⁅P, (⊤ : Subgroup A)⁆ ≠ ⊥ := by
    intro hh
    exact noncentral_supercritical hp _ pCore_isPGroup X hX hn
      (commutator_top_right_eq_bot_iff_le_center.mp hh)
  have hp3 := three_lt_of_perfect_action P ⊤ hp2 hP ho hc hr hnon
  have hm := CFSG.Quasithin.ChapterA.lemma_A_1_29_1 P ⊤ hp hP ho hc hr hnon
  have step {r : ℕ}
      (j : ((⊤ : Subgroup A) ⧸ frattiniCentralizer P ⊤) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :
      ∃ f : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r),
        Function.Surjective f ∧
        pResidual p f.ker ≤ centralizer (pCore p f.ker : Set f.ker) := by
    let q : A →* (⊤ : Subgroup A) := topEquiv.symm.toMonoidHom
    let f := j.toMonoidHom.comp ((QuotientGroup.mk' (frattiniCentralizer P ⊤)).comp q)
    refine ⟨f, j.surjective.comp ((QuotientGroup.mk'_surjective _).comp topEquiv.symm.surjective), ?_⟩
    apply residual_centralizes_core_of_frattini_fixed hp X hX f.ker
    intro n
    apply (QuotientGroup.eq_one_iff _).mp
    apply j.injective
    rw [map_one]
    change f n = 1
    exact MonoidHom.mem_ker.mp n.property
  rcases hm with hj | ⟨_, hj⟩
  · exact ⟨p, Fact.out, hp3, step hj.some⟩
  · exact ⟨5, by decide, by decide, step hj.some⟩

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.KernelIdentification

namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
open KernelIdentification
universe u
variable {G : Type u} [Group G] [Finite G] {L : Subgroup G}

/-- The odd Fitting subgroup is killed by every surjection onto SL₂(r), r > 3. -/
theorem fitting_le_SL2_kernel (hL : L.IsCComponent) (hO : pCore 2 G = ⊥)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r)
    (f : L →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r))
    (hf : Function.Surjective f) : fittingSubgroup L ≤ f.ker := by
  apply (fitting_le_oddCore hL hO).trans
  have hi : (pPrimeCore 2 L).map f ≤ pPrimeCore 2 (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :=
    le_sSup ⟨Normal.map inferInstance f hf,
      (pPrimeCore_coprime_card (p := 2) (G := L)).of_dvd_right (card_map_dvd _ f)⟩
  have htwo : (2 : ZMod r) ≠ 0 := by
    intro he
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < r)
      ((ZMod.natCast_eq_zero_iff 2 r).mp he)
  rw [Matrix.SpecialLinearGroup.pPrimeCore_two_eq_bot htwo] at hi
  exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hi)

/-- Every prime core of L lies in an SL₂ action kernel, and its intrinsic
prime core maps back to exactly that core of L. -/
theorem pCore_SL2_kernel_map (hL : L.IsCComponent) (hO : pCore 2 G = ⊥)
    {r p : ℕ} [Fact r.Prime] [Fact p.Prime] (hr : 3 < r)
    (f : L →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r))
    (hf : Function.Surjective f) : (pCore p f.ker).map f.ker.subtype = pCore p L := by
  rw [pCore_subnormal_eq_comap p (inferInstance : f.ker.Normal).isSubnormal,
    map_comap_eq, Subgroup.subtype_range]
  exact inf_eq_right.mpr ((pCore_le_fitting L p).trans (fitting_le_SL2_kernel hL hO hr f hf))

/-- Common-kernel comparison and supercritical detection discharge the
residual-centralization hypothesis of A.1.4 for each prime. -/
theorem SL2_kernel_nilpotent (hrigid : PrimeSL2CoverRigidity.{u})
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) {r : ℕ} [Fact r.Prime] (hr : 3 < r)
    (f : L →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r))
    (hf : Function.Surjective f) : Group.IsNilpotent f.ker := by
  let : Group.IsPerfect L := hL.perfect
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by simpa only [Nat.card_zmod] using hr) (MulEquiv.refl _)
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod r) ⧸ center _) :=
    IsQuasisimple.simple
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :=
    (QuotientGroup.mk'_surjective (center _)).nontrivial
  have hsolv := solvable_kernel_of_cComponent hL f hf
  apply (CFSG.Quasithin.ChapterA.lemma_A_1_4 hsolv ?_).2.2
  intro p hp _
  let : Fact p.Prime := ⟨hp⟩
  by_cases hc : pCore p L ≤ center L
  · intro x _
    rw [mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hy' : (y : L) ∈ pCore p L := by
      rw [← pCore_SL2_kernel_map hL hO hr f hf (p := p)]
      exact mem_map_of_mem f.ker.subtype hy
    exact (mem_center_iff.mp (hc hy') x).symm
  · have ho : Odd p := hp.odd_of_ne_two (by
      intro he
      apply hc
      rw [he, twoCore_eq_bot hL hO]
      exact bot_le)
    obtain ⟨s, hs, hs3, g, hg, hres⟩ :=
      exists_core_action_model (hG.subgroup L).stronglyQuasithin ho hc
    let : Fact s.Prime := ⟨hs⟩
    have he := cComponent_SL2_kernels_eq hrigid hL hr hs3 f g hf hg
    rw [he]
    exact hres

/-- The common supercritical-action kernel is precisely F(L). -/
theorem SL2_kernel_eq_fitting (hrigid : PrimeSL2CoverRigidity.{u})
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) {r : ℕ} [Fact r.Prime] (hr : 3 < r)
    (f : L →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r))
    (hf : Function.Surjective f) : f.ker = fittingSubgroup L := by
  exact le_antisymm (le_sSup ⟨inferInstance, SL2_kernel_nilpotent hrigid hG hO hL hr f hf⟩)
    (fitting_le_SL2_kernel hL hO hr f hf)

/-- The source's noncentral branch constructs an actual prime-field SL₂
Fitting quotient. Only the specified universal cover rigidity input remains. -/
theorem primeSL2FittingQuotient_of_noncentral (hrigid : PrimeSL2CoverRigidity.{u})
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hn : ¬ fittingSubgroup L ≤ center L) :
    PrimeSL2FittingQuotient L := by
  let : Group.IsPerfect L := hL.perfect
  obtain ⟨p, hp, ho, hnc⟩ := exists_noncentral_odd_core hL hO hn
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr, hr3, f, hf, _⟩ :=
    exists_core_action_model (hG.subgroup L).stronglyQuasithin ho hnc
  let : Fact r.Prime := ⟨hr⟩
  have hk := SL2_kernel_eq_fitting hrigid hG hO hL hr3 f hf
  exact ⟨r, hr, hr3, ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩⟩

/-- Consumer of the constructed witness: the noncentral Fitting subgroup
is the odd core and its quotient is quasisimple. -/
theorem noncentral_fitting_quotient_consequences (hrigid : PrimeSL2CoverRigidity.{u})
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hn : ¬ fittingSubgroup L ≤ center L) :
    fittingSubgroup L = pPrimeCore 2 L ∧ IsQuasisimple (L ⧸ fittingSubgroup L) := by
  have h := primeSL2FittingQuotient_of_noncentral hrigid hG hO hL hn
  exact ⟨fitting_eq_oddCore hL hO h, fitting_quotient_quasisimple h⟩

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
