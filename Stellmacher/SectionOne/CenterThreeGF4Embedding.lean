module

public import Stellmacher.SectionOne.Defs
public import Theory.Frattini.CoprimeAction
public import Theory.Representation.ElementaryAbelianAction
public import Theory.Representation.TwoDimensionalOddOrder
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Tactic

/-!
# The center-three `GF(4)` representation in Stellmacher (1.3)

This module constructs the field and special-linear representation used in the
center-fixed branch of Stellmacher's Lemma (1.3).  If the center of the normal
odd subgroup `F` has order three, is centralized by the given involution, and
acts without a fixed summand on the elementary abelian `2`-group `V`, a
generator of that center satisfies `T² + T + 1 = 0` on `V`.  Adjoining this
endomorphism equips `V` with compatible `GF(4)` scalars.  The faithful ambient
action is linear for these scalars.

The determinant vanishes on `[F, x] = F`, while the involution has determinant
of order dividing both two and the order-three unit group of `GF(4)`.  Since
`F` and the involution generate the ambient group, the representation lands in
`SL_n(4)`.  The hypotheses also force `F` to be noncommutative.  Dimensions
zero and one would make its faithful linear image commutative, and dimension
two is excluded by `Representation.theorem_2_6_a`; hence `n ≥ 3`.  The main
theorem deliberately exposes this dimension before any order-64 argument.  A
thin corollary specializes to `SL₃(4)` when `|V| = 2⁶`.

Source: `refs/latex/stellmacher-n-group.tex`, proof of Lemma (1.3), center-fixed
branch (journal p. 16, lines 337--351).  The dimension-first formulation avoids
using the later source conclusion `|V| ≤ 2⁶` circularly in constructing the
`GF(4)` module.
-/

open scoped IsMulCommutative Polynomial
open Polynomial

namespace Stellmacher.SectionOne

universe u v

private abbrev F2 := ZMod 2
private abbrev F4 := GaloisField 2 2

private theorem fixedPointSubgroup_eq_bot_of_commutatorAction_eq_top
    {A M : Type*} [Group A] [Finite A] [Group M] [Finite M]
    [MulDistribMulAction A M]
    (hsolv : Group.IsSolvable M)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card M))
    (hcommM : IsMulCommutative M)
    (hcomm : commutatorAction A M = ⊤) :
    FixedPoints.subgroup A M = ⊥ := by
  have hcompl :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := M) (A := A) hsolv hcop hcommM
  apply eq_bot_iff.mpr
  intro z hz
  have hzinf : z ∈ FixedPoints.subgroup A M ⊓ commutatorAction A M :=
    ⟨hz, by rw [hcomm]; exact Subgroup.mem_top z⟩
  exact hcompl.disjoint.le_bot hzinf

/-- A fixed-point-free central subgroup of order three makes the faithful
ambient action special-linear over `GF(4)`, in dimension at least three. -/
public theorem centerThree_fixed_action_to_specialLinear
    {G : Type u} {V : Type v} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (F : Subgroup G) (_hFnorm : F.Normal) (hFne : F ≠ ⊥)
    (p : ℕ) [Fact p.Prime] (_hFp : IsPGroup p F)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hgen : F ⊔ Subgroup.zpowers x = ⊤)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hcenterCard : Nat.card (Subgroup.center F) = 3)
    (hcenterComm :
      ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥)
    (hcommCenterV : commutatorAction (Subgroup.center F) V = ⊤)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    ∃ n : ℕ, 3 ≤ n ∧ Nat.card V = 4 ^ n ∧
      ∃ rho : G →* Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 2),
        Function.Injective rho := by
  let Z := Subgroup.center F
  let : IsCyclic Z := isCyclic_of_prime_card hcenterCard
  obtain ⟨z, hzgen⟩ := IsCyclic.exists_generator (α := Z)
  have hZfix : FixedPoints.subgroup Z V = ⊥ := by
    apply fixedPointSubgroup_eq_bot_of_commutatorAction_eq_top
    · infer_instance
    · obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
      rw [hcenterCard, hm]
      exact (by decide : Nat.Coprime 3 2).pow_right m
    · infer_instance
    · exact hcommCenterV
  have hzorder : orderOf z = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hzgen, hcenterCard]
  have hzpow : z ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by simp [hzorder])
  let rho2 : Representation F2 G (Additive V) :=
    Representation.ofElementaryAbelianAction (A := G) (G := V) (p := 2)
  let zG : G := ((z : Z) : F)
  let T : Module.End F2 (Additive V) := rho2 zG
  have hzMap : zG ∈ (Subgroup.center F).map F.subtype := by
    exact ⟨(z : F), z.property, rfl⟩
  have hzCentralX : zG ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcenterComm) hzMap
  have hzx : zG * x = x * zG :=
    (Subgroup.mem_centralizer_iff.mp hzCentralX x (Subgroup.mem_zpowers x)).symm
  have hFcentral : F ≤ Subgroup.centralizer ({zG} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    have hzcenter := Subgroup.mem_center_iff.mp z.property ⟨f, hf⟩
    exact congrArg Subtype.val hzcenter.symm
  have hxcentral : x ∈ Subgroup.centralizer ({zG} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact hzx
  have hGcentral : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({zG} : Set G) := by
    rw [← hgen]
    exact sup_le hFcentral (Subgroup.zpowers_le.mpr hxcentral)
  have hgcomm (g : G) : g * zG = zG * g := by
    exact (Subgroup.mem_centralizer_iff.mp
      (hGcentral (Subgroup.mem_top g)) zG (by simp)).symm
  have hTpow : T ^ 3 = 1 := by
    rw [← map_pow]
    apply LinearMap.ext
    intro w
    change Additive.ofMul ((((z ^ 3 : Z) : F) : G) • Additive.toMul w) = w
    rw [hzpow]
    simp
  have hTsub_inj :
      Function.Injective ((T - 1 : Module.End F2 (Additive V)) : Additive V → Additive V) := by
    apply (injective_iff_map_eq_zero
      (T - 1 : Module.End F2 (Additive V)).toAddMonoidHom).2
    intro w hw
    have hTw : T w = w := by
      change T w - w = 0 at hw
      exact sub_eq_zero.mp hw
    have hzw : zG • Additive.toMul w = Additive.toMul w := by
      apply Additive.ofMul.injective
      simpa [rho2, T] using hTw
    have hzfix : zG ∈ fixingSubgroup G ({Additive.toMul w} : Set V) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      exact hzw
    have hwfix : Additive.toMul w ∈ FixedPoints.subgroup Z V := by
      intro a
      obtain ⟨n, rfl⟩ := hzgen a
      change (zG ^ n) • Additive.toMul w = Additive.toMul w
      have hzpow := (fixingSubgroup G ({Additive.toMul w} : Set V)).zpow_mem hzfix n
      rw [mem_fixingSubgroup_iff] at hzpow
      exact hzpow _ (by simp)
    have : Additive.toMul w = 1 := by
      have := hZfix.le hwfix
      simpa using this
    exact Additive.toMul.injective (by simpa using this)
  have hfactor :
      (T - 1) * (T ^ 2 + T + 1) = (0 : Module.End F2 (Additive V)) := by
    calc
      (T - 1) * (T ^ 2 + T + 1) =
          T * (T ^ 2 + T + 1) - (T ^ 2 + T + 1) := by rw [sub_mul, one_mul]
      _ = (T ^ 3 + T ^ 2 + T) - (T ^ 2 + T + 1) := by
        rw [mul_add, mul_add, mul_one, ← pow_succ']
        norm_num [pow_two]
      _ = T ^ 3 - 1 := by abel
      _ = 0 := by rw [hTpow]; simp
  have hquad : T ^ 2 + T + 1 = (0 : Module.End F2 (Additive V)) := by
    apply LinearMap.ext
    intro w
    apply hTsub_inj
    have := LinearMap.congr_fun hfactor w
    simpa using this
  let q : F2[X] := X ^ 2 + X + 1
  have hqirr : Irreducible q := by
    dsimp [q]
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · have hdeg : ((X ^ 2 + X + 1) : F2[X]).natDegree = 2 := by
        simpa using Polynomial.natDegree_quadratic
          (R := F2) (a := 1) (b := 1) (c := 1) one_ne_zero
      simp [Finset.mem_Icc, hdeg]
    · intro a ha
      rw [Polynomial.IsRoot] at ha
      fin_cases a
      · change Polynomial.eval (0 : F2) (X ^ 2 + X + 1) = 0 at ha
        norm_num at ha
      · change Polynomial.eval (1 : F2) (X ^ 2 + X + 1) = 0 at ha
        have hthree : (3 : F2) = 1 := by decide
        norm_num at ha
        rw [hthree] at ha
        exact one_ne_zero ha
  let hqfact : Fact (Irreducible q) := ⟨hqirr⟩
  let : Fact (Irreducible q) := hqfact
  let K := AdjoinRoot q
  let E := Algebra.adjoin F2 ({T} : Set (Module.End F2 (Additive V)))
  let : IsMulCommutative E := Algebra.isMulCommutative_adjoin_singleton F2 T
  let eT : E := ⟨T, Algebra.subset_adjoin (by simp)⟩
  have hqeT : q.eval₂ (Algebra.ofId F2 E) eT = 0 := by
    apply Subtype.ext
    simpa [q, eT] using hquad
  let liftK : K →ₐ[F2] E :=
    AdjoinRoot.liftAlgHom q (Algebra.ofId F2 E) eT hqeT
  let scalarK : K →+* Module.End F2 (Additive V) :=
    E.val.toRingHom.comp liftK.toRingHom
  have hcardK : Nat.card K = 4 := by
    let : Fintype F2 := Fintype.ofFinite F2
    have hqne : q ≠ 0 := hqirr.ne_zero
    let bK := (AdjoinRoot.powerBasis hqne).basis
    let : Fintype K := Fintype.ofEquiv (Fin q.natDegree → F2) bK.equivFun.symm.toEquiv
    rw [Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := F2) (V := K)]
    rw [show Fintype.card F2 = 2 by simp]
    rw [(AdjoinRoot.powerBasis hqne).finrank]
    have hqdeg : q.natDegree = 2 := by
      dsimp [q]
      simpa using Polynomial.natDegree_quadratic
        (R := F2) (a := 1) (b := 1) (c := 1) one_ne_zero
    change 2 ^ q.natDegree = 4
    rw [hqdeg]
    norm_num
  let eK : K ≃ₐ[F2] F4 := GaloisField.algEquivGaloisField 2 2 hcardK
  let scalarF4 : F4 →+* Module.End F2 (Additive V) :=
    scalarK.comp eK.symm.toRingHom
  let : Module F4 (Additive V) := Module.compHom (Additive V) scalarF4
  have hrhoTcomm (g : G) : Commute (rho2 g) T := by
    rw [show T = rho2 zG by rfl]
    exact (map_mul rho2 g zG).symm.trans <|
      congrArg rho2 (hgcomm g) |>.trans (map_mul rho2 zG g)
  have hscalarComm (g : G) (a : F4) : Commute (rho2 g) (scalarF4 a) := by
    change Commute (rho2 g) ((liftK (eK.symm a) : E) : Module.End F2 (Additive V))
    apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute (R := F2) (s := {T})
    · exact (liftK (eK.symm a)).property
    · intro b hb
      simp only [Set.mem_singleton_iff] at hb
      subst b
      exact hrhoTcomm g
  let rho4fun : G → Module.End F4 (Additive V) := fun g =>
    { toFun := rho2 g
      map_add' := (rho2 g).map_add
      map_smul' := by
        intro a w
        change rho2 g (scalarF4 a w) = scalarF4 a (rho2 g w)
        exact LinearMap.congr_fun (hscalarComm g a).eq w }
  let rho4 : Representation F4 G (Additive V) :=
    { toFun := fun g => rho4fun g
      map_one' := by
        apply LinearMap.ext
        intro w
        simp [rho4fun, rho2]
      map_mul' := by
        intro g h
        apply LinearMap.ext
        intro w
        simp [rho4fun, rho2, Module.End.mul_apply] }
  have hrho4inj : Function.Injective rho4 := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [show rho4.ker = fixingSubgroup G (Set.univ : Set V) by
      ext g
      rw [MonoidHom.mem_ker, mem_fixingSubgroup_iff]
      constructor
      · intro hg w _
        have hw := congrArg (fun f : Module.End F4 (Additive V) => f (Additive.ofMul w)) hg
        exact Additive.ofMul.injective (by simpa [rho4, rho4fun, rho2] using hw)
      · intro hg
        apply LinearMap.ext
        intro w
        apply Additive.toMul.injective
        simpa [rho4, rho4fun, rho2] using hg (Additive.toMul w) (Set.mem_univ _)]
    exact hfaith
  let n := Module.finrank F4 (Additive V)
  have hcardF4 : Nat.card F4 = 4 := by
    simpa using GaloisField.card 2 2 (by decide)
  have hcardModule : Nat.card V = 4 ^ n := by
    let : Fintype F4 := Fintype.ofFinite F4
    let : Fintype V := Fintype.ofFinite V
    change Nat.card (Additive V) = 4 ^ n
    rw [Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := F4) (V := Additive V)]
    rw [show Fintype.card F4 = 4 by
      simpa [Nat.card_eq_fintype_card] using hcardF4]
  let b := Module.finBasis F4 (Additive V)
  let rhoGL : G →* LinearMap.GeneralLinearGroup F4 (Additive V) := rho4.asGroupHom
  have hrhoGLinj : Function.Injective rhoGL := by
    intro g h hgh
    apply hrho4inj
    change (rhoGL g : Module.End F4 (Additive V)) = rhoGL h
    exact congrArg Units.val hgh
  let matrixEquiv :
      Matrix.GeneralLinearGroup (Fin n) F4 ≃*
        LinearMap.GeneralLinearGroup F4 (Additive V) :=
    Matrix.GeneralLinearGroup.toLin' b
  let rhoMat : G →* Matrix.GeneralLinearGroup (Fin n) F4 :=
    matrixEquiv.symm.toMonoidHom.comp rhoGL
  have hrhoMatInj : Function.Injective rhoMat :=
    matrixEquiv.symm.injective.comp hrhoGLinj
  let detG : G →* F4ˣ := Matrix.GeneralLinearGroup.det.comp rhoMat
  have hcommKer : ⁅F, Subgroup.zpowers x⁆ ≤ detG.ker := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hFdet : F ≤ detG.ker := by
    rw [← hcommFx]
    exact hcommKer
  have hdetxPow : detG x ^ 2 = 1 := by
    rw [← map_pow, hx.2, map_one]
  have hdetx : detG x = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
    · exact orderOf_dvd_of_pow_eq_one hdetxPow
    · have hord := orderOf_dvd_natCard (detG x)
      rw [Nat.card_units, hcardF4] at hord
      simpa using hord
  have hxdet : x ∈ detG.ker := by
    simpa [MonoidHom.mem_ker] using hdetx
  have hdetAll : ∀ g : G, detG g = 1 := by
    intro g
    have htopKer : (⊤ : Subgroup G) ≤ detG.ker := by
      rw [← hgen]
      exact sup_le hFdet (Subgroup.zpowers_le.mpr hxdet)
    exact htopKer (Subgroup.mem_top g)
  let rhoSL : G →* Matrix.SpecialLinearGroup (Fin n) F4 :=
    { toFun := fun g =>
        ⟨(rhoMat g : Matrix (Fin n) (Fin n) F4), by
          have hg := congrArg Units.val (hdetAll g)
          simpa [detG] using hg⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro g h
        apply Subtype.ext
        change (rhoMat (g * h) : Matrix (Fin n) (Fin n) F4) =
          (rhoMat g : Matrix (Fin n) (Fin n) F4) * rhoMat h
        simp }
  have hrhoSLinj : Function.Injective rhoSL := by
    intro g h hgh
    apply hrhoMatInj
    apply Units.ext
    exact congrArg Subtype.val hgh
  have hFnoncomm : ¬ IsMulCommutative F := by
    intro hFcomm
    have hcenterTop : Subgroup.center F = ⊤ :=
      Subgroup.center_eq_top_iff.mpr hFcomm
    have hmapTop : (⊤ : Subgroup F).map F.subtype = F := by
      rw [← MonoidHom.range_eq_map]
      exact F.range_subtype
    have hcommBot : ⁅F, Subgroup.zpowers x⁆ = ⊥ := by
      simpa [hcenterTop, hmapTop] using hcenterComm
    apply hFne
    calc
      F = ⁅F, Subgroup.zpowers x⁆ := hcommFx.symm
      _ = ⊥ := hcommBot
  have hnLower : 3 ≤ n := by
    by_contra hnnot
    have hnle : n ≤ 2 := by omega
    have hnCases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    let rhoF : Representation F4 F (Additive V) := rho4.comp F.subtype
    have hrhoFinj : Function.Injective rhoF :=
      hrho4inj.comp Subtype.val_injective
    rcases hnCases with hn0 | hn1 | hn2
    · have hVsub : Subsingleton (Additive V) :=
        Module.finrank_zero_iff.mp (show Module.finrank F4 (Additive V) = 0 from hn0)
      let : Subsingleton (Module.End F4 (Additive V)) := by infer_instance
      let : Subsingleton F := hrhoFinj.subsingleton
      exact hFnoncomm (by infer_instance)
    · apply hFnoncomm
      rw [isMulCommutative_iff]
      intro a b
      apply hrhoFinj
      rw [map_mul, map_mul]
      obtain ⟨ca, hca, -⟩ :=
        LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hn1 (rhoF a)
      obtain ⟨cb, hcb, -⟩ :=
        LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hn1 (rhoF b)
      rw [hca, hcb]
      apply LinearMap.ext
      intro w
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
      rw [smul_smul, smul_smul, mul_comm cb ca]
    · have hfiniteDim : FiniteDimensional F4 (Additive V) := by infer_instance
      have hFodd' : Odd (Nat.card F) := Nat.coprime_two_left.mp hFodd
      have hchar : ¬ ringChar F4 ∣ Nat.card F := by
        rw [ringChar.eq F4 2]
        exact (Nat.prime_two.coprime_iff_not_dvd.mp hFodd)
      apply hFnoncomm
      exact @Representation.theorem_2_6_a F4 inferInstance F inferInstance hFodd'
        (Additive V) inferInstance inferInstance hfiniteDim hn2 rhoF hrhoFinj hchar
  exact ⟨n, hnLower, hcardModule, rhoSL, hrhoSLinj⟩

/-- The dimension-first representation specializes to `SL₃(4)` when
the elementary abelian module has order `2⁶`. -/
public theorem centerThree_fixed_action_to_slThreeFour
    {G : Type u} {V : Type v} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (F : Subgroup G) (hFnorm : F.Normal) (hFne : F ≠ ⊥)
    (p : ℕ) [Fact p.Prime] (hFp : IsPGroup p F)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hgen : F ⊔ Subgroup.zpowers x = ⊤)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hcenterCard : Nat.card (Subgroup.center F) = 3)
    (hcenterComm :
      ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥)
    (hcommCenterV : commutatorAction (Subgroup.center F) V = ⊤)
    (hcardV : Nat.card V = 2 ^ 6)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    ∃ rho : G →* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2),
      Function.Injective rho := by
  obtain ⟨n, -, hcardModule, rho, hrho⟩ :=
    centerThree_fixed_action_to_specialLinear F hFnorm hFne p hFp hFodd x hx
      hgen hcommFx hcenterCard hcenterComm hcommCenterV hfaith
  have hpow : 4 ^ n = 4 ^ 3 := by
    calc
      4 ^ n = Nat.card V := hcardModule.symm
      _ = 2 ^ 6 := hcardV
      _ = 4 ^ 3 := by norm_num
  have hn : n = 3 := Nat.pow_right_injective (by norm_num : 1 < 4) hpow
  subst n
  exact ⟨rho, hrho⟩

end Stellmacher.SectionOne
