module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryCartan
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison

/-!
# The full Cartan has no fixed points on nonbinary unitary roots

A prime dividing q-1 cannot divide the order of an involution centralizer
in PSU3(q): the actual involution geometry embeds that centralizer in the
root group extended by the norm-one torus. Cauchy's theorem then makes an
actor of that prime order fixed-point-free on every invariant two-subgroup.
The two-point torus of the marked root actor contains such an element.
Its fixed-point statement transports to every Weyl root using N-normality
of the full source Cartan.

For SU3 the actual scalar projection preserves this prime-order element.
At even field degree that projection is injective; at odd degree its cubic
kernel is coprime to q-1. The projection is also injective on the actual
root two-subgroup. Thus both full and projective actors give the same
fixed-point conclusion, in every nonbinary degree and either orientation.
No quotient actor or central kernel is silently replaced.

The model centralizer proof extends the prime-three calculation in
SU3/BinarySylowFixerCentralizer, using its same root and basis conventions.
Source: Huppert II.10.12; Fong--Seitz I (5I), pp.31--35, and the Cartan
centralizer method in (6C), pp.39--40. AffineUnitaryExclusion consumes the
fixed-point result on the actual marked hexagon. The degree-one unitary
case has no nontrivial q-1 torus and is not claimed here.
-/

public noncomputable section
open Subgroup Matrix BenderSuzuki.External
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFixed
open BenderSuzuki.MatrixGroups BenderSuzuki.MatrixGroups.HermitianForm
open BorelTorus BorelTorus.EvenCenterAction OddPrimeSylow.NormalizedOuter.Coverage
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
private theorem root_normalizer_eq_borel {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card F = q^2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    normalizer (projectiveRoot J hJ : Set _) = projectiveBorel J hJ := by
  obtain ⟨_,rho,p,_,_,_,hr,_⟩ := huppert_II_10_12 J q hcard hfixed hJ
  obtain ⟨R,T,hRU,_,hn,_,hRT,_,hRc,_,_,_,hreg,⟨coord,hcoord⟩,hT,hTall⟩ := hr
  have hcoord_eq (w : hermitianUnipotentCoord J) :
      (coord w).val = hermitianUnipotentPSU J hJ w := by
    obtain ⟨M,hM,he⟩ := hcoord w
    have hh : M = hermitianUnipotentGL J w := Units.ext hM
    apply Subtype.ext
    simpa only [hh,hermitianUnipotentPSU_val] using he
  have heR : R = projectiveRoot J hJ := by
    apply le_antisymm
    · intro r hr
      obtain ⟨w,hw⟩ := coord.surjective ⟨r,hr⟩
      exact ⟨w,(hcoord_eq w).symm.trans (congrArg Subtype.val hw)⟩
    · rintro _ ⟨w,rfl⟩
      rw [←hcoord_eq w]
      exact (coord w).property
  have heT : T = projectiveTorus J hJ := by
    apply le_antisymm
    · intro t ht
      obtain ⟨k,M,hM,he⟩ := hT ⟨t,ht⟩
      refine ⟨k,?_⟩
      apply Subtype.ext
      have hh : M = hermitianTorusGL J k := Units.ext hM
      simpa only [hh,hermitianTorusPSU_val] using he.symm
    · rintro _ ⟨k,rfl⟩
      obtain ⟨t,M,hM,he⟩ := hTall k
      have hh : (t : ProjectiveSpecialUnitaryMatrixGroup J) = hermitianTorusPSU J hJ k := by
        apply Subtype.ext
        have hM' : M = hermitianTorusGL J k := Units.ext hM
        simpa only [hM',hermitianTorusPSU_val] using he
      exact hh ▸ t.property
  have hne : R ≠ ⊥ := by
    intro hb
    rw [hb,card_bot] at hRc
    have := one_lt_pow₀ hq (by decide : (3 : ℕ) ≠ 0)
    omega
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (BinaryInvolutionTable.IsotropicPoint J) :=
    MulAction.compHom _ rho
  have heN := BenderSuzuki.normalizer_eq_stabilizer_of_regular_compl
    R p (fun _ hx => hRU hx) hne hreg hn
  rw [←heR,projectiveBorel,←heR,←heT,hRT]
  exact heN

variable [CharP F 2]

omit [CharP F 2] in
private theorem root_torus_normalizes {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card F = q^2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    projectiveTorus J hJ ≤ normalizer (projectiveRoot J hJ : Set _) := by
  rw [root_normalizer_eq_borel J hJ hq hcard hfixed]
  exact le_sup_right

private theorem central_borel_le_rootTorus {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card F = q^2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q)
    (r : ProjectiveSpecialUnitaryMatrixGroup J)
    (hr : r ∈ centralImage J hJ) (hne : r ≠ 1) :
    projectiveBorel J hJ ⊓ centralizer ({r} : Set _) ≤ EvenInner.rootTorus J hJ := by
  rw [NormalizedRootCentralizers.uniform_centralImage J hJ r hr hne]
  rintro g ⟨hg,hc⟩
  have hgprod : g ∈ (projectiveRoot J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) *
      (projectiveTorus J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ (root_torus_normalizes J hJ hq hcard hfixed)]
    exact hg
  obtain ⟨u,hu,_,⟨k,rfl⟩,rfl⟩ := hgprod
  have hk : hermitianTorusPSU J hJ k ∈ centralizer (centralImage J hJ : Set _) := by
    let C : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
      centralizer (centralImage J hJ : Set _)
    have hh : u⁻¹ * (u * hermitianTorusPSU J hJ k) ∈ C :=
      C.mul_mem (C.inv_mem (root_centralizes J hJ hu)) hc
    simpa only [inv_mul_cancel_left] using hh
  have hnorm := (torus_centralizer_iff J hJ k).mp hk
  have hnormval := congrArg (fun x : (fixedField J)ˣ => ((x : fixedField J) : F)) hnorm
  change ((k : F) * J.conj (k : F))⁻¹ = 1 at hnormval
  have hkone : k ∈ EvenInner.normOne J := by
    change J.conj (k : F) = (k : F)⁻¹
    exact (eq_inv_of_mul_eq_one_right (inv_eq_one.mp hnormval))
  exact (EvenInner.rootTorus J hJ).mul_mem
    ((show EvenInner.rootImage J hJ ≤ EvenInner.rootTorus J hJ from le_sup_left) hu)
    ((show EvenInner.normOneImage J hJ ≤ EvenInner.rootTorus J hJ from le_sup_right) ⟨⟨k,hkone⟩,rfl⟩)


private theorem prime_separation {n r : ℕ} (hn : 0 < n)
    (hr : r.Prime) (hd : r ∣ 2^n-1) : ¬ r ∣ 2 ∧ ¬ r ∣ 2^n+1 := by
  have hq : 1 ≤ 2^n := Nat.one_le_pow _ _ (by decide)
  have hr2 : ¬ r ∣ 2 := by
    intro h
    have he : r = 2 := (Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hr.ne_one
    subst r
    have ht : 2 ∣ 2^n := dvd_pow_self _ (by omega : n ≠ 0)
    have ho := Nat.dvd_sub ht hd
    rw [Nat.sub_sub_self hq] at ho
    norm_num at ho
  refine ⟨hr2,?_⟩
  intro hh
  have ht := Nat.dvd_sub hh hd
  have he : 2^n+1-(2^n-1) = 2 := by omega
  exact hr2 (he ▸ ht)

omit [CharP F 2] in
private theorem rootTorus_prime_free {n r : ℕ} (hn : 0 < n)
    (hcard : Nat.card F = (2^n)^2) (hc : ∀ x : F, J.conj x = x^(2^n))
    (hr : r.Prime) (hd : r ∣ 2^n-1) :
    ¬ r ∣ Nat.card (EvenInner.rootTorus J hJ) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hc
  have hsep := prime_separation hn hr hd
  apply Theory.GroupTheory.not_dvd_card_sup_of_normalizes hr
  · apply le_trans _ (root_torus_normalizes J hJ
      (one_lt_pow₀ (by decide) (by omega : n ≠ 0)) hcard hfixed)
    rintro _ ⟨k,rfl⟩
    exact ⟨k.val,rfl⟩
  · rw [EvenInner.rootImage_card J hJ hcard hfixed]
    intro hh
    exact hsep.1 (hr.dvd_of_dvd_pow (hr.dvd_of_dvd_pow hh))
  · intro hh
    have ht := hh.trans (Subgroup.card_range_dvd (EvenInner.normOneMap J hJ))
    rw [EvenInner.normOne_card J hcard hc] at ht
    exact hsep.2 ht

include hJ in
/-- Primes dividing q-1 do not divide the full involution centralizer. -/
private theorem involution_centralizer_prime_free_standard {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2^n)^2)
    (hc : ∀ x : F, J.conj x = x^(2^n)) {r : ℕ} (hr : r.Prime) (hd : r ∣ 2^n-1)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : orderOf x = 2) :
    ¬ r ∣ Nat.card (centralizer ({x} : Set _)) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hc
  obtain ⟨g,z,hz,he,hC,_⟩ := BinaryInvolutionTable.involution_root_geometry
    J hJ hn hcard hfixed x hx
  let f := MulAut.conj g
  have hzfixed : J.conj z.val.2 = z.val.2 := by
    have hh := z.property
    rw [hz,zero_mul,add_zero] at hh
    exact (eq_neg_of_add_eq_zero_right hh).trans (CharTwo.neg_eq _)
  have hroot : root J hJ z ∈ centralImage J hJ := by
    refine ⟨.ofAdd ⟨z.val.2,hzfixed⟩,?_⟩
    change hermitianUnipotentPSU J hJ (centralCoord J (.ofAdd ⟨z.val.2,hzfixed⟩)) =
      hermitianUnipotentPSU J hJ z
    apply congrArg (hermitianUnipotentPSU J hJ)
    exact Subtype.ext (Prod.ext hz.symm rfl)
  have hne : root J hJ z ≠ 1 := by
    rw [←he]
    intro hh
    have hx1 : x = 1 := f.injective (hh.trans (map_one f).symm)
    simp [hx1] at hx
  have hmap : (centralizer ({x} : Set _)).map f.toMonoidHom ≤ EvenInner.rootTorus J hJ := by
    rintro _ ⟨u,hu,rfl⟩
    apply central_borel_le_rootTorus J hJ
      (one_lt_pow₀ (by decide) (by omega : n ≠ 0)) hcard hfixed _ hroot hne
    refine ⟨?_,?_⟩
    · have hh := hC hu
      change f u ∈ normalizer (projectiveRoot J hJ : Set _) at hh
      rwa [root_normalizer_eq_borel J hJ
        (one_lt_pow₀ (by decide) (by omega : n ≠ 0)) hcard hfixed] at hh
    · change f u ∈ centralizer ({root J hJ z} : Set _)
      rw [mem_centralizer_singleton_iff,←he]
      exact (show Commute u x from mem_centralizer_singleton_iff.mp hu).map f
  intro hdiv
  apply rootTorus_prime_free J hJ (by omega) hcard hc hr hd
  apply dvd_trans _ (card_dvd_of_le hmap)
  rwa [card_map_of_injective f.injective]

/-- The same full-centralizer exclusion for any actual Hermitian form. -/
theorem involution_centralizer_prime_free {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2^n)^2)
    (hc : ∀ x : F, J.conj x = x^(2^n)) {r : ℕ} (hr : r.Prime) (hd : r ∣ 2^n-1)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : orderOf x = 2) :
    ¬ r ∣ Nat.card (centralizer ({x} : Set _)) := by
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hc
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^n) hcard hfixed
  rw [Nat.card_congr
    (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e x).toEquiv]
  exact involution_centralizer_prime_free_standard
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) rfl hn hcard hc hr hd
    (e x) ((e.orderOf_eq x).trans hx)


end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFixed

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open RootCoordinates HermitianForm
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- Primes dividing q-1 have no fixed nonidentity two-elements in PSU3(q). -/
theorem unitary_prime_two_centralizer {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    {r : ℕ} (hr : r.Prime) (hd : r ∣ 2^n-1)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hA : IsPGroup 2 A)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = r) :
    A ⊓ centralizer ({t} : Set _) = ⊥ := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let C := A ⊓ centralizer ({t} : Set _)
  have hC : IsPGroup 2 C := hA.to_le inf_le_left
  by_contra hne
  obtain ⟨u,hu,hu1⟩ := C.bot_or_exists_ne_one.resolve_left hne
  have hd2 : 2 ∣ Nat.card C :=
    (hC.dvd_orderOf (g := ⟨u,hu⟩) (fun he => hu1 (congrArg Subtype.val he))).trans
      (orderOf_dvd_natCard (⟨u,hu⟩ : C))
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hd2
  have hxt : t ∈ centralizer ({(x : ProjectiveSpecialUnitaryMatrixGroup J)} : Set _) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp x.property.2).symm
  have ho : orderOf (x : ProjectiveSpecialUnitaryMatrixGroup J) = 2 :=
    (Subgroup.orderOf_coe x).trans hx
  apply UnitaryFixed.involution_centralizer_prime_free J hn hcard hconj hr hd x ho
  have ht' : orderOf (⟨t,hxt⟩ : centralizer ({(x : ProjectiveSpecialUnitaryMatrixGroup J)} : Set _)) = r :=
    (Subgroup.orderOf_coe _).symm.trans ht
  have hh := orderOf_dvd_natCard (⟨t,hxt⟩ : centralizer ({(x : ProjectiveSpecialUnitaryMatrixGroup J)} : Set _))
  rwa [ht'] at hh

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The entire source Cartan has trivial fixed subgroup on every nonbinary
projective-unitary root, in either orientation and in every field degree. -/
theorem unitary_cartan_all_roots_fixedFree {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (i : Fin 2) (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : rankOne Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hroot : Nat.card (simpleRoot Q split i) = (2^n)^3)
    (s : RootReflection Q split i) (w : Weyl Q) :
    rootAt Q split i w ⊓ centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) = ⊥ := by
  have hq : 4 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
  obtain ⟨r,hr,hd⟩ := Nat.exists_prime_and_dvd (show 2^n-1 ≠ 1 by omega)
  let : Fact r.Prime := ⟨hr⟩
  have hdiv : 2^n-1 ∣ Nat.card ((Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split i)) := by
    rw [(unitary_rankOne_cartan_cyclic_card J Q split hn hcard hconj i hKi μ hroot s).2]
    have he : (2^n)^2-1 = (2^n-1)*(2^n+1) := by
      have hh : 2^n-1+1 = 2^n := by omega
      have hs : 1 ≤ (2^n)^2 := by nlinarith
      have hh2 := Nat.sub_add_cancel hs
      nlinarith
    rw [he,Nat.mul_div_assoc _ (Nat.gcd_dvd_right 3 (2^n+1))]
    exact Nat.dvd_mul_right _ _
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card'
    (G := ((Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split i))) r (hd.trans hdiv)
  let A := (simpleRoot Q split i).subgroupOf (rankOne Q split i)
  have hA : IsPGroup 2 A := (split.isTwo.to_le (simpleRoot_le Q split i)).comap_subtype
  have hf := unitary_prime_two_centralizer J hn hcard hconj hr hd
    (A.map μ.toMonoidHom) (hA.map _) (μ t.val)
    ((μ.orderOf_eq t.val).trans ((Subgroup.orderOf_coe t).trans ht))
  have hH : simpleRoot Q split i ⊓
      centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    let a : rankOne Q split i := ⟨u,(show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left) hu.1⟩
    have ha : μ a ∈ A.map μ.toMonoidHom ⊓ centralizer ({μ t.val} : Set _) := by
      refine ⟨mem_map_of_mem _ (show a ∈ A from hu.1),?_⟩
      apply mem_centralizer_singleton_iff.mpr
      have he : t.val*a = a*t.val := Subtype.ext (mem_centralizer_iff.mp hu.2 _ t.property)
      simpa only [map_mul] using congrArg μ he.symm
    exact mem_bot.mpr (congrArg Subtype.val (μ.map_eq_one_iff.mp (mem_bot.mp (hf ▸ ha))))
  let a := representative w
  have hh := congrArg (fun C => rightConjugate C (a : X ⧸ Q.D)) hH
  rw [rightConjugate_inf,rightConjugate_eq_self _
    (normalizer_le_normalizer_centralizer _ (torus_normalizes a))] at hh
  have hb : rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (a : X ⧸ Q.D) = ⊥ := by
    ext x
    exact (MulAut.conj (a : X ⧸ Q.D)).map_eq_one_iff
  rwa [hb] at hh

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource BenderSuzuki.MatrixGroups BenderSuzuki.External HermitianForm
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
private instance : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
private theorem unitary_sylow_card {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card T = (2^n)^3 := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  obtain ⟨a⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J (2^n) hcard hf
  let T' := T.mapSurjective (f := a.toMonoidHom) a.surjective
  let b : T ≃* T' := (T : Subgroup _).equivMapOfInjective a.toMonoidHom a.injective
  rw [Nat.card_congr b.toEquiv,
    Nat.card_congr (T'.equiv (EvenTwoRank.rootSylow
      (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) rfl hn hcard hf)).toEquiv]
  change Nat.card (OddPrimeSylow.NormalizedOuter.Coverage.rootGroup
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) rfl) = _
  exact OddPrimeSylow.NormalizedOuter.Coverage.rootGroup_card _ rfl _ hcard hf


omit [Finite E] in
/-- The q-1 part survives the literal scalar projection, including odd field degree. -/
theorem special_unitary_prime_projection_order {n r : ℕ}
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hr : r.Prime) (hd : r ∣ 2^n-1)
    (t : J.specialSubgroup) (ht : orderOf t = r) :
    orderOf (J.specialToProjective t) = r := by
  by_cases he : Even n
  · exact (orderOf_injective J.specialToProjective
      (EvenProjectiveComparison.specialToProjective_injective J he hconj) t).trans ht
  have hr3 : r ≠ 3 := by
    intro h
    have hm : 2^n % 3 = 2 := by
      rw [Nat.BinaryTorusParity.two_pow_mod_three,if_neg (by simpa only [Nat.even_iff] using he)]
    rw [h,Nat.dvd_iff_mod_eq_zero] at hd
    have hq : 1 ≤ 2^n := Nat.one_le_pow _ _ (by decide)
    omega
  have ho := orderOf_map_dvd J.specialToProjective t
  rw [ht] at ho
  rcases (Nat.dvd_prime hr).mp ho with ho | ho
  · have htK : t ∈ J.specialToProjective.ker := orderOf_eq_one_iff.mp ho
    have hc : t^3 = 1 := congrArg Subtype.val (J.specialToProjective_ker_cube ⟨t,htK⟩)
    have hh := orderOf_dvd_of_pow_eq_one hc
    rw [ht] at hh
    exact (hr3 ((Nat.dvd_prime Nat.prime_three).mp hh |>.resolve_left hr.ne_one)).elim
  · exact ho

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
private theorem simpleRoot_sylow_of_special_unitary {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (j : Fin 2) (μ : rankOne Q split j ≃* J.specialSubgroup)
    (hroot : Nat.card (simpleRoot Q split j) = (2^n)^3) :
    ∃ S : Sylow 2 (rankOne Q split j),
      (S : Subgroup (rankOne Q split j)) = (simpleRoot Q split j).subgroupOf (rankOne Q split j) := by
  let A := (simpleRoot Q split j).subgroupOf (rankOne Q split j)
  have hA : IsPGroup 2 A := (split.isTwo.to_le (simpleRoot_le Q split j)).comap_subtype
  obtain ⟨S,hS⟩ := hA.exists_le_sylow
  let S' := S.mapSurjective (f := μ.toMonoidHom) μ.surjective
  have hcA : Nat.card A = (2^n)^3 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left)).toEquiv).trans hroot
  let a : S ≃* S' := (S : Subgroup _).equivMapOfInjective μ.toMonoidHom μ.injective
  have hcS : Nat.card S = (2^n)^3 := by
    calc
      Nat.card S = Nat.card S' := Nat.card_congr a.toEquiv
      _ = (2^n)^3 := (by
      rw [Nat.card_congr (SylowOmega.specialSylowEquivProjective J S').toEquiv]
      exact unitary_sylow_card J hn hcard hconj _)
  exact ⟨S,(eq_of_le_of_card_ge hS (by rw [hcA,hcS])).symm⟩

theorem special_unitary_rankOne_cartan_cyclic_card {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* J.specialSubgroup)
    (hroot : Nat.card (simpleRoot Q split j) = (2^n)^3)
    (s : RootReflection Q split j) :
    IsCyclic ((Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j)) ∧
      Nat.card ((Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j)) =
        (2^n)^2-1 := by
  obtain ⟨S,hS⟩ := simpleRoot_sylow_of_special_unitary J Q split (by omega) hcard hconj j μ hroot
  let r := involutoryRootReflection Q split j s
  let t : rankOne Q split j := ⟨r.val,r.mem_rankOne⟩
  have ht : BenderSuzuki.PFAppendixIII.IsInvolution t := ⟨fun he => involutoryRootReflection_ne_one Q split j s
    (congrArg Subtype.val he),Subtype.ext (involutoryRootReflection_sq Q split j s)⟩
  have htB : t ∉ normalizer (S : Set (rankOne Q split j)) := by
    intro htB
    rw [show (S : Set (rankOne Q split j)) =
      ((simpleRoot Q split j).subgroupOf (rankOne Q split j) : Set _) from congrArg SetLike.coe hS] at htB
    exact Q.tits.representative_not_mem_B (Q.simple_mem j) r.val r.class_eq
      ((rankOne_borel_iff_root_normalizer Q split j hKj t).mpr htB)
  have he : BenderSuzuki.ZD.RankOneModelGeometry.twoPoint (normalizer (S : Set (rankOne Q split j))) t =
      (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j) := by
    ext x
    change x ∈ normalizer (S : Set (rankOne Q split j)) ∧
      x ∈ BenderSuzuki.PFchapter1section1.rightConjugate (normalizer (S : Set (rankOne Q split j))) t ↔ _
    rw [BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry.mem_rightConjugate]
    simp only [show (S : Set (rankOne Q split j)) =
      ((simpleRoot Q split j).subgroupOf (rankOne Q split j) : Set _) from congrArg SetLike.coe hS,
      ← rankOne_borel_iff_root_normalizer Q split j hKj]
    constructor
    · intro hx
      apply UnitarySource.oppositeLevi_inf_two_borels_le_torus Q split j
      refine ⟨UnitarySource.rootActor_le_oppositeLevi Q split j x.property,hx.1,?_⟩
      rw [borelConjugate_eq _ r.val r.class_eq]
      exact hx.2
    · intro hx
      exact ⟨hx.1,((torus_conjugate r.val).symm ▸ hx).1⟩
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  obtain ⟨C,hC⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_standard_basis J (2^n) hcard hf
  let a := OddPrimeSylow.NormalizedOuter.FormTransport.specialEquiv J C hC
  have hh := BenderSuzuki.ZD.RankOneModelGeometry.unitary_special_tori_of_equiv
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) hn rfl hcard hf
    (μ.trans a) S t ht htB
  rw [he] at hh
  exact ⟨hh.1,hh.2.1⟩

/-- The entire source Cartan has trivial fixed subgroup on every nonbinary
special-unitary root, in either orientation and in every field degree. -/
theorem special_unitary_cartan_all_roots_fixedFree {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (i : Fin 2) (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : rankOne Q split i ≃* J.specialSubgroup)
    (hroot : Nat.card (simpleRoot Q split i) = (2^n)^3)
    (s : RootReflection Q split i) (w : Weyl Q) :
    rootAt Q split i w ⊓ centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) = ⊥ := by
  have hq : 4 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
  obtain ⟨r,hr,hd⟩ := Nat.exists_prime_and_dvd (show 2^n-1 ≠ 1 by omega)
  let : Fact r.Prime := ⟨hr⟩
  have hdiv : 2^n-1 ∣ Nat.card ((Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split i)) := by
    rw [(special_unitary_rankOne_cartan_cyclic_card J Q split hn hcard hconj i hKi μ hroot s).2]
    have he : (2^n)^2-1 = (2^n-1)*(2^n+1) := by
      have hh : 2^n-1+1 = 2^n := by omega
      have hs : 1 ≤ (2^n)^2 := by nlinarith
      have hh2 := Nat.sub_add_cancel hs
      nlinarith
    rw [he]
    exact Nat.dvd_mul_right _ _
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card'
    (G := ((Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split i))) r (hd.trans hdiv)
  let A := (simpleRoot Q split i).subgroupOf (rankOne Q split i)
  have hA : IsPGroup 2 A := (split.isTwo.to_le (simpleRoot_le Q split i)).comap_subtype
  let f := J.specialToProjective.comp μ.toMonoidHom
  have horder : orderOf (μ t.val) = r :=
    (μ.orderOf_eq t.val).trans ((Subgroup.orderOf_coe t).trans ht)
  have hf := unitary_prime_two_centralizer J hn hcard hconj hr hd
    (A.map f) (hA.map _) (f t.val)
    (special_unitary_prime_projection_order J hconj hr hd (μ t.val) horder)
  have hk3 : IsPGroup 3 J.specialToProjective.ker :=
    fun x => ⟨1,by simpa using J.specialToProjective_ker_cube x⟩
  have hdis := (hA.map μ.toMonoidHom).disjoint_of_coprime hk3 (by decide : Nat.Coprime 2 3)
  have hH : simpleRoot Q split i ⊓
      centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    let a : rankOne Q split i := ⟨u,(show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left) hu.1⟩
    have ha : f a ∈ A.map f ⊓ centralizer ({f t.val} : Set _) := by
      refine ⟨mem_map_of_mem _ (show a ∈ A from hu.1),?_⟩
      apply mem_centralizer_singleton_iff.mpr
      have he : t.val*a = a*t.val := Subtype.ext (mem_centralizer_iff.mp hu.2 _ t.property)
      simpa only [map_mul] using congrArg f he.symm
    have hz : f a = 1 := mem_bot.mp (hf ▸ ha)
    have hzμ : μ a = 1 := disjoint_def.mp hdis
      (mem_map_of_mem _ (show a ∈ A from hu.1)) hz
    exact mem_bot.mpr (congrArg Subtype.val (μ.map_eq_one_iff.mp hzμ))
  let a := representative w
  have hh := congrArg (fun C => rightConjugate C (a : X ⧸ Q.D)) hH
  rw [rightConjugate_inf,rightConjugate_eq_self _
    (normalizer_le_normalizer_centralizer _ (torus_normalizes a))] at hh
  have hb : rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (a : X ⧸ Q.D) = ⊥ := by
    ext x
    exact (MulAut.conj (a : X ⧸ Q.D)).map_eq_one_iff
  rwa [hb] at hh

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
