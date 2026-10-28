module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddUnitary
public import Theory.SpecificGroups.GL2.FermatFrattini
public import Theory.SpecificGroups.PSL3.OddSylowCenter
public import Theory.SpecificGroups.SU3.OddSylowCenter
public import Theory.GroupTheory.SylowOuterFrattiniSections
import all Theory.SpecificGroups.SU3.CyclicCoreSylow.Generators

/-!
# Odd ternary outer exclusions for the original binary-three residual

Odd PSL₃ Sylow two-subgroups identify with the actual GL₂ involution
centralizer Sylows. In the split congruence, a maximal two-power diagonal
unit and the coordinate swap generate a Sylow subgroup; the other congruence
uses the semidihedral generators. Both have Frattini quotient of order at
most four. For PSU₃ over an odd prime-square fixed field, the original
hyperbolic torus and Weyl matrix give a semidihedral Sylow subgroup through
the full projective map. The stored Hermitian form is transported explicitly.

The Burnside basis kernel and the solvable permutation group on four points
then give solvable Sylow automorphisms and hence solvable outer groups.
Central-cover descent excludes these rows from the actual SL₃(2) section.
The final chosen-module consumer preserves the remaining seven B families.

The proof-only `import all` reuses the internal Weyl identities from the
existing prime-field construction for its prime-square extension; no shared
visibility or public statement is changed. The generator and order arguments
are adapted from `SU3/CyclicCoreSylow/Generators.lean` and `Order.lean`.
Source: ABG II.2 Lemma 1 and Aschbacher–Smith 4.4.10–12,
printed pp.621–622, used by 7.3.4 and 7.6.1, printed pp.699,702,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddTernary
open Matrix.GeneralLinearGroup

private theorem pair_frattini_le_four {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (a b : P) (hg : closure ({a,b} : Set P) = ⊤) :
    Nat.card (P ⧸ frattini P) ≤ 4 := by
  classical
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  have hr : Group.rank P ≤ 2 := (Group.rank_le (S := {a,b}) (by simpa using hg)).trans
    (Finset.card_insert_le _ _ |>.trans (by simp))
  have hq := (Group.rank_le_of_surjective (QuotientGroup.mk' (frattini P))
    (QuotientGroup.mk'_surjective _)).trans hr
  have hd := card_dvd_exponent_pow_rank' (P ⧸ frattini P)
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (P ⧸ frattini P)))
  exact (Nat.le_of_dvd (by positivity) hd).trans
    (show 2 ^ Group.rank (P ⧸ frattini P) ≤ 4 by
      exact Nat.pow_le_pow_right (by decide) hq)

private theorem split_frattini_le_four {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F % 4 = 1)
    (P : Sylow 2 (GL (Fin 2) F)) : Nat.card (P ⧸ frattini P) ≤ 4 := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  obtain ⟨k,r,hr,hqr⟩ := Nat.exists_eq_two_pow_mul_odd (show q-1 ≠ 0 by omega)
  have hk : 2 ≤ k := by
    by_contra! hk
    obtain ⟨s,hs⟩ := hr
    interval_cases k <;> simp only [pow_zero,pow_one,one_mul] at hqr <;> omega
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hdu : 2^k ∣ orderOf u := by rw [hu,Nat.card_units]; exact ⟨r,hqr⟩
  let z := u ^ (orderOf u / 2^k)
  have hz : orderOf z = 2^k := orderOf_pow_orderOf_div (orderOf_pos u).ne' hdu
  let H := diagonalSwapSubgroup F z
  have hp2 : 2 ^ (2*k+1) = 2*(2^k)^2 := by
    rw [show 2*k+1=k*2+1 by omega,pow_add,pow_mul,pow_one]
    ring
  have hc : Nat.card H = 2 ^ (2*k+1) := by
    rw [diagonalSwapSubgroup_card,hz,hp2]
  have htwo : IsPGroup 2 H := IsPGroup.of_card hc
  have hind : Odd H.index := by
    have hG : Nat.card (GL (Fin 2) F) = q*(q-1)^2*(q+1) := by
      let := Fintype.ofFinite F
      rw [Matrix.card_GL_field]
      simp only [Fin.prod_univ_two,Fin.val_zero,Fin.val_one,pow_zero,pow_one,
        ←Nat.card_eq_fintype_card]
      change (q^2-1)*(q^2-q) = _
      rw [show q^2-1=(q-1)*(q+1) by simpa only [one_pow,mul_comm] using Nat.sq_sub_sq q 1,
        show q^2-q=q*(q-1) by rw [pow_two,Nat.mul_sub_left_distrib,mul_one]]
      ring
    have hplus : q+1=2*((q+1)/2) := by omega
    have hoq : Odd q := Nat.odd_iff.mpr (by omega)
    have hop : Odd ((q+1)/2) := Nat.odd_iff.mpr (by omega)
    have he := H.card_mul_index
    rw [hc,hG,hqr,hplus] at he
    have hi : H.index = q*r^2*((q+1)/2) := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 2^(2*k+1) by positivity)
      rw [he,hp2]
      ring
    rw [hi]
    exact (hoq.mul hr.pow).mul hop
  let S : Sylow 2 (GL (Fin 2) F) := htwo.toSylow hind.not_two_dvd_nat
  rw [SylowFrattiniBounds.card_congr (P.equiv S)]
  let a : H := ⟨diagonalPair F (z,1),subset_closure (by simp)⟩
  let b : H := ⟨coordinateSwap F,subset_closure (by simp)⟩
  apply pair_frattini_le_four htwo a b
  apply Subgroup.map_injective H.subtype_injective
  rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,H.range_subtype,
    Set.image_insert_eq,Set.image_singleton]
  change closure {diagonalPair F (z,1),coordinateSwap F} = diagonalSwapSubgroup F z
  apply le_antisymm
  · exact closure_mono (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at *; tauto)
  · apply (closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact subset_closure (by simp)
    · rw [←coordinateSwap_conj_diagonalPair F z 1]
      exact mul_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
        (inv_mem (subset_closure (by simp)))
    · exact subset_closure (by simp)

/-- The actual Sylow two-subgroups in odd degree two have two Frattini generators. -/
theorem linear_two_frattini_le_four {F : Type*} [Field F] [Finite F]
    (ho : Odd (Nat.card F)) (P : Sylow 2 (GL (Fin 2) F)) :
    Nat.card (P ⧸ frattini P) ≤ 4 := by
  have hm : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by
    have := Nat.odd_iff.mp ho
    omega
  rcases hm with hm | hm
  · exact split_frattini_le_four hm P
  · obtain ⟨S,n,_,_,a,b,_,_,_,hg,_,_⟩ := exists_semidihedral_sylow F hm
    rw [SylowFrattiniBounds.card_congr (P.equiv S)]
    exact pair_frattini_le_four S.isPGroup' a b hg

/-- The actual odd PSL₃ Sylow group inherits the two-generator bound from
its involution centralizer, through the full odd central covering kernel. -/
theorem linear_three_frattini_le_four {F : Type*} [Field F] [Finite F]
    (ho : Odd (Nat.card F)) (P : Sylow 2 PSL(3,F)) :
    Nat.card (P ⧸ frattini P) ≤ 4 := by
  have h2 : (2:F) ≠ 0 := Field.two_ne_zero_of_odd_card F ho
  let S : Sylow 2 SL(3,F) := default
  let R : Sylow 2 (GL (Fin 2) F) := default
  have hi := odd_index_centralizer_of_one_involution_class
    (Matrix.SL3.standardInvolution F) (Matrix.SL3.standardInvolution_orderOf F h2)
    (fun z hz => Matrix.SL3.involution_isConj_standard F z hz h2)
  obtain ⟨e⟩ := sylow_equiv_of_odd_index _ hi
    (Matrix.SL3.standardInvolutionCentralizerEquiv F h2).symm S R
  have hk : Nat.Coprime 2 (Nat.card (Matrix.PSL3.projection F).ker) := by
    rw [Matrix.PSL3.projection_ker]
    exact Nat.coprime_two_left.mpr (Matrix.SL3.odd_card_center F)
  let a := Sylow.equivOfSurjectiveCoprime (Matrix.PSL3.projection F)
    (Matrix.PSL3.projection_surjective F) hk S P
  rw [←SylowFrattiniBounds.card_congr a,SylowFrattiniBounds.card_congr e]
  exact linear_two_frattini_le_four ho R

open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.CyclicCoreSylow HermitianForm.OddPrimeSylow.NormalizedOuter

private theorem unitary_generators {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {p : ℕ} (hp1 : 1 ≤ p) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (n : ℕ) (hdiv : 2 ^ (n + 2) ∣ p - 1) (hodd : Odd ((p - 1) / 2 ^ (n + 2))) :
    ∃ x y : ProjectiveSpecialUnitaryMatrixGroup J,
      orderOf x = 2 ^ (n + 3) ∧ y ^ 2 = 1 ∧
      y * x * y⁻¹ = x ^ (2 ^ (n + 2) - 1) ∧
      entrywiseProjectiveAut J hJ x = x ^ (2 ^ (n + 2) + 1) ∧
      entrywiseProjectiveAut J hJ y = y := by
  have hdivF : 2 ^ (n + 3) ∣ Nat.card F - 1 := by
    rw [hcard, show p ^ 2 - 1 = (p - 1) * (p + 1) by
      simpa only [one_pow, mul_comm] using Nat.sq_sub_sq p 1,
      show n + 3 = (n + 2) + 1 by omega, pow_succ]
    exact Nat.mul_dvd_mul hdiv (even_iff_two_dvd.mp ho.add_one)
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hdu : 2 ^ (n + 3) ∣ orderOf u := by rw [hu, Nat.card_units]; exact hdivF
  let r := u ^ (orderOf u / 2 ^ (n + 3))
  have hr : orderOf r = 2 ^ (n + 3) := orderOf_pow_orderOf_div (orderOf_pos u).ne' hdu
  obtain ⟨k, hk⟩ := hodd
  have hrep : p - 1 = 2 ^ (n + 2) * (2 * k + 1) := by
    rw [← hk]; exact (Nat.mul_div_cancel' hdiv).symm
  have hexp : p = 2 ^ (n + 3) * k + (2 ^ (n + 2) + 1) := by
    rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
    nlinarith only [hrep, Nat.sub_add_cancel hp1]
  have hpow : r ^ p = r ^ (2 ^ (n + 2) + 1) := by
    rw [hexp, pow_add, pow_mul, ← hr, pow_orderOf_eq_one, one_pow, one_mul]
  have hinv : (r ^ p)⁻¹ = r ^ (2 ^ (n + 2) - 1) := by
    apply inv_injective
    rw [inv_inv]
    apply eq_inv_of_mul_eq_one_left
    rw [hpow, ← pow_add]
    have he : 2 ^ (n + 2) + 1 + (2 ^ (n + 2) - 1) = 2 ^ (n + 3) := by
      have hpos : 0 < 2 ^ (n + 2) := by positivity
      rw [show 2 ^ (n + 3) = 2 ^ (n + 2) * 2 by ring]
      omega
    rw [he, ← hr, pow_orderOf_eq_one]
  have hγ : Units.map J.conj.toMonoidHom r = r ^ p := by
    apply Units.ext
    exact hc r
  refine ⟨hermitianTorusPSU J hJ r, hermitianWeylPSU J hJ, ?_, weyl_square J hJ, ?_, ?_, entrywise_weyl J hJ⟩
  · rw [(hermitianTorusPSU J hJ).orderOf_map_eq_of_coprime_of_isPGroup_ker
      (HermitianForm.BorelTorus.projective_ker_isThreeGroup J hJ) r (by rw [hr]; exact (by decide : Nat.Coprime 3 2).pow_right _)]
    exact hr
  · rw [weyl_action, hγ, hinv, map_pow]
  · rw [entrywise_torus, hγ, hpow, map_pow]

private theorem unitary_two_subgroup_card_le {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {p : ℕ} (hp1 : 1 ≤ p) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hfixed : Nat.card {x : F // J.conj x = x} = p)
    (n : ℕ) (hdiv : 2 ^ (n + 2) ∣ p - 1) (hodd : Odd ((p - 1) / 2 ^ (n + 2)))
    (R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hR : IsPGroup 2 R) :
    Nat.card R ≤ 2 ^ (n + 4) := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨_, _, _, _, _, _, _, _, hGcard, _⟩ := huppert_II_10_12 J p hcard hfixed hJ
  have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    simpa only [one_pow, mul_comm] using Nat.sq_sub_sq p 1
  have hden : Nat.gcd 3 (p + 1) ∣ (p ^ 3 + 1) * p ^ 3 * (p ^ 2 - 1) := by
    rw [hsq]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 (p + 1)) _) _
  have hRd : Nat.card R ∣ (p ^ 3 + 1) * p ^ 3 * (p ^ 2 - 1) :=
    R.card_subgroup_dvd_card.trans (by rw [hGcard]; exact Nat.div_dvd_of_dvd hden)
  have hfour : 4 ∣ p - 1 := (show 4 ∣ 2 ^ (n + 2) by
    exact ⟨2 ^ n, by ring⟩).trans hdiv
  have hplus : p + 1 = 2 * ((p + 1) / 2) := by
    have := Nat.odd_iff.mp ho
    omega
  have hplusodd : Odd ((p + 1) / 2) := by
    rw [Nat.odd_iff]
    omega
  have hminus : p - 1 = 2 ^ (n + 2) * ((p - 1) / 2 ^ (n + 2)) :=
    (Nat.mul_div_cancel' hdiv).symm
  have hfactor : p ^ 3 + 1 = (p + 1) * (p * (p - 1) + 1) := by
    have he := Nat.sub_add_cancel hp1
    nlinarith [congrArg (fun t : ℕ => p * p * t) he]
  have hfactorodd : Odd (p * (p - 1) + 1) := by
    apply Even.add_one
    apply Even.mul_left
    exact even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 4) hfour)
  let d := ((p + 1) / 2) ^ 2 * p ^ 3 * (p * (p - 1) + 1) * ((p - 1) / 2 ^ (n + 2))
  have hd : Odd d := ((hplusodd.pow.mul ho.pow).mul hfactorodd).mul hodd
  have he : (p ^ 3 + 1) * p ^ 3 * (p ^ 2 - 1) = 2 ^ (n + 4) * d := by
    rw [hfactor, hsq]
    nth_rw 2 [hminus]
    rw [hplus]
    dsimp [d]
    ring
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hcop : (Nat.card R).Coprime d := by rw [hk]; exact hd.coprime_two_left.pow_left k
  apply Nat.le_of_dvd (by positivity : 0 < 2 ^ (n + 4))
  exact hcop.dvd_of_dvd_mul_right (he ▸ hRd)

private theorem unitary_standard_frattini_le_four {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {q : ℕ} (hq : 1 < q) (hm : q % 4 = 1)
    (hc : Nat.card F = q^2) (hj : ∀ x, J.conj x = x^q)
    (hf : Nat.card {x : F // J.conj x = x} = q)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (P ⧸ frattini P) ≤ 4 := by
  have ho : Odd q := Nat.odd_iff.mpr (by omega)
  obtain ⟨v,d,hd,he⟩ := Nat.exists_eq_two_pow_mul_odd (show q-1 ≠ 0 by omega)
  have hv : 2 ≤ v := by
    by_contra! hh
    obtain ⟨k,hk⟩ := hd
    interval_cases v <;> simp only [pow_zero,pow_one,one_mul] at he <;> omega
  let n := v-2
  have hn : n+2=v := Nat.sub_add_cancel hv
  have hdiv : 2^(n+2) ∣ q-1 := hn ▸ ⟨d,he⟩
  have hodd : Odd ((q-1)/2^(n+2)) := by
    rw [hn,he,Nat.mul_div_cancel_left _ (by positivity)]
    exact hd
  obtain ⟨x,y,hx,hy,hyx,_,_⟩ := unitary_generators J hJ (by omega) ho hc hj n hdiv hodd
  have hne : x^(2^(n+2)-1) ≠ x := by
    intro heq
    have h4 : 4 ≤ 2^(n+2) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ n+2)
    have horder : orderOf x = 2^(n+2)*2 := by rw [hx]; ring
    have h := pow_injOn_Iio_orderOf (x:=x)
      (show 2^(n+2)-1 < orderOf x by rw [horder]; omega)
      (show 1 < orderOf x by rw [horder]; omega) (by simpa only [pow_one] using heq)
    omega
  have hout : y ∉ zpowers x := by
    rintro ⟨i,rfl⟩
    apply hne
    rw [←hyx,(Commute.zpow_self x i).eq,mul_inv_cancel_right]
  obtain ⟨hsize,hshape,_⟩ := ABG.semidihedral_generated_subgroup_data
    (by omega : 2 ≤ n+2) x y (by simpa only [Nat.add_assoc] using hx) hy hout hyx
  let Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    { toSubgroup := zpowers x ⊔ zpowers y
      isPGroup' := IsPGroup.of_card hsize
      is_maximal' := fun {R} hR hQR =>
        (eq_of_le_of_card_ge hQR (by
          rw [hsize]
          exact unitary_two_subgroup_card_le J hJ (by omega) ho hc hf n hdiv hodd R hR)).symm }
  rw [SylowFrattiniBounds.card_congr (P.equiv Q)]
  obtain ⟨_,_,_,a,b,_,_,_,hg⟩ := hshape
  exact pair_frattini_le_four Q.isPGroup' a b hg

/-- For an odd prime-square fixed field, the literal unitary Sylow subgroup
has two Frattini generators, with its stored Hermitian form retained. -/
theorem unitary_three_square_frattini_le_four {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hc : Nat.card F = (p^2)^2) (hj : ∀ x, J.conj x = x^(p^2))
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (P ⧸ frattini P) ≤ 4 := by
  let : Fact p.Prime := ⟨hp⟩
  have hf : Nat.card {x : F // J.conj x=x} = p^2 :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj p 2 (by decide) hc hj
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J (p^2) hc hf
  let R := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  rw [SylowFrattiniBounds.card_congr (P.equivMapOfInjective e.toMonoidHom e.injective)]
  have hm : p % 4 = 1 ∨ p % 4 = 3 := by
    have := Nat.odd_iff.mp ho
    omega
  have hsquare : p^2 % 4 = 1 := by
    rw [Nat.pow_mod]
    rcases hm with hm | hm <;> simp [hm]
  exact unitary_standard_frattini_le_four (FormTransport.standardForm J) rfl
    (by have := hp.two_le; nlinarith) hsquare hc hj hf R

private theorem small_mulAut_solvable {E : Type*} [Group E] [Finite E]
    (hE : Nat.card E ≤ 4) : Group.IsSolvable (MulAut E) := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let j : E ↪ Fin 4 := (Fintype.equivFin E).toEmbedding.trans
    (Fin.castLEEmb (by simpa only [Nat.card_eq_fintype_card] using hE))
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm E) := Group.isSolvable_of_isSolvable_injective
    (Equiv.Perm.viaEmbeddingHom_injective j)
  exact Group.isSolvable_of_isSolvable_injective
    (f:=MulAut.toPerm E) (fun a b he => MulEquiv.ext (fun x => Equiv.congr_fun he x))

private theorem small_frattini_aut_solvable {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hb : Nat.card (P ⧸ frattini P) ≤ 4) :
    Group.IsSolvable (MulAut P) := by
  let f := quotientAut (frattini P)
  let : Group.IsNilpotent f.ker := (isPGroup_quotientAut_frattini_kernel hP).isNilpotent
  let : Group.IsSolvable (MulAut (P ⧸ frattini P)) := small_mulAut_solvable hb
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [range_subtype])

/-- Odd PSL₃ has solvable outer automorphisms via the actual two-generator Sylow. -/
theorem linear_three_outer_solvable {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL S 3 q) :
    Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 S := default
  let R := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  have hb : Nat.card (P ⧸ frattini P) ≤ 4 := by
    rw [SylowFrattiniBounds.card_congr (P.equivMapOfInjective e.toMonoidHom e.injective)]
    exact linear_three_frattini_le_four (hF.symm ▸ ho) R
  let : Group.IsSolvable (MulAut P) := small_frattini_aut_solvable P.isPGroup' hb
  let : Group.IsSolvable (fixingSubgroup (MulAut S) (P : Set S)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  exact MulAut.outer_isSolvable_of_sylow_aut P

/-- Odd prime-square PSU₃ has solvable outer automorphisms; no field automorphism
coverage or additional source hypothesis is required. -/
theorem unitary_three_square_outer_solvable {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSU S 3 (p^2)) :
    Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := hm
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv S e.toEquiv
  let P : Sylow 2 S := default
  let R := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  have hb : Nat.card (P ⧸ frattini P) ≤ 4 := by
    rw [SylowFrattiniBounds.card_congr (P.equivMapOfInjective e.toMonoidHom e.injective)]
    exact unitary_three_square_frattini_le_four J hp ho hF hj R
  let : Group.IsSolvable (MulAut P) := small_frattini_aut_solvable P.isPGroup' hb
  let : Group.IsSolvable (fixingSubgroup (MulAut S) (P : Set S)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  exact MulAut.outer_isSolvable_of_sylow_aut P

private instance : IsSimpleGroup BinaryLinearThree.Group := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  exact Matrix.PSL3Two.equiv.isSimpleGroup

private instance : Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)

/-- The original perfect central cover retains its entire center in both
odd prime-square degree-three exclusions. -/
theorem cover_exclusions {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f) :
    (∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 q) ∧
      ∀ p : ℕ, p.Prime → Odd p → ¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 (p^2) := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  have hbad (hs : Group.IsSolvable (MulAut.Outer (K ⧸ center K))) : False := by
    let := hs
    let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
      (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
    obtain ⟨U,f,hf⟩ := ho
    exact Group.IsPerfect.not_isSolvable BinaryLinearThree.Group
      (Group.isSolvable_of_surjective hf)
  exact ⟨fun q hq hm => hbad (linear_three_outer_solvable hq hm),
    fun p hp hq hm => hbad (unitary_three_square_outer_solvable hp hq hm)⟩

/-- Both the rank-six inner placement and the actual outer section exclude
the square-field ternary families on the original central quotient. -/
theorem square_model_exclusions {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hc : 6 ≤ primeRank 2 (K ⧸ center K) ∨
      ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
        Function.Surjective f) :
    ∀ p : ℕ, p.Prime → Odd p →
      (¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 (p^2)) ∧
      (¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 (p^2)) := by
  rcases hc with hr | ho
  · intro p _ hq
    constructor
    · intro hm
      have := ChapterA.Section02.odd_psl_three_twoRank_le_two hq.pow hm
      omega
    · intro hm
      have := ChapterA.Section02.odd_psu_three_twoRank_le_two hq.pow hm
      omega
  · obtain ⟨hl,hu⟩ := cover_exclusions ho
    exact fun p hp hq => ⟨hl (p^2) hq.pow,hu p hp hq⟩

/-- The seven actual outer model families remaining after the ternary
prime-square exclusions. The original quotient markings are retained. -/
inductive RemainingOuterModel (Q : Type*) [Group Q] : Prop
  | symplectic_odd (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (iso : ClassicalGroup.IsPSp Q 2 p)
  | g2_odd (p : ℕ) (hp : p.Prime) (ho : Odd p) (iso : ClassificationModels.IsG2At Q p)
  | linear_four (p : ℕ) (hp : p.Prime) (hf : ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1)
      (iso : ClassicalGroup.IsPSL Q 4 p)
  | unitary_four (p : ℕ) (hp : p.Prime) (hm : ∃ k : ℕ, p + 1 = 2 ^ k)
      (iso : ClassicalGroup.IsPSU Q 4 p)
  | symplectic_binary (iso : ClassicalGroup.IsPSp Q 3 2)
  | janko_three (iso : Nonempty (Q ≃* Sporadic.Janko3.Model))
  | mcl (iso : Nonempty (Q ≃* Sporadic.LeechRelated.McL.Carrier))

/-- The literal B catalogue has neither ternary square-field outer case. -/
theorem remaining_outer_models {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f) : RemainingOuterModel (K ⧸ center K) := by
  obtain ⟨hl,hu⟩ := cover_exclusions ho
  cases DoubledBinaryOddUnitary.remaining_outer_models hm ho with
  | linear_three_square p hp hq e => exact (hl (p^2) hq.pow e).elim
  | unitary_three_square p hp hq e => exact (hu p hp hq e).elim
  | symplectic_odd p hp hq e => exact .symplectic_odd p hp hq e
  | g2_odd p hp hq e => exact .g2_odd p hp hq e
  | linear_four p hp hf e => exact .linear_four p hp hf e
  | unitary_four p hp hf e => exact .unitary_four p hp hf e
  | symplectic_binary e => exact .symplectic_binary e
  | janko_three e => exact .janko_three e
  | mcl e => exact .mcl e

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddTernary
