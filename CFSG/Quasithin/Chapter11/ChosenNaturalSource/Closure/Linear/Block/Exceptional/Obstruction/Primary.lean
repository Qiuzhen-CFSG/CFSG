module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncentralFittingExclusion

/-!
# Odd primary factors surviving the central quotient

For a C-component in a two-reduced SQTK group, each primary Fitting seed
survives modulo the ambient center with order divisible by p². The elementary
seed is inverted by an involution, so meets that center trivially. The
extraspecial seed loses at most its order-p center. This treats all homocyclic
exponents and all primary factors, without assuming SQTK inheritance through
the central quotient.

Prime support and the SL₂ Fitting quotient then contribute a prime cube,
contradicting the order of GL₈(2). Thus the Fitting subgroup is central when
only the order of the quotient by the center divides |GL₈(2)|. This strengthens
the whole-component bound used in C.5 to the literal quotient in 11.5.7.

Source: Aschbacher–Smith A.3.6, A.3.14(13–14), and 11.5.7,
refs/quasithin.pdf, printed pp.43–45,50,782.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
open CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
open CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.PrimaryShapes
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Obstruction
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

/-- Every primary seed contributes a square after removing the ambient center. -/
theorem seed_square_dvd_central_fitting_index
    (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hquot : PrimeSL2FittingQuotient L)
    {p : ℕ} [Fact p.Prime] (s : PrimarySeed p L) :
    p ^ 2 ∣ (center L).relIndex (fittingSubgroup L) := by
  let : Group.IsPerfect L := hL.perfect
  let q := QuotientGroup.mk' (center L)
  let j := (pCore p L).subtype.comp s.X.subtype
  let f := q.comp j
  have hk (x : s.X) (hx : x ∈ f.ker) : j x ∈ center L :=
    (QuotientGroup.eq_one_iff (j x)).mp hx
  have hdiv : p ^ 2 ∣ f.ker.index := by
    rcases s.models with ⟨hc, ⟨e⟩⟩ | he
    · obtain ⟨t, ht, hnt⟩ := exists_involution_outside_fitting hO hL hquot
      have hinv := elementary_seed_inverted s hc e t
        (ht ▸ pow_orderOf_eq_one t) hnt
      have hker : f.ker = ⊥ := by
        apply (Subgroup.eq_bot_iff_forall _).mpr
        intro x hx
        have hf : coreAction s.X t x = x := by
          apply Subtype.ext
          apply Subtype.ext
          change t * j x * t⁻¹ = j x
          rw [mem_center_iff.mp (hk x hx) t, mul_inv_cancel_right]
        have hx2 : x ^ 2 = 1 := by
          have hi : x = x⁻¹ := hf.symm.trans (hinv x)
          calc
            x ^ 2 = x * x := pow_two x
            _ = x⁻¹ * x := congrArg (fun y => y * x) hi
            _ = 1 := inv_mul_cancel x
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
          (Nat.coprime_two_right.mpr s.odd)
          (orderOf_dvd_of_pow_eq_one (s.supercritical.pow_eq_one x))
          (orderOf_dvd_of_pow_eq_one hx2))
      rw [hker, index_bot, hc]
    · let : IsExtraspecial p s.X := he.1.1
      have hkz : f.ker ≤ center s.X := by
        intro x hx
        apply mem_center_iff.mpr
        intro y
        apply Subtype.ext
        apply Subtype.ext
        exact mem_center_iff.mp (hk x hx) (j y)
      have hc : (center s.X).index = p ^ 2 := by
        have hh := (center s.X).index_mul_card
        rw [IsExtraspecial.center_order_p p s.X, he.1.2] at hh
        apply Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos
        calc
          (center s.X).index * p = p ^ 3 := hh
          _ = p ^ 2 * p := by ring
      exact hc ▸ index_dvd_of_le hkz
  have hle : f.range ≤ (fittingSubgroup L).map q := by
    rintro _ ⟨x, rfl⟩
    exact mem_map_of_mem q (pCore_le_fitting L p (x : pCore p L).property)
  rw [index_ker] at hdiv
  have hh := hdiv.trans (card_dvd_of_le hle)
  simpa only [← relIndex_ker (fittingSubgroup L) q, q, QuotientGroup.ker_mk'] using hh

/-- A bound on the central quotient excludes every noncentral Fitting branch. -/
theorem fitting_central_of_central_order
    {κ : GroupClass} (hG : IsSQTK κ G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent)
    (hd : Nat.card (L ⧸ center L) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2))) :
    fittingSubgroup L ≤ center L := by
  by_contra hn
  obtain ⟨r, hr, hr3, ⟨e⟩⟩ := primeSL2FittingQuotient_of_noncentral
    CFSG.Quasithin.ChapterA.RankActions.primeSL2CoverRigidity hG hO hL hn
  let : Fact r.Prime := ⟨hr⟩
  have hq : PrimeSL2FittingQuotient L := ⟨r, hr, hr3, ⟨e⟩⟩
  have hnon : Nat.card (fittingSubgroup L) ≠ 1 := by
    intro hc
    apply hn
    rw [card_eq_one.mp hc]
    exact bot_le
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hnon
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨s⟩ := exists_primarySeed
    CFSG.Quasithin.ChapterA.RankActions.primeSL2CoverRigidity hG hO hL hq hpd
  have hs := CoreShapes.PrimeSupport.prime_support
    CFSG.Quasithin.ChapterA.RankActions.primeSL2CoverRigidity hG hO hL hr3 e hp hpd
  have hsq := seed_square_dvd_central_fitting_index hO hL hq s
  have hzc : center L ≤ fittingSubgroup L := le_sSup ⟨inferInstance, inferInstance⟩
  have hsGL : p ^ 2 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :=
    hsq.trans ((relIndex_dvd_index_of_le hzc).trans hd)
  have hpGL := Representation.BinaryEight.prime_divisors_binary_GL_eight hp
    ((dvd_pow_self p (by decide : 2 ≠ 0)).trans hsGL)
  have hpr : p = r := by
    rcases hs with he | ⟨hr5, hmod⟩
    · exact he
    · rcases hpGL with h | h | h | h | h | h | h <;> subst p
      all_goals try omega
      rw [Matrix.card_GL_field] at hsGL
      norm_num [Fin.prod_univ_succ] at hsGL
  subst p
  have hrq : r ∣ (fittingSubgroup L).index := by
    rw [index_eq_card, Nat.card_congr e.toEquiv, Atlas.card_sl_two, Nat.card_zmod]
    exact dvd_mul_right _ _
  have hcube : r ^ 3 ∣ Nat.card (L ⧸ center L) := by
    rw [← index_eq_card, ← relIndex_mul_index hzc, show r ^ 3 = r ^ 2 * r by ring]
    exact Nat.mul_dvd_mul hsq hrq
  have hb := hcube.trans hd
  rcases hpGL with h | h | h | h | h | h | h <;> subst r
  all_goals try omega
  all_goals rw [Matrix.card_GL_field] at hb
  all_goals norm_num [Fin.prod_univ_succ] at hb

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Obstruction
