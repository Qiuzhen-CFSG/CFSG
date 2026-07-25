/-
Authors: OpenAI
-/

module

public import BenderSuzuki.PFAppendixIII.proposition_1
import BenderSuzuki.PFAppendixIII.lemma_1
import Mathlib.Algebra.Module.ZMod

/-!
# Peterfalvi Appendix III, Proposition 2
-/

namespace BenderSuzuki
namespace PFAppendixIII

universe u

/-- Appendix III, Proposition 2. For a `B(n,1)` central extension written
with its quadratic-field norm coordinates, the induced action of its
automorphism group on the quotient is exactly the semilinear group. Its
kernel is elementary abelian of exponent two. -/
public theorem proposition2_automorphisms_semilinear
    (F E P : Type u)
    [Field F] [Fintype F] [CharP F 2]
    [Field E] [Fintype E] [Algebra F E]
    [Group P] [Finite P]
    (conjugation : E ≃ₐ[F] E)
    (hconjugation : orderOf conjugation = 2)
    (norm : E → F)
    (hnorm : ∀ x : E, algebraMap F E (norm x) = x * conjugation x)
    (iota : Multiplicative F →* P)
    (pi : P →* Multiplicative E)
    (hiota : Function.Injective iota)
    (hpi : Function.Surjective pi)
    (hexact : iota.range = pi.ker)
    (hcentral : iota.range ≤ Subgroup.center P)
    (hsquare : ∀ p : P,
      p ^ 2 =
        iota (Multiplicative.ofAdd (norm (pi p).toAdd))) :
    ∃ induced : MulAut P →* AddAut E,
      (∀ alpha : MulAut P, ∀ p : P,
        Multiplicative.ofAdd (induced alpha (pi p).toAdd) = pi (alpha p)) ∧
      (∀ f : AddAut E, f ∈ induced.range ↔
        ∃ (lambda : Eˣ) (sigma : E ≃+* E),
          ∀ x : E, f x = (lambda : E) * sigma x) ∧
      IsMulCommutative induced.ker ∧
      ∀ alpha : induced.ker, alpha ^ 2 = 1 := by
  classical
  letI : CharP E 2 :=
    charP_of_injective_algebraMap (algebraMap F E).injective 2
  have hnorm_zero_iff (x : E) : norm x = 0 ↔ x = 0 := by
    constructor
    · intro hx
      have hprod : x * conjugation x = 0 := by
        rw [← hnorm x, hx, map_zero]
      rcases mul_eq_zero.mp hprod with hx | hx
      · exact hx
      · exact conjugation.injective (by simpa using hx)
    · intro hx
      subst x
      apply (algebraMap F E).injective
      simpa using hnorm 0
  have hiota_range_eq_involutions (p : P) :
      p ∈ iota.range ↔ p ^ 2 = 1 := by
    constructor
    · intro hp
      have hpker : p ∈ pi.ker := by
        rw [← hexact]
        exact hp
      have hp_pi : pi p = 1 := MonoidHom.mem_ker.mp hpker
      rw [hsquare, hp_pi]
      change iota (Multiplicative.ofAdd (norm 0)) = 1
      rw [(hnorm_zero_iff 0).2 rfl]
      simp
    · intro hp
      have hnorm_pi : norm (pi p).toAdd = 0 := by
        change Multiplicative.ofAdd (norm (pi p).toAdd) =
          Multiplicative.ofAdd 0
        apply hiota
        calc
          iota (Multiplicative.ofAdd (norm (pi p).toAdd)) = p ^ 2 :=
            (hsquare p).symm
          _ = 1 := hp
          _ = iota (Multiplicative.ofAdd 0) := by simp
      rw [hexact]
      apply MonoidHom.mem_ker.mpr
      change Multiplicative.ofAdd (pi p).toAdd = 1
      rw [(hnorm_zero_iff (pi p).toAdd).mp hnorm_pi]
      simp
  have hinduced_actions :
      ∃ inducedE : MulAut P →* AddAut E,
        (∀ alpha : MulAut P, ∀ p : P,
          Multiplicative.ofAdd (inducedE alpha (pi p).toAdd) = pi (alpha p)) ∧
        ∃ inducedF : MulAut P →* AddAut F,
          ∀ alpha : MulAut P, ∀ z : Multiplicative F,
            alpha (iota z) =
              iota (Multiplicative.ofAdd (inducedF alpha z.toAdd)) := by
    have hdescend_surjective
        {A B : Type u} [Group A] [Group B]
        (q : A →* B) (hq : Function.Surjective q)
        (hpreserved : ∀ alpha : MulAut A, ∀ x : A,
          x ∈ q.ker ↔ alpha x ∈ q.ker) :
        ∃ action : MulAut A →* MulAut B,
          ∀ alpha : MulAut A, ∀ x : A,
            action alpha (q x) = q (alpha x) := by
      have hker (alpha : MulAut A) :
          q.ker ≤ (q.comp alpha.toMonoidHom).ker := by
        intro x hx
        exact (hpreserved alpha x).mp hx
      let descendedHom (alpha : MulAut A) : B →* B :=
        MonoidHom.liftOfSurjective q hq
          ⟨q.comp alpha.toMonoidHom, hker alpha⟩
      have hdescendedHom_apply (alpha : MulAut A) (x : A) :
          descendedHom alpha (q x) = q (alpha x) := by
        simp [descendedHom, MonoidHom.liftOfSurjective]
      have hleftInverse (alpha : MulAut A) :
          Function.LeftInverse (descendedHom alpha.symm)
            (descendedHom alpha) := by
        intro y
        obtain ⟨x, rfl⟩ := hq y
        rw [hdescendedHom_apply, hdescendedHom_apply]
        simp
      have hdescended_bijective (alpha : MulAut A) :
          Function.Bijective (descendedHom alpha) :=
        ⟨(hleftInverse alpha).injective,
          (hleftInverse alpha.symm).surjective⟩
      let descendedEquiv (alpha : MulAut A) : MulAut B :=
        MulEquiv.ofBijective (descendedHom alpha)
          (hdescended_bijective alpha)
      have hdescendedEquiv_apply (alpha : MulAut A) (x : A) :
          descendedEquiv alpha (q x) = q (alpha x) := by
        rw [MulEquiv.ofBijective_apply]
        exact hdescendedHom_apply alpha x
      let action : MulAut A →* MulAut B :=
        { toFun := descendedEquiv
          map_one' := by
            apply DFunLike.ext _ _
            intro y
            obtain ⟨x, rfl⟩ := hq y
            simp [hdescendedEquiv_apply]
          map_mul' := by
            intro alpha beta
            apply DFunLike.ext _ _
            intro y
            obtain ⟨x, rfl⟩ := hq y
            simp [hdescendedEquiv_apply] }
      refine ⟨action, ?_⟩
      intro alpha x
      exact hdescendedEquiv_apply alpha x
    have hrestrict_injective
        {A B : Type u} [Group A] [Group B]
        (j : B →* A) (hj : Function.Injective j)
        (hpreserved : ∀ alpha : MulAut A, ∀ x : B,
          alpha (j x) ∈ j.range) :
        ∃ action : MulAut A →* MulAut B,
          ∀ alpha : MulAut A, ∀ x : B,
            alpha (j x) = j (action alpha x) := by
      let restrictedFun (alpha : MulAut A) (x : B) : B :=
        Classical.choose (hpreserved alpha x)
      have hrestrictedFun_apply (alpha : MulAut A) (x : B) :
          j (restrictedFun alpha x) = alpha (j x) :=
        Classical.choose_spec (hpreserved alpha x)
      let restrictedHom (alpha : MulAut A) : B →* B :=
        { toFun := restrictedFun alpha
          map_one' := by
            apply hj
            simp [hrestrictedFun_apply]
          map_mul' := by
            intro x y
            apply hj
            simp [hrestrictedFun_apply] }
      have hrestrictedHom_apply (alpha : MulAut A) (x : B) :
          j (restrictedHom alpha x) = alpha (j x) :=
        hrestrictedFun_apply alpha x
      have hleftInverse (alpha : MulAut A) :
          Function.LeftInverse (restrictedHom alpha.symm)
            (restrictedHom alpha) := by
        intro x
        apply hj
        rw [hrestrictedHom_apply, hrestrictedHom_apply]
        simp
      have hrestricted_bijective (alpha : MulAut A) :
          Function.Bijective (restrictedHom alpha) :=
        ⟨(hleftInverse alpha).injective,
          (hleftInverse alpha.symm).surjective⟩
      let restrictedEquiv (alpha : MulAut A) : MulAut B :=
        MulEquiv.ofBijective (restrictedHom alpha)
          (hrestricted_bijective alpha)
      have hrestrictedEquiv_apply (alpha : MulAut A) (x : B) :
          j (restrictedEquiv alpha x) = alpha (j x) := by
        rw [MulEquiv.ofBijective_apply]
        exact hrestrictedHom_apply alpha x
      let action : MulAut A →* MulAut B :=
        { toFun := restrictedEquiv
          map_one' := by
            apply DFunLike.ext _ _
            intro x
            apply hj
            simp [hrestrictedEquiv_apply]
          map_mul' := by
            intro alpha beta
            apply DFunLike.ext _ _
            intro x
            apply hj
            simp [hrestrictedEquiv_apply] }
      refine ⟨action, ?_⟩
      intro alpha x
      exact (hrestrictedEquiv_apply alpha x).symm
    have hpi_ker_preserved (alpha : MulAut P) (p : P) :
        p ∈ pi.ker ↔ alpha p ∈ pi.ker := by
      constructor
      · intro hp
        have hp_range : p ∈ iota.range := by
          rwa [hexact]
        rw [← hexact]
        apply (hiota_range_eq_involutions (alpha p)).mpr
        simpa using congrArg alpha
          ((hiota_range_eq_involutions p).mp hp_range)
      · intro hp
        have hp_range : alpha p ∈ iota.range := by
          rwa [hexact]
        rw [← hexact]
        apply (hiota_range_eq_involutions p).mpr
        apply alpha.injective
        simpa using (hiota_range_eq_involutions (alpha p)).mp hp_range
    have hiota_range_preserved (alpha : MulAut P)
        (z : Multiplicative F) : alpha (iota z) ∈ iota.range := by
      apply (hiota_range_eq_involutions (alpha (iota z))).mpr
      simpa using congrArg alpha
        ((hiota_range_eq_involutions (iota z)).mp ⟨z, rfl⟩)
    obtain ⟨actionE, hactionE⟩ :=
      hdescend_surjective pi hpi hpi_ker_preserved
    obtain ⟨actionF, hactionF⟩ :=
      hrestrict_injective iota hiota hiota_range_preserved
    have hconvert_actions :
        ∃ inducedE : MulAut P →* AddAut E,
          (∀ alpha : MulAut P, ∀ p : P,
            Multiplicative.ofAdd (inducedE alpha (pi p).toAdd) = pi (alpha p)) ∧
          ∃ inducedF : MulAut P →* AddAut F,
            ∀ alpha : MulAut P, ∀ z : Multiplicative F,
              alpha (iota z) =
                iota (Multiplicative.ofAdd (inducedF alpha z.toAdd)) := by
      let inducedE : MulAut P →* AddAut E :=
        (MulAutMultiplicative E).toMonoidHom.comp actionE
      let inducedF : MulAut P →* AddAut F :=
        (MulAutMultiplicative F).toMonoidHom.comp actionF
      refine ⟨inducedE, ?_, inducedF, ?_⟩
      · intro alpha p
        simpa [inducedE, MulAutMultiplicative_apply_apply] using
          hactionE alpha p
      · intro alpha z
        simpa [inducedF, MulAutMultiplicative_apply_apply] using
          hactionF alpha z
    exact hconvert_actions
  obtain ⟨induced, hinduced_pi, inducedF, hinduced_iota⟩ := hinduced_actions
  have hinduced_norm (alpha : MulAut P) (x : E) :
      inducedF alpha (norm x) = norm (induced alpha x) := by
    obtain ⟨p, hp⟩ := hpi (Multiplicative.ofAdd x)
    have hp_toAdd : (pi p).toAdd = x := congrArg Multiplicative.toAdd hp
    have hpi_alpha_toAdd :
        induced alpha x = (pi (alpha p)).toAdd := by
      have h := congrArg Multiplicative.toAdd (hinduced_pi alpha p)
      simpa [hp_toAdd] using h
    change Multiplicative.ofAdd (inducedF alpha (norm x)) =
      Multiplicative.ofAdd (norm (induced alpha x))
    apply hiota
    calc
      iota (Multiplicative.ofAdd (inducedF alpha (norm x))) =
          alpha (iota (Multiplicative.ofAdd (norm x))) :=
        (hinduced_iota alpha (Multiplicative.ofAdd (norm x))).symm
      _ = alpha (iota (Multiplicative.ofAdd (norm (pi p).toAdd))) := by
        rw [hp_toAdd]
      _ = alpha (p ^ 2) := by rw [hsquare]
      _ = (alpha p) ^ 2 := map_pow alpha p 2
      _ = iota (Multiplicative.ofAdd (norm (pi (alpha p)).toAdd)) :=
        hsquare (alpha p)
      _ = iota (Multiplicative.ofAdd (norm (induced alpha x))) := by
        rw [hpi_alpha_toAdd]
  have hnorm_surjective : Function.Surjective norm := by
    have hsquare_surjective_F :
        Function.Surjective (fun a : F => a ^ 2) := by
      apply Finite.injective_iff_surjective.mp
      intro a b hab
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hab with hab | hab
      · exact hab
      · exact hab.trans (CharTwo.neg_eq b)
    have hfixed_iff (x : E) :
        conjugation x = x ↔ ∃ a : F, algebraMap F E a = x := by
      constructor
      · intro hx
        obtain ⟨a, ha⟩ := hsquare_surjective_F (norm x)
        refine ⟨a, ?_⟩
        change a ^ 2 = norm x at ha
        have hsquares : (algebraMap F E a) ^ 2 = x ^ 2 := by
          calc
            (algebraMap F E a) ^ 2 = algebraMap F E (a ^ 2) :=
              (map_pow (algebraMap F E) a 2).symm
            _ = algebraMap F E (norm x) := by rw [ha]
            _ = x * conjugation x := hnorm x
            _ = x ^ 2 := by rw [hx, pow_two]
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with h | h
        · exact h
        · exact h.trans (CharTwo.neg_eq x)
      · rintro ⟨a, rfl⟩
        simp
    have hfinrank : Module.finrank F E = 2 := by
      have hconjugation_sq : conjugation ^ 2 = 1 := by
        rw [← hconjugation]
        exact pow_orderOf_eq_one conjugation
      have hconjugation_involutive (x : E) :
          conjugation (conjugation x) = x := by
        have h := DFunLike.congr_fun hconjugation_sq x
        exact h
      let delta : E →ₗ[F] E :=
        conjugation.toLinearMap + LinearMap.id
      have hdelta_range_le_ker : delta.range ≤ delta.ker := by
        rintro _ ⟨x, rfl⟩
        change conjugation (conjugation x + x) + (conjugation x + x) = 0
        rw [map_add, hconjugation_involutive]
        ring_nf
        simp [CharTwo.two_eq_zero]
      have hdelta_ker_eq :
          delta.ker = LinearMap.range (Algebra.linearMap F E) := by
        ext x
        constructor
        · intro hx
          change conjugation x + x = 0 at hx
          have hfixed : conjugation x = x :=
            (eq_neg_of_add_eq_zero_left hx).trans (CharTwo.neg_eq x)
          obtain ⟨a, ha⟩ := (hfixed_iff x).mp hfixed
          exact ⟨a, ha⟩
        · rintro ⟨a, rfl⟩
          change conjugation (algebraMap F E a) + algebraMap F E a = 0
          simp [CharTwo.add_self_eq_zero]
      have hdelta_ker_finrank : Module.finrank F delta.ker = 1 := by
        rw [hdelta_ker_eq,
          LinearMap.finrank_range_of_inj (algebraMap F E).injective,
          Module.finrank_self]
      have hfinrank_le : Module.finrank F E ≤ 2 := by
        have hrange_le : Module.finrank F delta.range ≤ 1 := by
          rw [← hdelta_ker_finrank]
          exact Submodule.finrank_mono hdelta_range_le_ker
        have hrank_nullity := LinearMap.finrank_range_add_finrank_ker delta
        omega
      have hfinrank_ne_one : Module.finrank F E ≠ 1 := by
        intro hdim
        have hdim_eq : Module.finrank F F = Module.finrank F E := by
          simp [hdim]
        have halgebraMap_surjective :
            Function.Surjective (Algebra.linearMap F E) :=
          (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim_eq).mp
            (algebraMap F E).injective
        have hconjugation_one : conjugation = 1 := by
          apply DFunLike.ext _ _
          intro x
          obtain ⟨a, ha⟩ := halgebraMap_surjective x
          change conjugation x = x
          rw [← ha]
          simp
        have : (2 : ℕ) = 1 := by
          calc
            2 = orderOf conjugation := hconjugation.symm
            _ = orderOf (1 : Gal(E/F)) :=
              congrArg orderOf hconjugation_one
            _ = 1 := orderOf_one
        omega
      have hfinrank_pos : 0 < Module.finrank F E := Module.finrank_pos
      omega
    have hnorm_eq_algebraNorm (x : E) : norm x = Algebra.norm F x := by
      letI : IsGalois F E := inferInstance
      have hcard_aut : Fintype.card Gal(E/F) = 2 := by
        rw [← Nat.card_eq_fintype_card,
          IsGalois.card_aut_eq_finrank F E, hfinrank]
      have hconjugation_ne_one : conjugation ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hconjugation
        omega
      have huniv : (Finset.univ : Finset Gal(E/F)) = {1, conjugation} := by
        symm
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        simp [hcard_aut, Ne.symm hconjugation_ne_one]
      apply (algebraMap F E).injective
      rw [hnorm x, Algebra.norm_eq_prod_automorphisms F x, huniv]
      rw [Finset.prod_pair (Ne.symm hconjugation_ne_one)]
      simp
    intro y
    obtain ⟨x, hx⟩ := FiniteField.norm_surjective F E y
    exact ⟨x, (hnorm_eq_algebraNorm x).trans hx⟩
  have hnorm_similitude_semilinear
      (f : AddAut E) (g : AddAut F)
      (hfg : ∀ x : E, g (norm x) = norm (f x)) :
      ∃ (lambda : Eˣ) (sigma : E ≃+* E),
        ∀ x : E, f x = (lambda : E) * sigma x := by
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    letI : Fintype (E ≃+* E) :=
      Fintype.ofInjective (fun sigma : E ≃+* E => (sigma : E → E)) (by
        intro sigma tau h
        ext x
        exact congrFun h x)
    let c : E ≃+* E := conjugation.toRingEquiv
    let twist (sigma : E ≃+* E) : E ≃+* E := sigma.trans c
    have hconjugation_sq : conjugation ^ 2 = 1 := by
      rw [← hconjugation]
      exact pow_orderOf_eq_one conjugation
    have hconjugation_involutive (x : E) :
        conjugation (conjugation x) = x := by
      have h := DFunLike.congr_fun hconjugation_sq x
      exact h
    have htwist_involutive (sigma : E ≃+* E) :
        twist (twist sigma) = sigma := by
      apply DFunLike.ext _ _
      intro x
      change conjugation (conjugation (sigma x)) = sigma x
      exact hconjugation_involutive (sigma x)
    have htwist_ne (sigma : E ≃+* E) : twist sigma ≠ sigma := by
      intro htwist
      have hconjugation_one : conjugation = 1 := by
        apply DFunLike.ext _ _
        intro x
        obtain ⟨y, rfl⟩ := sigma.surjective x
        have hy := DFunLike.congr_fun htwist y
        exact hy
      rw [hconjugation_one, orderOf_one] at hconjugation
      omega
    have hf_expansion :
        ∃ a : (E ≃+* E) → E,
          (∀ x : E, f x = ∑ sigma, a sigma * sigma x) ∧
          ∃ sigma, a sigma ≠ 0 := by
      obtain ⟨autBasis, hAutBasis⟩ :=
        lemma2a_fieldAutomorphisms_basis_linearMaps E
      let fLinear : E →ₗ[ZMod 2] E :=
        f.toAddMonoidHom.toZModLinearMap 2
      let a : (E ≃+* E) → E := autBasis.repr fLinear
      have hf_sum (x : E) :
          f x = ∑ sigma, a sigma * sigma x := by
        have hsum :
            ∑ sigma, a sigma • autBasis sigma = fLinear := by
          simpa [a] using autBasis.sum_repr fLinear
        calc
          f x = fLinear x := rfl
          _ = (∑ sigma, a sigma • autBasis sigma) x :=
            (LinearMap.congr_fun hsum x).symm
          _ = ∑ sigma, a sigma * sigma x := by
            simp [hAutBasis]
      refine ⟨a, hf_sum, ?_⟩
      by_contra! hzero
      have hf_one : f (1 : E) = 0 := by
        simpa [hzero] using hf_sum 1
      have hone_zero : (1 : E) = 0 := by
        apply f.injective
        simpa using hf_one
      exact one_ne_zero hone_zero
    obtain ⟨a, hf_expansion, sigma, hsigma⟩ := hf_expansion
    obtain ⟨quadBasis, hQuadBasis⟩ :=
      lemma2c_fieldAutomorphism_products_basis_quadraticMaps E
    let pairIndex (tau rho : E ≃+* E) :
        {s : Finset (E ≃+* E) // s.card = 1 ∨ s.card = 2} :=
      ⟨{tau, twist rho}, Finset.card_pair_eq_one_or_two⟩
    have hpairIndex_eval (tau rho : E ≃+* E) (x : E) :
        quadBasis (pairIndex tau rho) x = tau x * twist rho x := by
      rw [hQuadBasis]
      by_cases h : tau = twist rho
      · subst tau
        simp [pairIndex, pow_two]
      · simp [pairIndex, h]
    let qf : QuadraticMap (ZMod 2) E E :=
      ∑ tau, ∑ rho,
        (a tau * conjugation (a rho)) • quadBasis (pairIndex tau rho)
    have hqf_eval (x : E) :
        qf x = f x * conjugation (f x) := by
      rw [hf_expansion]
      simp [qf, hpairIndex_eval, map_sum, twist, c,
        Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro tau htau
      apply Finset.sum_congr rfl
      intro rho hrho
      ring
    have hnorm_quadratic_support :
        ∃ qnorm : QuadraticMap (ZMod 2) E E,
          (∀ x : E, qnorm x = algebraMap F E (g (norm x))) ∧
          ∀ s : {s : Finset (E ≃+* E) //
              s.card = 1 ∨ s.card = 2},
            (∀ tau : E ≃+* E, s.1 ≠ {tau, twist tau}) →
              quadBasis.repr qnorm s = 0 := by
      letI : IsScalarTower (ZMod 2) F E :=
        IsScalarTower.of_algebraMap_eq (fun z =>
          DFunLike.congr_fun
            (RingHom.ext_zmod (algebraMap (ZMod 2) E)
              ((algebraMap F E).comp (algebraMap (ZMod 2) F))) z)
      letI : Fintype (F ≃+* F) :=
        Fintype.ofInjective (fun rho : F ≃+* F => (rho : F → F)) (by
          intro rho eta h
          ext x
          exact congrFun h x)
      have hg_expansion :
          ∃ mu : (F ≃+* F) → F,
            ∀ y : F, g y = ∑ rho, mu rho * rho y := by
        obtain ⟨autBasis, hAutBasis⟩ :=
          lemma2a_fieldAutomorphisms_basis_linearMaps F
        let gLinear : F →ₗ[ZMod 2] F :=
          g.toAddMonoidHom.toZModLinearMap 2
        let mu : (F ≃+* F) → F := autBasis.repr gLinear
        refine ⟨mu, ?_⟩
        intro y
        have hsum :
            ∑ rho, mu rho • autBasis rho = gLinear := by
          simpa [mu] using autBasis.sum_repr gLinear
        calc
          g y = gLinear y := rfl
          _ = (∑ rho, mu rho • autBasis rho) y :=
            (LinearMap.congr_fun hsum y).symm
          _ = ∑ rho, mu rho * rho y := by
            simp [hAutBasis]
      obtain ⟨mu, hg_expansion⟩ := hg_expansion
      have hextend (rho : F ≃+* F) :
          ∃ sigma : E ≃+* E, ∀ y : F,
            sigma (algebraMap F E y) = algebraMap F E (rho y) := by
        let rhoAlg : F ≃ₐ[ZMod 2] F :=
          AlgEquiv.ofRingEquiv (f := rho) (by
            intro z
            exact DFunLike.congr_fun
              (RingHom.ext_zmod
                (rho.toRingHom.comp (algebraMap (ZMod 2) F))
                (algebraMap (ZMod 2) F)) z)
        obtain ⟨sigma, hsigma_restrict⟩ :=
          (AlgEquiv.restrictNormalHom_surjective
            (F := ZMod 2) (K₁ := F) E) rhoAlg
        refine ⟨sigma.toRingEquiv, ?_⟩
        intro y
        have hy := DFunLike.congr_fun hsigma_restrict y
        have hy' := congrArg (algebraMap F E) hy
        simpa [rhoAlg, AlgEquiv.restrictNormalHom] using hy'
      let extend (rho : F ≃+* F) : E ≃+* E :=
        Classical.choose (hextend rho)
      have hextend_apply (rho : F ≃+* F) (y : F) :
          extend rho (algebraMap F E y) =
            algebraMap F E (rho y) :=
        Classical.choose_spec (hextend rho) y
      have hextend_commutes (rho : F ≃+* F) (x : E) :
          extend rho (conjugation x) =
            conjugation (extend rho x) := by
        let extendAlg : E ≃ₐ[ZMod 2] E :=
          AlgEquiv.ofRingEquiv (f := extend rho) (by
            intro z
            exact DFunLike.congr_fun
              (RingHom.ext_zmod
                ((extend rho).toRingHom.comp
                  (algebraMap (ZMod 2) E))
                (algebraMap (ZMod 2) E)) z)
        let conjugationAlg : E ≃ₐ[ZMod 2] E :=
          conjugation.restrictScalars (ZMod 2)
        letI : CommGroup (E ≃ₐ[ZMod 2] E) :=
          IsCyclic.commGroup
        have hcomm : extendAlg * conjugationAlg =
            conjugationAlg * extendAlg := mul_comm _ _
        have hx := DFunLike.congr_fun hcomm x
        exact hx
      let qnorm : QuadraticMap (ZMod 2) E E :=
        ∑ rho, algebraMap F E (mu rho) •
          quadBasis (pairIndex (extend rho) (extend rho))
      have hqnorm_eval (x : E) :
          qnorm x = algebraMap F E (g (norm x)) := by
        calc
          qnorm x =
              ∑ rho, algebraMap F E (mu rho) *
                (extend rho x * conjugation (extend rho x)) := by
            simp [qnorm, hpairIndex_eval, twist, c, Algebra.smul_def]
          _ = ∑ rho, algebraMap F E (mu rho) *
                extend rho (x * conjugation x) := by
            apply Finset.sum_congr rfl
            intro rho hrho
            rw [← hextend_commutes rho x, map_mul]
          _ = ∑ rho, algebraMap F E (mu rho) *
                extend rho (algebraMap F E (norm x)) := by
            rw [hnorm]
          _ = ∑ rho, algebraMap F E (mu rho) *
                algebraMap F E (rho (norm x)) := by
            apply Finset.sum_congr rfl
            intro rho hrho
            rw [hextend_apply]
          _ = algebraMap F E
                (∑ rho, mu rho * rho (norm x)) := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro rho hrho
            rw [map_mul]
          _ = algebraMap F E (g (norm x)) := by
            rw [hg_expansion]
      have hqnorm_support
          (s : {s : Finset (E ≃+* E) //
            s.card = 1 ∨ s.card = 2})
          (hs : ∀ tau : E ≃+* E,
            s.1 ≠ {tau, twist tau}) :
          quadBasis.repr qnorm s = 0 := by
        have hne (rho : F ≃+* F) :
            pairIndex (extend rho) (extend rho) ≠ s := by
          intro h
          apply hs (extend rho)
          exact (congrArg Subtype.val h).symm
        change Finsupp.applyAddHom s
          (quadBasis.repr
            (∑ rho, (algebraMap F E (mu rho)) •
              quadBasis (pairIndex (extend rho) (extend rho)))) = 0
        rw [map_sum, map_sum]
        apply Finset.sum_eq_zero
        intro rho hrho
        change quadBasis.repr
          ((algebraMap F E (mu rho)) •
            quadBasis (pairIndex (extend rho) (extend rho))) s = 0
        rw [map_smul]
        simp [hne rho]
      exact ⟨qnorm, hqnorm_eval, hqnorm_support⟩
    obtain ⟨qnorm, hqnorm_eval, hqnorm_support⟩ :=
      hnorm_quadratic_support
    have hqf_eq_qnorm : qf = qnorm := by
      ext x
      rw [hqf_eval, hqnorm_eval, hfg, hnorm]
    have hqf_singleton_coord (tau : E ≃+* E) :
        quadBasis.repr qf
            ⟨{tau}, Or.inl (Finset.card_singleton tau)⟩ =
          a tau * conjugation (a (twist tau)) := by
      let singletonIndex :
          {s : Finset (E ≃+* E) // s.card = 1 ∨ s.card = 2} :=
        ⟨{tau}, Or.inl (Finset.card_singleton tau)⟩
      have hindex (rho eta : E ≃+* E) :
          pairIndex rho eta = singletonIndex ↔
            rho = tau ∧ eta = twist tau := by
        constructor
        · intro h
          have hset : ({rho, twist eta} : Finset (E ≃+* E)) =
              {tau} := congrArg Subtype.val h
          have hrho : rho = tau := by
            have hmem : rho ∈ ({rho, twist eta} :
                Finset (E ≃+* E)) := by simp
            rw [hset] at hmem
            simpa using hmem
          have heta_twist : twist eta = tau := by
            have hmem : twist eta ∈ ({rho, twist eta} :
                Finset (E ≃+* E)) := by simp
            rw [hset] at hmem
            simpa using hmem
          refine ⟨hrho, ?_⟩
          calc
            eta = twist (twist eta) := (htwist_involutive eta).symm
            _ = twist tau := congrArg twist heta_twist
        · rintro ⟨rfl, rfl⟩
          apply Subtype.ext
          simp [pairIndex, singletonIndex, htwist_involutive]
      change quadBasis.repr qf singletonIndex =
        a tau * conjugation (a (twist tau))
      simp [qf, Finsupp.single_apply, hindex]
      calc
        (∑ rho, ∑ eta,
            if rho = tau ∧ eta = twist tau then
              a rho * conjugation (a eta) else 0) =
            ∑ rho, if rho = tau then
              (∑ eta, if eta = twist tau then
                a rho * conjugation (a eta) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro rho hrho
          by_cases hrt : rho = tau
          · subst rho
            simp
          · simp [hrt]
        _ = ∑ eta, if eta = twist tau then
              a tau * conjugation (a eta) else 0 := by
          rw [Fintype.sum_ite_eq']
        _ = a tau * conjugation (a (twist tau)) := by
          rw [Fintype.sum_ite_eq']
    have hqf_pair_coord (tau rho : E ≃+* E)
        (hrho_ne_twist : rho ≠ twist tau) :
        quadBasis.repr qf (pairIndex tau rho) =
          a tau * conjugation (a rho) +
            a (twist rho) * conjugation (a (twist tau)) := by
      have htau_ne_twist_rho : tau ≠ twist rho := by
        intro h
        have ht := congrArg twist h
        rw [htwist_involutive] at ht
        exact hrho_ne_twist ht.symm
      have htwist_injective : Function.Injective twist :=
        Function.LeftInverse.injective htwist_involutive
      have hindex (eta zeta : E ≃+* E) :
          pairIndex eta zeta = pairIndex tau rho ↔
            (eta = tau ∧ zeta = rho) ∨
            (eta = twist rho ∧ zeta = twist tau) := by
        constructor
        · intro h
          have hset : ({eta, twist zeta} : Finset (E ≃+* E)) =
              {tau, twist rho} := congrArg Subtype.val h
          have hset' : ({eta, twist zeta} : Set (E ≃+* E)) =
              {tau, twist rho} := by
            simpa only [Finset.coe_insert, Finset.coe_singleton] using
              congrArg (fun s : Finset (E ≃+* E) =>
                (s : Set (E ≃+* E))) hset
          rcases Set.pair_eq_pair_iff.mp hset' with hdirect | hswap
          · exact Or.inl ⟨hdirect.1,
              htwist_injective hdirect.2⟩
          · refine Or.inr ⟨hswap.1, ?_⟩
            calc
              zeta = twist (twist zeta) :=
                (htwist_involutive zeta).symm
              _ = twist tau := congrArg twist hswap.2
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · rfl
          · apply Subtype.ext
            simp [pairIndex, htwist_involutive, Finset.pair_comm]
      have hsingle_sum (u v : E ≃+* E) :
          (∑ eta, ∑ zeta,
            if eta = u ∧ zeta = v then
              a eta * conjugation (a zeta) else 0) =
            a u * conjugation (a v) := by
        calc
          (∑ eta, ∑ zeta,
              if eta = u ∧ zeta = v then
                a eta * conjugation (a zeta) else 0) =
              ∑ eta, if eta = u then
                (∑ zeta, if zeta = v then
                  a eta * conjugation (a zeta) else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro eta heta
            by_cases heu : eta = u
            · subst eta
              simp
            · simp [heu]
          _ = ∑ zeta, if zeta = v then
                a u * conjugation (a zeta) else 0 := by
            rw [Fintype.sum_ite_eq']
          _ = a u * conjugation (a v) := by
            rw [Fintype.sum_ite_eq']
      have hsplit (eta zeta : E ≃+* E) :
          (if (eta = tau ∧ zeta = rho) ∨
              (eta = twist rho ∧ zeta = twist tau) then
              a eta * conjugation (a zeta) else 0) =
            (if eta = tau ∧ zeta = rho then
              a eta * conjugation (a zeta) else 0) +
            (if eta = twist rho ∧ zeta = twist tau then
              a eta * conjugation (a zeta) else 0) := by
        by_cases hfirst : eta = tau ∧ zeta = rho
        · have hsecond :
              ¬(eta = twist rho ∧ zeta = twist tau) := by
            intro hs
            exact htau_ne_twist_rho (hfirst.1.symm.trans hs.1)
          rw [if_pos (Or.inl hfirst), if_pos hfirst,
            if_neg hsecond, add_zero]
        · by_cases hsecond :
              eta = twist rho ∧ zeta = twist tau
          · rw [if_pos (Or.inr hsecond), if_neg hfirst,
              if_pos hsecond, zero_add]
          · rw [if_neg (not_or_intro hfirst hsecond),
              if_neg hfirst, if_neg hsecond, add_zero]
      simp [qf, Finsupp.single_apply, hindex]
      calc
        (∑ eta, ∑ zeta,
            if (eta = tau ∧ zeta = rho) ∨
                (eta = twist rho ∧ zeta = twist tau) then
              a eta * conjugation (a zeta) else 0) =
            (∑ eta, ∑ zeta,
              if eta = tau ∧ zeta = rho then
                a eta * conjugation (a zeta) else 0) +
            (∑ eta, ∑ zeta,
              if eta = twist rho ∧ zeta = twist tau then
                a eta * conjugation (a zeta) else 0) := by
          simp_rw [hsplit]
          simp [Finset.sum_add_distrib]
        _ = a tau * conjugation (a rho) +
              a (twist rho) * conjugation (a (twist tau)) := by
          rw [hsingle_sum, hsingle_sum]
    have hsingleton_coefficient (tau : E ≃+* E) :
        a tau * conjugation (a (twist tau)) = 0 := by
      let singletonIndex :
          {s : Finset (E ≃+* E) // s.card = 1 ∨ s.card = 2} :=
        ⟨{tau}, Or.inl (Finset.card_singleton tau)⟩
      have hnot_conjugate_pair (eta : E ≃+* E) :
          singletonIndex.1 ≠ {eta, twist eta} := by
        intro h
        have hcard := congrArg Finset.card h
        have hne : eta ≠ twist eta := Ne.symm (htwist_ne eta)
        rw [Finset.card_pair hne] at hcard
        simp [singletonIndex] at hcard
      calc
        a tau * conjugation (a (twist tau)) =
            quadBasis.repr qf singletonIndex :=
          (hqf_singleton_coord tau).symm
        _ = quadBasis.repr qnorm singletonIndex := by
          rw [hqf_eq_qnorm]
        _ = 0 := hqnorm_support singletonIndex hnot_conjugate_pair
    have hpair_coefficient (tau rho : E ≃+* E)
        (hrho_ne_tau : rho ≠ tau)
        (hrho_ne_twist : rho ≠ twist tau) :
        a tau * conjugation (a rho) +
            a (twist rho) * conjugation (a (twist tau)) = 0 := by
      have htwist_injective : Function.Injective twist :=
        Function.LeftInverse.injective htwist_involutive
      have hnot_conjugate_pair (eta : E ≃+* E) :
          (pairIndex tau rho).1 ≠ {eta, twist eta} := by
        intro h
        have hset' : ({tau, twist rho} : Set (E ≃+* E)) =
            {eta, twist eta} := by
          simpa only [pairIndex, Finset.coe_insert,
            Finset.coe_singleton] using congrArg
              (fun s : Finset (E ≃+* E) =>
                (s : Set (E ≃+* E))) h
        rcases Set.pair_eq_pair_iff.mp hset' with hdirect | hswap
        · exact hrho_ne_tau
            ((htwist_injective hdirect.2).trans hdirect.1.symm)
        · apply hrho_ne_tau
          calc
            rho = twist (twist rho) :=
              (htwist_involutive rho).symm
            _ = twist eta := congrArg twist hswap.2
            _ = tau := hswap.1.symm
      calc
        a tau * conjugation (a rho) +
              a (twist rho) * conjugation (a (twist tau)) =
            quadBasis.repr qf (pairIndex tau rho) :=
          (hqf_pair_coord tau rho hrho_ne_twist).symm
        _ = quadBasis.repr qnorm (pairIndex tau rho) := by
          rw [hqf_eq_qnorm]
        _ = 0 :=
          hqnorm_support (pairIndex tau rho) hnot_conjugate_pair
    have ha_twist : a (twist sigma) = 0 := by
      rcases mul_eq_zero.mp (hsingleton_coefficient sigma) with h | h
      · exact (hsigma h).elim
      · apply conjugation.injective
        simpa using h
    have ha_other (tau : E ≃+* E) (htau : tau ≠ sigma) :
        a tau = 0 := by
      by_cases htau_twist : tau = twist sigma
      · rw [htau_twist]
        exact ha_twist
      · have hrel :=
          hpair_coefficient sigma tau htau htau_twist
        rw [ha_twist, map_zero, mul_zero, add_zero] at hrel
        rcases mul_eq_zero.mp hrel with h | h
        · exact (hsigma h).elim
        · apply conjugation.injective
          simpa using h
    let lambda : Eˣ := Units.mk0 (a sigma) hsigma
    refine ⟨lambda, sigma, ?_⟩
    intro x
    calc
      f x = ∑ tau, a tau * tau x := hf_expansion x
      _ = ∑ tau, if tau = sigma then a sigma * sigma x else 0 := by
        apply Finset.sum_congr rfl
        intro tau htau_mem
        by_cases htau : tau = sigma
        · subst tau
          simp
        · simp [htau, ha_other tau htau]
      _ = a sigma * sigma x := by simp
      _ = (lambda : E) * sigma x := by rfl
  have hsemilinear_lifts (lambda : Eˣ) (sigma : E ≃+* E) :
      ∃ alpha : MulAut P,
        ∀ x : E, induced alpha x = (lambda : E) * sigma x := by
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    letI : IsScalarTower (ZMod 2) F E :=
      IsScalarTower.of_algebraMap_eq (fun z =>
        DFunLike.congr_fun
          (RingHom.ext_zmod (algebraMap (ZMod 2) E)
            ((algebraMap F E).comp (algebraMap (ZMod 2) F))) z)
    have hnorm_quadratic_map :
        ∃ q : QuadraticMap (ZMod 2) E F,
          ∀ x : E, q x = norm x := by
      let idLinear : E →ₗ[ZMod 2] E := LinearMap.id
      let conjugationLinear : E →ₗ[ZMod 2] E :=
        conjugation.toLinearMap.restrictScalars (ZMod 2)
      let qE : QuadraticMap (ZMod 2) E E :=
        LinearMap.BilinMap.toQuadraticMap
          (idLinear.smulRight conjugationLinear)
      obtain ⟨retract, hretract⟩ :=
        LinearMap.exists_leftInverse_of_injective
          (Algebra.linearMap F E)
          (LinearMap.ker_eq_bot.mpr (algebraMap F E).injective)
      have hretract_apply (y : F) :
          retract (algebraMap F E y) = y := by
        have h := LinearMap.congr_fun hretract y
        simpa using h
      let retractZMod : E →ₗ[ZMod 2] F :=
        retract.restrictScalars (ZMod 2)
      let q : QuadraticMap (ZMod 2) E F :=
        retractZMod.compQuadraticMap qE
      refine ⟨q, ?_⟩
      intro x
      change retract (x * conjugation x) = norm x
      rw [← hnorm x]
      exact hretract_apply (norm x)
    obtain ⟨q, hq_eval⟩ := hnorm_quadratic_map
    have hsigma_restrict :
        ∃ rho : F ≃+* F, ∀ y : F,
          sigma (algebraMap F E y) = algebraMap F E (rho y) := by
      let sigmaAlg : E ≃ₐ[ZMod 2] E :=
        AlgEquiv.ofRingEquiv (f := sigma) (by
          intro z
          exact DFunLike.congr_fun
            (RingHom.ext_zmod
              (sigma.toRingHom.comp (algebraMap (ZMod 2) E))
              (algebraMap (ZMod 2) E)) z)
      let rhoAlg : F ≃ₐ[ZMod 2] F :=
        AlgEquiv.restrictNormalHom F sigmaAlg
      refine ⟨rhoAlg.toRingEquiv, ?_⟩
      intro y
      change sigma (algebraMap F E y) =
        algebraMap F E (rhoAlg y)
      simp [rhoAlg, sigmaAlg, AlgEquiv.restrictNormalHom]
    obtain ⟨rho, hrho_apply⟩ := hsigma_restrict
    have hsigma_commutes (x : E) :
        sigma (conjugation x) = conjugation (sigma x) := by
      let sigmaAlg : E ≃ₐ[ZMod 2] E :=
        AlgEquiv.ofRingEquiv (f := sigma) (by
          intro z
          exact DFunLike.congr_fun
            (RingHom.ext_zmod
              (sigma.toRingHom.comp (algebraMap (ZMod 2) E))
              (algebraMap (ZMod 2) E)) z)
      let conjugationAlg : E ≃ₐ[ZMod 2] E :=
        conjugation.restrictScalars (ZMod 2)
      letI : CommGroup (E ≃ₐ[ZMod 2] E) :=
        IsCyclic.commGroup
      have hcomm : sigmaAlg * conjugationAlg =
          conjugationAlg * sigmaAlg := mul_comm _ _
      have hx := DFunLike.congr_fun hcomm x
      exact hx
    have hnorm_semilinear (x : E) :
        norm ((lambda : E) * sigma x) =
          norm (lambda : E) * rho (norm x) := by
      apply (algebraMap F E).injective
      calc
        algebraMap F E
            (norm ((lambda : E) * sigma x)) =
            ((lambda : E) * sigma x) *
              conjugation ((lambda : E) * sigma x) :=
          hnorm _
        _ = ((lambda : E) * conjugation (lambda : E)) *
              sigma (x * conjugation x) := by
          rw [map_mul, ← hsigma_commutes x, map_mul]
          ring
        _ = algebraMap F E (norm (lambda : E)) *
              sigma (algebraMap F E (norm x)) := by
          rw [hnorm, hnorm]
        _ = algebraMap F E (norm (lambda : E)) *
              algebraMap F E (rho (norm x)) := by
          rw [hrho_apply]
        _ = algebraMap F E
              (norm (lambda : E) * rho (norm x)) := by
          rw [map_mul]
    have hnorm_lambda_ne : norm (lambda : E) ≠ 0 := by
      intro h
      exact Units.ne_zero lambda ((hnorm_zero_iff _).mp h)
    let normUnit : Fˣ :=
      Units.mk0 (norm (lambda : E)) hnorm_lambda_ne
    have hlinear_equivs :
        ∃ fLinear : E ≃ₗ[ZMod 2] E,
          ∃ gLinear : F ≃ₗ[ZMod 2] F,
            (∀ x : E, fLinear x = (lambda : E) * sigma x) ∧
            ∀ y : F, gLinear y =
              norm (lambda : E) * rho y := by
      let fAdd : AddAut E :=
        sigma.toAddEquiv.trans
          (DistribMulAction.toAddEquiv E lambda)
      let gAdd : AddAut F :=
        rho.toAddEquiv.trans
          (DistribMulAction.toAddEquiv F normUnit)
      let fMap : E →ₗ[ZMod 2] E :=
        fAdd.toAddMonoidHom.toZModLinearMap 2
      let gMap : F →ₗ[ZMod 2] F :=
        gAdd.toAddMonoidHom.toZModLinearMap 2
      let fLinear : E ≃ₗ[ZMod 2] E :=
        LinearEquiv.ofBijective fMap fAdd.bijective
      let gLinear : F ≃ₗ[ZMod 2] F :=
        LinearEquiv.ofBijective gMap gAdd.bijective
      refine ⟨fLinear, gLinear, ?_, ?_⟩
      · intro x
        simp [fLinear, fMap, fAdd,
          DistribMulAction.toAddEquiv_apply, Units.smul_def, smul_eq_mul]
      · intro y
        simp [gLinear, gMap, gAdd, normUnit,
          DistribMulAction.toAddEquiv_apply, Units.smul_def, smul_eq_mul]
    obtain ⟨fLinear, gLinear, hfLinear, hgLinear⟩ :=
      hlinear_equivs
    have hq_compatible (x : E) :
        gLinear (q x) = q (fLinear x) := by
      rw [hfLinear, hgLinear, hq_eval, hq_eval,
        hnorm_semilinear]
    obtain ⟨e, he_pi, he_iota⟩ :=
      (lemma1c_central_extensions_equivalent_iff
        iota pi iota pi q q
        hiota hpi hexact hcentral
        hiota hpi hexact hcentral
        (fun p => by rw [hq_eval]; exact (hsquare p).symm)
        (fun p => by rw [hq_eval]; exact (hsquare p).symm)
        fLinear gLinear).2 hq_compatible
    refine ⟨e, ?_⟩
    intro x
    obtain ⟨p, hp⟩ := hpi (Multiplicative.ofAdd x)
    have hp_toAdd : (pi p).toAdd = x :=
      congrArg Multiplicative.toAdd hp
    have hinduced_toAdd :
        induced e x = (pi (e p)).toAdd := by
      have h := congrArg Multiplicative.toAdd (hinduced_pi e p)
      simpa [hp_toAdd] using h
    calc
      induced e x = (pi (e p)).toAdd := hinduced_toAdd
      _ = fLinear (pi p).toAdd := he_pi p
      _ = (lambda : E) * sigma x := by
        rw [hfLinear, hp_toAdd]
  have himage (f : AddAut E) : f ∈ induced.range ↔
      ∃ (lambda : Eˣ) (sigma : E ≃+* E),
        ∀ x : E, f x = (lambda : E) * sigma x := by
    constructor
    · rintro ⟨alpha, rfl⟩
      exact hnorm_similitude_semilinear (induced alpha) (inducedF alpha)
        (hinduced_norm alpha)
    · rintro ⟨lambda, sigma, hf⟩
      obtain ⟨alpha, halpha⟩ := hsemilinear_lifts lambda sigma
      refine ⟨alpha, ?_⟩
      ext x
      exact (halpha x).trans (hf x).symm
  have hinducedF_eq_one_of_mem_ker (alpha : induced.ker) :
      inducedF alpha.1 = 1 := by
    apply DFunLike.ext _ _
    intro y
    obtain ⟨x, rfl⟩ := hnorm_surjective y
    have halpha : induced alpha.1 = 1 :=
      MonoidHom.mem_ker.mp alpha.2
    rw [hinduced_norm, halpha]
    simp
  letI : Algebra (ZMod 2) E := ZMod.algebra E 2
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨encode, hencode_injective, hencode_zero, hencode_add,
      hencode_pi, hencode_iota, hencode_unique⟩ :=
    lemma1d_extension_kernel_automorphisms
      iota pi hiota hpi hexact hcentral
  have hkernel_fixes_pi (alpha : induced.ker) (p : P) :
      pi (alpha.1 p) = pi p := by
    have halpha : induced alpha.1 = 1 :=
      MonoidHom.mem_ker.mp alpha.2
    have h := hinduced_pi alpha.1 p
    rw [halpha] at h
    simpa using h.symm
  have hkernel_fixes_iota (alpha : induced.ker)
      (z : Multiplicative F) :
      alpha.1 (iota z) = iota z := by
    have h := hinduced_iota alpha.1 z
    rw [hinducedF_eq_one_of_mem_ker alpha] at h
    simpa using h
  have hkernel_encoded (alpha : induced.ker) :
      ∃ f : E →ₗ[ZMod 2] F, encode f = alpha.1 :=
    (hencode_unique alpha.1
      (hkernel_fixes_pi alpha)
      (hkernel_fixes_iota alpha)).exists
  have hkernel_commutative : IsMulCommutative induced.ker := by
    constructor
    constructor
    intro alpha beta
    obtain ⟨f, hf⟩ := hkernel_encoded alpha
    obtain ⟨g, hg⟩ := hkernel_encoded beta
    apply Subtype.ext
    change alpha.1 * beta.1 = beta.1 * alpha.1
    calc
      alpha.1 * beta.1 = encode f * encode g := by
        rw [hf, hg]
      _ = encode (f + g) := (hencode_add f g).symm
      _ = encode (g + f) := by rw [add_comm]
      _ = encode g * encode f := hencode_add g f
      _ = beta.1 * alpha.1 := by rw [hf, hg]
  have hkernel_exponent_two : ∀ alpha : induced.ker, alpha ^ 2 = 1 := by
    intro alpha
    obtain ⟨f, hf⟩ := hkernel_encoded alpha
    apply Subtype.ext
    change alpha.1 ^ 2 = 1
    calc
      alpha.1 ^ 2 = encode f * encode f := by
        rw [pow_two, hf]
      _ = encode (f + f) := (hencode_add f f).symm
      _ = encode 0 := by rw [ZModModule.add_self]
      _ = 1 := hencode_zero
  exact ⟨induced, hinduced_pi, himage, hkernel_commutative,
    hkernel_exponent_two⟩

end PFAppendixIII
end BenderSuzuki


