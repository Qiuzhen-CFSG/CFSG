module
public import Theory.Representation.Suzuki.LinearLifts
public import Theory.Representation.BinaryOffender.PerfectNormalizer
public import Theory.Representation.FiniteFieldSemilinearDisplacement
public import Theory.Representation.SemilinearFixedPointCentralizer
public import Theory.SpecificGroups.Suzuki.OddTorusContainment
public import Theory.Representation.NonsplitFour
public import Theory.SpecificGroups.Suzuki.TwoRank

/-!
# Odd-prime displacement in the full Suzuki linear normalizer

Every odd-prime-order actor in the binary linear normalizer of the natural
Suzuki module moves at least two thirds of its dimension. Binary Schur's
lemma and the actual automorphism decomposition express a normalizer actor
as a scalar times an inner and a field operator. A nontrivial field part
has the required semilinear displacement. For a scalar-inner actor, the
split torus has four distinct weights, while a nonsplit torus has no
one-dimensional invariant subspace over the defining field. These yield
the stronger three-quarter displacement bound in the remaining case.

This is the model estimate used for the beta column in Table 7.2.1 and
source 7.4.1, through the literal chosen-module automizer marking.
Source: Aschbacher--Smith, H.0.1 and H.3, printed pp.377--379.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Representation.BinaryOffender
namespace Representation.SuzukiNatural
open SuzukiSmallDegree

private theorem intertwiner_scalar_inner_field (m : ℕ) (hm : 1 ≤ m)
    (α : MulAut (SuzukiMatrixGroup m)) (E : W m ≃ₗ[ZMod 2] W m)
    (he : ∀ g v, E (natural m g v) = natural m (α g) (E v)) :
    ∃ (g : SuzukiMatrixGroup m) (s : F m ≃ₐ[ZMod 2] F m) (c : F m),
      c ≠ 0 ∧ α = MulAut.conj g * suzukiFieldAut m s ∧
      ∀ v, E v = c • natural m g (fieldCoordinates m s v) := by
  obtain ⟨g,s,hs⟩ := suzukiAut_eq_inner_mul_field m hm α
  let D := (innerFieldEquiv m g s).toLinearEquiv
  have hD (x : SuzukiMatrixGroup m) (v : W m) :
      D (natural m x v) = natural m (α x) (D v) := by
    have hh := LinearMap.congr_fun ((innerFieldEquiv m g s).isIntertwining' x) v
    change D (natural m x v) = natural m ((MulAut.conj g * suzukiFieldAut m s) x) (D v) at hh
    rwa [←hs] at hh
  let f : W m →+ W m := E.symm.toAddEquiv.toAddMonoidHom.comp D.toAddEquiv.toAddMonoidHom
  have hf (x : SuzukiMatrixGroup m) (v : W m) :
      f (natural m x v) = natural m x (f v) := by
    apply E.injective
    change E (E.symm (D (natural m x v))) = E (natural m x (E.symm (D v)))
    rw [E.apply_symm_apply,he,E.apply_symm_apply,hD]
  obtain ⟨a,ha⟩ := commuting_addHom_eq_scalar m f hf
  have ha0 : a ≠ 0 := by
    intro hz
    obtain ⟨v,hv⟩ := exists_ne (0 : W m)
    have hf0 : f v = f 0 := by rw [ha,ha,hz]; simp
    exact hv (D.injective (E.symm.injective hf0))
  have hDv (v : W m) : D v = E (a • v) := by
    have hh := congrArg E (ha v)
    change E (E.symm (D v)) = _ at hh
    rwa [E.apply_symm_apply] at hh
  have hsem (b : F m) (v : W m) : D (b • v) = s b • D v := by
    change natural m g (fieldCoordinates m s (b • v)) =
      s b • natural m g (fieldCoordinates m s v)
    have hh : fieldCoordinates m s (b • v) = s b • fieldCoordinates m s v := by
      ext i
      exact s.map_mul b (v i)
    rw [hh]
    exact (naturalField m g).map_smul (s b) _
  refine ⟨g,s,s a⁻¹,(map_ne_zero s).mpr (inv_ne_zero ha0),hs,?_⟩
  intro v
  calc
    E v = D (a⁻¹ • v) := by rw [hDv, smul_smul, mul_inv_cancel₀ ha0, one_smul]
    _ = s a⁻¹ • D v := hsem _ _

private theorem natural_faithful (m : ℕ) : Function.Injective (natural m) := by
  intro x y h
  apply (SuzukiMatrixSubgroup m).subtype_injective
  apply generalLinearNatural_injective 4
  apply LinearMap.ext
  intro v
  exact LinearMap.congr_fun h v

private def normalizerAut (m : ℕ) :
    linearNormalizer (natural m) →* MulAut (SuzukiMatrixGroup m) :=
  (MulAut.congr (PerfectNormalizer.imageEquiv (natural m) (natural_faithful m)).symm).toMonoidHom.comp
    (actionImage (natural m)).normalizerMonoidHom

private def operator (m : ℕ) (a : linearNormalizer (natural m)) : W m ≃ₗ[ZMod 2] W m :=
  LinearEquiv.ofLinearMap a.val.val a.val.inv a.val.val_inv a.val.inv_val

private theorem normalizer_intertwines (m : ℕ) (a : linearNormalizer (natural m))
    (g : SuzukiMatrixGroup m) (v : W m) :
    operator m a (natural m g v) = natural m (normalizerAut m a g) (operator m a v) := by
  let e := PerfectNormalizer.imageEquiv (natural m) (natural_faithful m)
  have hh : (natural m).asGroupHom (normalizerAut m a g) =
      a.val * (natural m).asGroupHom g * a.val⁻¹ := by
    have he := e.apply_symm_apply ((actionImage (natural m)).normalizerMonoidHom a (e g))
    exact congrArg Subtype.val he
  have he := congrArg (fun u : (Module.End (ZMod 2) (W m))ˣ => u.val (operator m a v)) hh
  change _ = a.val.val ((natural m g) (a.val.inv (a.val.val v))) at he
  rw [show a.val.inv (a.val.val v) = v from (operator m a).symm_apply_apply v] at he
  exact he.symm

private theorem normalizer_scalar_inner_field (m : ℕ) (hm : 1 ≤ m)
    (a : linearNormalizer (natural m)) :
    ∃ (g : SuzukiMatrixGroup m) (s : F m ≃ₐ[ZMod 2] F m) (c : F m),
      c ≠ 0 ∧ ∀ v, normalizerRepresentation (natural m) a v =
        c • natural m g (fieldCoordinates m s v) := by
  obtain ⟨g,s,c,hc,_,he⟩ := intertwiner_scalar_inner_field m hm (normalizerAut m a) (operator m a)
    (normalizer_intertwines m a)
  exact ⟨g,s,c,hc,he⟩

private theorem normalizer_semilinear (m : ℕ) (hm : 1 ≤ m)
    (a : linearNormalizer (natural m)) :
    ∃ s : F m ≃+* F m, ∀ c v,
      normalizerRepresentation (natural m) a (c • v) =
        s c • normalizerRepresentation (natural m) a v := by
  obtain ⟨g,s,c,_,he⟩ := normalizer_scalar_inner_field m hm a
  refine ⟨s.toRingEquiv,?_⟩
  intro b v
  rw [he,he]
  have hh : fieldCoordinates m s (b • v) = s b • fieldCoordinates m s v := by
    ext i
    exact s.map_mul b (v i)
  rw [hh]
  change c • naturalField m g (s b • _) = s b • c • naturalField m g _
  rw [(naturalField m g).map_smul, smul_comm]

private def normalizerCoefficient (m : ℕ) (hm : 1 ≤ m) :
    linearNormalizer (natural m) →* (F m ≃+* F m) :=
  SemilinearFixedPointCentralizer.coefficient (normalizerRepresentation (natural m))
    (normalizer_semilinear m hm)

private theorem normalizerCoefficient_smul (m : ℕ) (hm : 1 ≤ m)
    (a : linearNormalizer (natural m)) (c : F m) (v : W m) :
    normalizerRepresentation (natural m) a (c • v) =
      normalizerCoefficient m hm a c • normalizerRepresentation (natural m) a v :=
  SemilinearFixedPointCentralizer.coefficient_smul _ _ _ _ _

private theorem normalizer_field_displacement (m : ℕ) (hm : 1 ≤ m)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (a : linearNormalizer (natural m)) (ha : orderOf a = p)
    (hn : normalizerCoefficient m hm a ≠ 1) :
    8 * (2 * m + 1) ≤ 3 * fixedCodim (normalizerRepresentation (natural m)) (zpowers a) := by
  have hd : orderOf (normalizerCoefficient m hm a) ∣ p :=
    ha ▸ orderOf_map_dvd (normalizerCoefficient m hm) a
  have hs : orderOf (normalizerCoefficient m hm a) = p :=
    ((Nat.dvd_prime hp).mp hd).resolve_left (fun h => hn (orderOf_eq_one_iff.mp h))
  have hb := FiniteFieldSemilinearDisplacement.two_thirds_le_fixedCodim
    (normalizerRepresentation (natural m)) hp ho a ha (normalizerCoefficient m hm a) hs
    (normalizerCoefficient_smul m hm a)
  have hF : Module.finrank (ZMod 2) (F m) = 2 * m + 1 :=
    GaloisField.finrank 2 (by omega)
  have hW : Module.finrank (F m) (W m) = 4 := by simp [W]
  rw [hF,hW] at hb
  omega

private theorem normalizer_small_displacement_scalar_inner (m : ℕ) (hm : 1 ≤ m)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (a : linearNormalizer (natural m)) (ha : orderOf a = p)
    (hsmall : 3 * fixedCodim (normalizerRepresentation (natural m)) (zpowers a) <
      8 * (2 * m + 1)) :
    ∃ (g : SuzukiMatrixGroup m) (c : F m), c ≠ 0 ∧ Odd (orderOf g) ∧
      ∀ v, normalizerRepresentation (natural m) a v = c • natural m g v := by
  have hc : normalizerCoefficient m hm a = 1 := by
    by_contra hn
    exact (not_lt_of_ge (normalizer_field_displacement m hm hp ho a ha hn)) hsmall
  obtain ⟨g,s,c,hc0,hα,he⟩ := intertwiner_scalar_inner_field m hm
    (normalizerAut m a) (operator m a) (normalizer_intertwines m a)
  change ∀ v, normalizerRepresentation (natural m) a v =
    c • natural m g (fieldCoordinates m s v) at he
  have hs : s.toRingEquiv = normalizerCoefficient m hm a := by
    apply SemilinearFixedPointCentralizer.coefficient_unique
      (normalizerRepresentation (natural m)) a ?_ (normalizerCoefficient_smul m hm a)
    intro b v
    rw [he,he]
    have hh : fieldCoordinates m s (b • v) = s b • fieldCoordinates m s v := by
      ext i
      exact s.map_mul b (v i)
    rw [hh]
    change c • naturalField m g (s b • _) = s b • c • naturalField m g _
    rw [(naturalField m g).map_smul,smul_comm]
  have hs1 : s = 1 := by
    ext b
    exact DFunLike.congr_fun (hs.trans hc) b
  have hmodel : BenderSuzuki.IsSimpleBenderGroup (SuzukiMatrixGroup m) :=
    .isSuzuki ⟨m,hm,⟨MulEquiv.refl _⟩⟩
  let := hmodel.isSimple
  have hcenter : center (SuzukiMatrixGroup m)=⊥ := by
    rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact False.elim (hmodel.not_commutative (fun x y => by
        have hx : x ∈ center (SuzukiMatrixGroup m) := by rw [ht]; trivial
        exact (mem_center_iff.mp hx y).symm))
  have hα' : normalizerAut m a=MulAut.conj g := by
    rw [hα,hs1,←suzukiFieldAutHom_apply,map_one,mul_one]
  have hgp : g^p=1 := by
    apply MulAut.conj_injective_of_center_eq_bot hcenter
    rw [map_pow,map_one,←hα',←map_pow,←ha,pow_orderOf_eq_one,map_one]
  refine ⟨g,c,hc0,ho.of_dvd_nat (orderOf_dvd_of_pow_eq_one hgp),?_⟩
  intro v
  rw [he,hs1]
  rfl

end Representation.SuzukiNatural

namespace Representation.SuzukiNatural
open SuzukiSmallDegree BenderSuzuki PFAppendixIII

private theorem pow_card_field (m : ℕ) (x : F m) : x ^ (2 ^ (2*m+1)) = x := by
  let : Fintype (F m) := Fintype.ofFinite _
  have hc : Fintype.card (F m) = 2^(2*m+1) := by
    rw [←Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (2*m+1) (by omega)
  simpa only [hc] using FiniteField.pow_card x

private theorem pow_half_add_one (m : ℕ) (x : F m) (hx : x ≠ 0)
    (he : x ^ (1+2^m) = 1) : x = 1 := by
  have hpow : x ^ (2^m) = x⁻¹ := by
    rw [pow_add,pow_one] at he
    calc
      _ = x⁻¹ * (x * x^(2^m)) := by rw [←mul_assoc,inv_mul_cancel₀ hx,one_mul]
      _ = x⁻¹ := by rw [he,mul_one]
  have heq : x ^ (2^(2*m)) = x := by
    calc
      _ = (x^(2^m))^(2^m) := by rw [←pow_mul,←pow_add]; congr 2; omega
      _ = x := by rw [hpow,inv_pow,hpow,inv_inv]
  have hs : x^2 = x := by
    calc
      _ = (x^(2^(2*m)))^2 := by rw [heq]
      _ = x^(2^(2*m+1)) := by
        rw [pow_succ (2 : ℕ) (2*m)]
        exact (pow_mul x (2^(2*m)) 2).symm
      _ = x := pow_card_field m x
  have hh : x*(x-1)=0 := by linear_combination hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hx)

private theorem pow_tits_add_one (m : ℕ) (x : F m) (hx : x ≠ 0)
    (he : x ^ (1+2^(m+1)) = 1) : x = 1 := by
  have hpow : x ^ (2^(m+1)) = x⁻¹ := by
    rw [pow_add,pow_one] at he
    calc
      _ = x⁻¹ * (x * x^(2^(m+1))) := by rw [←mul_assoc,inv_mul_cancel₀ hx,one_mul]
      _ = x⁻¹ := by rw [he,mul_one]
  have heq : x ^ (2^(2*m+2)) = x := by
    calc
      _ = (x^(2^(m+1)))^(2^(m+1)) := by rw [←pow_mul,←pow_add]; congr 2; omega
      _ = x := by rw [hpow,inv_pow,hpow,inv_inv]
  have hs : x^2 = x := by
    rw [show 2*m+2=(2*m+1)+1 by omega,pow_succ,pow_mul,pow_card_field] at heq
    exact heq
  have hh : x*(x-1)=0 := by linear_combination hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hx)

private theorem square_one (m : ℕ) {x : F m} (hx : x^2=1) : x=1 := by
  have hh : (x-1)^2=0 := by
    calc
      _ = x^2 + 1 := by rw [CharTwo.sub_eq_add,CharTwo.add_sq,pow_two (1 : F m),one_mul]
      _ = 0 := by rw [hx]; exact CharTwo.add_self_eq_zero 1
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hh)

private def torusWeights (m : ℕ) (u : (F m)ˣ) : Fin 4 → F m :=
  ![(u : F m)^(1+2^m),(u : F m)^(2^m),((u : F m)^(2^m))⁻¹,
    ((u : F m)^(1+2^m))⁻¹]

private theorem torusWeights_injective (m : ℕ) (u : (F m)ˣ) (hu : u ≠ 1) :
    Function.Injective (torusWeights m u) := by
  have hu1 : (u : F m) ≠ 1 := fun h => hu (Units.ext h)
  let x : F m := u
  let a := x^(1+2^m)
  let b := x^(2^m)
  have hx : x ≠ 0 := u.ne_zero
  have ha : a ≠ 0 := pow_ne_zero _ hx
  have hb : b ≠ 0 := pow_ne_zero _ hx
  have hab : a ≠ b := by
    intro h
    have he : x*b=1*b := by simpa [a,b,pow_add] using h
    exact hu1 (mul_right_cancel₀ hb he)
  have habi : a ≠ b⁻¹ := by
    intro h
    have he : x^(1+2^(m+1))=1 := by
      calc
        _ = a*b := by dsimp [a,b]; rw [←pow_add,pow_succ]; congr 1; omega
        _ = 1 := by rw [h,inv_mul_cancel₀ hb]
    exact hu1 (pow_tits_add_one m x hx he)
  have hai : a ≠ a⁻¹ := by
    intro h
    have he : a^2=1 := by rw [pow_two]; nth_rw 1 [h]; exact inv_mul_cancel₀ ha
    exact hu1 (pow_half_add_one m x hx (square_one m he))
  have hbi : b ≠ b⁻¹ := by
    intro h
    have he : b^2=1 := by rw [pow_two]; nth_rw 1 [h]; exact inv_mul_cancel₀ hb
    have hh : x^(2^m)=1^(2^m) := by simpa only [one_pow] using square_one m he
    exact hu1 ((iterateFrobenius_inj (F m) 2 m) hh)
  have hiab : a⁻¹ ≠ b := fun he => habi (by simpa using congrArg Inv.inv he)
  change Function.Injective ![a,b,b⁻¹,a⁻¹]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem diagonal_fixed_finrank_le (m : ℕ) {X : Type*} [Group X]
    (ρ : Representation (ZMod 2) X (W m))
    (a : X) (c : F m) (hc : c ≠ 0)
    (w : Fin 4 → F m) (hw : Function.Injective w)
    (he : ∀ v i, ρ a v i = c * w i * v i) :
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers a)) ≤ 2*m+1 := by
  classical
  let U := fixedSpace ρ (zpowers a)
  have hv (v : U) (i : Fin 4) : (c*w i-1)*v.val i=0 := by
    have hh := congrFun (v.property ⟨a,mem_zpowers a⟩) i
    change ρ a v.val i = v.val i at hh
    rw [he] at hh
    linear_combination hh
  have atMostOne {i j : Fin 4} (hi : c*w i=1) (hj : c*w j=1) : i=j :=
    hw (mul_left_cancel₀ hc (hi.trans hj.symm))
  by_cases hex : ∃ i, c*w i=1
  · obtain ⟨i,hi⟩ := hex
    let ev : U →ₗ[ZMod 2] F m := (LinearMap.proj i).comp U.subtype
    have hinj : Function.Injective ev := by
      intro v z hvz
      apply Subtype.ext
      funext j
      by_cases hj : j=i
      · subst j; exact hvz
      · have hne : c*w j-1 ≠ 0 := fun hz => hj (atMostOne (sub_eq_zero.mp hz) hi)
        have hv0 := (mul_eq_zero.mp (hv v j)).resolve_left hne
        have hz0 := (mul_eq_zero.mp (hv z j)).resolve_left hne
        exact hv0.trans hz0.symm
    have hd := LinearMap.finrank_le_finrank_of_injective (f := ev) hinj
    simpa only [GaloisField.finrank 2 (by omega : 2*m+1 ≠ 0)] using hd
  · have hU : U=⊥ := by
      apply le_bot_iff.mp
      intro v hvU
      change v=0
      ext i
      exact (mul_eq_zero.mp (hv ⟨v,hvU⟩ i)).resolve_left
        (fun hh => hex ⟨i,sub_eq_zero.mp hh⟩)
    change Module.finrank (ZMod 2) U ≤ _
    rw [hU,finrank_bot]
    omega

private theorem natural_nonsplit_no_eigenvector (m : ℕ)
    (g : SuzukiMatrixGroup m) (hg : g ≠ 1)
    (hd : orderOf g ∣ (2^(2*m+1))^2+1)
    (c : F m) (v : W m) (hv : natural m g v = c • v) : v=0 := by
  classical
  by_contra hv0
  let : Fintype (F m) := Fintype.ofFinite _
  let A := zpowers g
  have hA : A ≠ ⊥ := fun hh => hg (mem_bot.mp (hh ▸ mem_zpowers g))
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA
  let μ := (naturalField m).comp A.subtype
  let U := Submodule.span (F m) {v}
  have hfaith : Function.Injective μ :=
    ((generalLinearNatural_injective 4).comp (SuzukiMatrixSubgroup m).subtype_injective).comp
      A.subtype_injective
  have hcard : Fintype.card (F m) = 2^(2*m+1) := by
    rw [←Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (2*m+1) (by omega)
  have hinv : ∀ x : A, ∀ z ∈ U, μ x z ∈ U := by
    rintro x z hz
    obtain ⟨k,hk⟩ := mem_powers_iff_mem_zpowers.mpr x.property
    obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hz
    change naturalField m x.val (b • v) ∈ U
    rw [←hk,map_smul]
    apply Submodule.smul_mem
    have hkv : naturalField m (g^k) v = c^k • v := by
      clear hk
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ',map_mul,Module.End.mul_apply,ih,map_smul]
        change c^k • natural m g v = _
        rw [hv,smul_smul,pow_succ]
    rw [hkv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
  have he := invariant_eq_bot_or_top_of_card_dvd_sq_add_one μ hfaith (by simp [W])
    (by simpa only [A,Nat.card_zpowers,hcard] using hd)
    Fintype.one_lt_card (by rw [hcard]; exact even_two.pow_of_ne_zero (by omega)) U hinv
  rcases he with hbot | htop
  · have hmem : v ∈ U := Submodule.subset_span (Set.mem_singleton v)
    rw [hbot] at hmem
    exact hv0 hmem
  · have hf := finrank_span_singleton (K := F m) hv0
    change Module.finrank (F m) U=1 at hf
    rw [htop,finrank_top] at hf
    simp [W] at hf

private theorem scalar_odd_fixedCodim (m : ℕ) (hm : 1 ≤ m)
    {X : Type*} [Group X] (τ : Representation (ZMod 2) X (W m)) (a : X)
    (ha : a ≠ 1) (hf : Function.Injective τ)
    (g : SuzukiMatrixGroup m) (ho : Odd (orderOf g))
    (c : F m) (hc : c ≠ 0) (he : ∀ v, τ a v = c • natural m g v) :
    3*(2*m+1) ≤ fixedCodim τ (zpowers a) := by
  by_cases hg : g=1
  · have hc1 : c ≠ 1 := by
      intro hc1
      apply ha
      apply hf
      apply LinearMap.ext
      intro v
      simp [he,hg,hc1]
    have hfix : fixedSpace τ (zpowers a)=⊥ := by
      apply le_bot_iff.mp
      intro v hv
      change v=0
      have hh : τ a v=v := hv ⟨a,mem_zpowers a⟩
      rw [he,hg,map_one,Module.End.one_apply] at hh
      have hz : (c-1) • v=0 := by rw [sub_smul,one_smul,hh,sub_self]
      exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc1)
    have hh := fixedCodim_add_finrank τ (zpowers a)
    rw [hfix,finrank_bot,natural_finrank] at hh
    omega
  obtain ⟨U,hU,hu⟩ := suzukiOddSubgroup_exists_torus (by omega : 0<m) (zpowers g)
    (by simpa only [Nat.card_zpowers] using ho)
  rcases hu with ⟨h,rfl⟩ | hnonsplit
  · obtain ⟨t,ht,hg'⟩ := hU (mem_zpowers g)
    have htne : t ≠ 1 := by intro ht1; apply hg; rw [←hg',ht1,map_one]
    obtain ⟨u,hu⟩ := (mem_suzukiSplitTorus_iff m t).mp ht
    have hu1 : u ≠ 1 := by
      intro hu1
      apply htne
      apply Subtype.ext
      rw [hu,hu1]
      exact External.suzukiTorusGL_one m
    let E := matrixCoordinates m h⁻¹
    let τ' : Representation (ZMod 2) X (W m) := E.conjRingEquiv.toMonoidHom.comp τ
    have heq : ∀ x v, E (τ x v)=τ' x (E v) := by
      intro x v
      change _ = E (τ x (E.symm (E v)))
      rw [E.symm_apply_apply]
    have haction (v : W m) : τ' a v = c • natural m t v := by
      change natural m h⁻¹ (τ a (E.symm v)) = _
      rw [he]
      change naturalField m h⁻¹ (c • natural m g (E.symm v)) = _
      rw [map_smul]
      change c • natural m h⁻¹ (natural m g (E.symm v)) = _
      rw [←Module.End.mul_apply,←map_mul]
      have hEq : E.symm v=natural m h v := by
        change natural m (h⁻¹)⁻¹ v=natural m h v
        rw [inv_inv]
      rw [hEq,←Module.End.mul_apply,←map_mul]
      have hconj : h⁻¹*g*h=t := by
        change h*t*h⁻¹=g at hg'
        rw [←hg']; group
      rw [hconj]
    have hdiag (v : W m) (i : Fin 4) : τ' a v i = c*torusWeights m u i*v i := by
      rw [haction]
      change c*(Matrix.mulVec t.val.val v i)=_
      rw [hu]
      fin_cases i <;>
        simp [torusWeights,SuzukiTorusGL,SuzukiTorusMatrix,Matrix.mulVec,dotProduct,
          Fin.sum_univ_four,mul_assoc]
    have hd := diagonal_fixed_finrank_le m τ' a c hc (torusWeights m u)
      (torusWeights_injective m u hu1) hdiag
    have hsum := fixedCodim_add_finrank τ' (zpowers a)
    have htotal := natural_finrank m
    have hcod := fixedCodim_map_equivariant τ τ' (MonoidHom.id X) E heq (zpowers a)
    simp only [Subgroup.map_id] at hcod
    omega
  · have hd : orderOf g ∣ (2^(2*m+1))^2+1 := by
      rw [←Nat.card_zpowers]
      exact (card_dvd_of_le hU).trans hnonsplit.card_dvd
    have hfix : fixedSpace τ (zpowers a)=⊥ := by
      apply le_bot_iff.mp
      intro v hv
      change v=0
      have hh : τ a v=v := hv ⟨a,mem_zpowers a⟩
      rw [he] at hh
      have hv' : natural m g v=c⁻¹ • v := by
        calc
          _ = c⁻¹ • (c • natural m g v) := by rw [smul_smul,inv_mul_cancel₀ hc,one_smul]
          _ = c⁻¹ • v := congrArg (fun w => c⁻¹ • w) hh
      exact natural_nonsplit_no_eigenvector m g hg hd _ v hv'
    have hh := fixedCodim_add_finrank τ (zpowers a)
    rw [hfix,finrank_bot] at hh
    have hd := natural_finrank m
    omega

/-- The full binary normalizer satisfies the unrounded Suzuki odd-prime bound. -/
theorem normalizer_odd_prime_fixedCodim (m : ℕ) (hm : 1 ≤ m)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (a : linearNormalizer (natural m)) (ha : orderOf a = p) :
    8 * (2*m+1) ≤ 3 * fixedCodim (normalizerRepresentation (natural m)) (zpowers a) := by
  by_contra hn
  have hs : 3 * fixedCodim (normalizerRepresentation (natural m)) (zpowers a) <
      8*(2*m+1) := by omega
  obtain ⟨g,c,hc,hg,he⟩ := normalizer_small_displacement_scalar_inner m hm hp ho a ha hs
  have ha1 : a ≠ 1 := by intro ha1; simp [ha1] at ha; exact hp.ne_one ha.symm
  have hb := scalar_odd_fixedCodim m hm (normalizerRepresentation (natural m)) a ha1
    (fun x y hxy => Subtype.ext (Units.ext hxy)) g hg c hc he
  omega

end Representation.SuzukiNatural
