module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalMinusTorus
public import Theory.FieldTheory.BinaryTorusTwoPower
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Constructing and inverting the original minus torus

The Hall subgroup of the literal Borel is cyclic of order 2ⁿ−1. Its
subgroup of roots of order dividing 2ᵐ+1, when n=2m, has exactly that
order. When m is odd it contains the original cubic.

The cubic inverter preserves the Sylow-normalizer quotient even when it
does not preserve the chosen Hall complement. On that quotient its field
automorphism is nontrivial and has two-power order. Odd m forces order
two, so it is the half-degree Frobenius. Hence the original inverter
inverts the entire minus torus modulo the original Sylow.

The concrete exceptional quotient spectra and the existing whole-module
recognition now finish the exceptional conclusion assuming only odd
half-degree and fixation of the actual minus-torus roots on omega. The
source module argument must still discharge those two premises; the
initial component-and-cubic sieve remains open as well.
Source: Aschbacher--Smith 5.1.13, final paragraph, printed p.638,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The original cubic inverter also inverts the minus torus modulo T.
No normalization of the selected Hall complement by the inverter is assumed. -/
theorem CartanPair.inverts_minus_torus_mod_sylow
    {T : Sylow 2 G} {L H A B D E : Subgroup G} {m : ℕ}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hlin : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^(2*m)))
    (hm : Odd m) (hDA : D ≤ A) (hDc : Nat.card D = 3)
    {t : G} (ht : t ∈ (T : Subgroup G)) (hti : ∀ x ∈ D, t*x*t⁻¹=x⁻¹)
    (hEA : E ≤ A) (hEc : Nat.card E = 2^m+1) :
    ∀ x ∈ E, t*x*t⁻¹*x ∈ (T : Subgroup G) := by
  obtain ⟨F,_,_,hF,⟨e₀⟩⟩ := hlin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=2*m)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e := e₀.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F:=F)).symm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  let tN : normalizer (L : Set G) := ⟨t,hTL ht⟩
  let α := L.normalizerMonoidHom tN
  let β := MulAut.congr e (normalizerQuotientAction L (pCore 2 L) tN)
  have he (x : L) : q (α x) = β (q x) := by
    change e (QuotientGroup.mk' _ (α x)) =
      e (normalizerQuotientAction L (pCore 2 L) tN
        (e.symm (e (QuotientGroup.mk' _ x))))
    rw [e.symm_apply_apply]
    simp only [normalizerQuotientAction,MonoidHom.comp_apply,quotientAut_apply_mk]
    rfl
  have hPa : (P : Subgroup L).map α.toMonoidHom = (P : Subgroup L) := by
    apply eq_of_le_of_card_ge
    · rw [hP]
      rintro _ ⟨x,hx,rfl⟩
      change t*x.val*t⁻¹ ∈ (T : Subgroup G)
      exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht hx)
        ((T : Subgroup G).inv_mem ht)
    · exact (Nat.card_congr ((P : Subgroup L).equivMapOfInjective
        α.toMonoidHom α.injective).toEquiv).le
  obtain ⟨f,σ,hf,hfk,hfe⟩ := Matrix.SpecialLinearGroup.exists_sylowNormalizer_torus_action
    q hq P (hk.symm ▸ pCore_isPGroup.le_sylow_of_normal P) α β he hPa
  let N := normalizer (P : Set L)
  let j : N →* G := L.subtype.comp N.subtype
  have hj : Function.Injective j := L.subtype_injective.comp N.subtype_injective
  have hjr : j.range = localBorel T L := by
    rw [MonoidHom.range_comp,range_subtype]
    change (normalizer ((P : Subgroup L) : Set L)).map L.subtype = _
    rw [hP,←localBorel_eq_map]
  let A₀ := A.comap j
  have hAj : A₀.map j = A := map_comap_eq_self (hjr.symm ▸ c.left_le)
  have hfo : Odd (Nat.card A₀) := by
    rw [Nat.card_congr (A₀.equivMapOfInjective j hj).toEquiv,hAj]
    have hh := OddHall.odd_hall_odd c.left_hall
    rwa [Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv] at hh
  have hPN : N.map α.toMonoidHom = N := by
    have hh := map_equiv_normalizer_eq (P : Subgroup L) α
    rw [hPa] at hh
    exact hh
  let αN : MulAut N := (α.subgroupMap N).trans (MulEquiv.subgroupCongr hPN)
  have hα (x : N) : j (αN x) = t*j x*t⁻¹ := rfl
  have hfα (x : N) : f (αN x) = Units.map σ.toMonoidHom (f x) := hfe x (αN x) rfl
  have hsne : σ ≠ 1 := by
    intro hs
    have hcardD : 1 < Nat.card D := by rw [hDc]; decide
    let : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp hcardD
    obtain ⟨z,hz⟩ := exists_ne (1:D)
    obtain ⟨x,hx,hxz⟩ := hAj.ge (hDA z.property)
    have hinvN : αN x = x⁻¹ := by
      apply hj
      rw [hα,map_inv,hxz]
      exact hti z z.property
    have hfi : f x = (f x)⁻¹ := by
      have hh := hfα x
      rw [hinvN,map_inv,hs] at hh
      exact hh.symm
    have hsq : (f x)^2 = 1 := by
      calc
        (f x)^2 = f x*(f x)⁻¹ := by rw [pow_two]; exact congrArg (fun a => f x*a) hfi
        _ = 1 := mul_inv_cancel _
    have hfoimage : Odd (Nat.card (A₀.map f)) := hfo.of_dvd_nat (A₀.card_map_dvd f)
    have hfx : f x = 1 := by
      let y : A₀.map f := ⟨f x,mem_map_of_mem f hx⟩
      have hy : y^2 = 1 := Subtype.ext hsq
      have heq : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hfoimage.coprime_two_left
        (orderOf_dvd_of_pow_eq_one hy) (orderOf_dvd_natCard y)
      exact congrArg Subtype.val (orderOf_eq_one_iff.mp heq)
    have hxp : (x : L) ∈ P := (hfk x).mp hfx
    have hzT : (z : G) ∈ (T : Subgroup G) := by
      change (x : L) ∈ (P : Subgroup L) at hxp
      rw [hP] at hxp
      change j x ∈ (T : Subgroup G) at hxp
      rwa [hxz] at hxp
    have hoD : Odd (Nat.card D) := by rw [hDc]; decide
    have hd : Disjoint D (T : Subgroup G) := by
      apply disjoint_of_coprime_natCard
      obtain ⟨k,hk⟩ := T.isPGroup'.exists_card_eq
      rw [hk]
      exact hoD.coprime_two_right.pow_right k
    exact hz (Subtype.ext (hd.le_bot ⟨z.property,hzT⟩))
  obtain ⟨k,hk⟩ := T.isPGroup'.exists_pow_pow_eq_one (⟨t,ht⟩ : T)
  have htG : t ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have haj (r : ℕ) (x : N) : j ((αN ^ r) x) = t^r * j x * (t^r)⁻¹ := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ', MulAut.mul_apply, hα, ih, pow_succ']
      group
  have hfj (r : ℕ) (x : N) :
      f ((αN ^ r) x) = Units.map (σ ^ r).toMonoidHom (f x) := by
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [pow_succ', MulAut.mul_apply, hfα, ih]
      apply Units.ext
      change σ ((σ ^ r) ((f x : Fˣ) : F)) = (σ ^ (r+1)) ((f x : Fˣ) : F)
      rw [pow_succ']
      rfl
  have has : αN ^ (2^k) = 1 := by
    apply MulEquiv.ext
    intro x
    apply hj
    simpa only [htG,one_mul,inv_one,mul_one,MulAut.one_apply] using haj (2^k) x
  have hsp : σ ^ (2^k) = 1 := by
    ext z
    by_cases hz : z = 0
    · simp [hz]
    obtain ⟨x,hx⟩ := hf (Units.mk0 z hz)
    have he := congrArg Units.val (hfj (2^k) x)
    rw [has] at he
    simp only [MulAut.one_apply,hx] at he
    exact he.symm
  have horder : orderOf σ ∣ 2*m := by
    simpa only [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF] using
      orderOf_dvd_natCard σ
  have hoc : Nat.Coprime (orderOf σ) m :=
    (hm.coprime_two_left.pow_left k).of_dvd_left (orderOf_dvd_of_pow_eq_one hsp)
  have hss : σ^2 = 1 := orderOf_dvd_iff_pow_eq_one.mp
    (hoc.dvd_of_dvd_mul_right horder)
  obtain ⟨r,_,hr,hσ⟩ := FiniteField.BinaryTorusTwoPower.involution_eq_half_frobenius hF σ hss hsne
  have hrm : r = m := by omega
  subst r
  intro x hx
  obtain ⟨a,_,hax⟩ := hAj.ge (hEA hx)
  have hxp : x ^ (2^m+1) = 1 := by
    rw [←hEc]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨x,hx⟩ : E)))
  have hap : a ^ (2^m+1) = 1 := by
    apply hj
    rw [map_pow,hax,map_one]
    exact hxp
  have hfpow : (f a) ^ (2^m+1) = 1 := by rw [←map_pow,hap,map_one]
  have hfprod : f (αN a*a) = 1 := by
    rw [map_mul,hfα]
    have hfσ : Units.map σ.toMonoidHom (f a) = (f a) ^ (2^m) := Units.ext (hσ (f a))
    rw [hfσ,←pow_succ]
    exact hfpow
  have hPmem := (hfk (αN a*a)).mp hfprod
  change (αN a*a : L) ∈ (P : Subgroup L) at hPmem
  rw [hP] at hPmem
  change j (αN a*a) ∈ (T : Subgroup G) at hPmem
  simpa only [map_mul,hα,hax] using hPmem

/-- The minus torus is the actual subgroup of roots of order dividing
`2^m+1` in the original cyclic Hall Cartan. -/
theorem CartanPair.exists_minus_torus
    {T : Sylow 2 G} {L H A B : Subgroup G} {m : ℕ}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hlin : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^(2*m))) :
    ∃ E : Subgroup G, E ≤ A ∧ Nat.card E = 2^m+1 ∧
      ∀ x : G, x ∈ E ↔ x ∈ A ∧ x^(2^m+1) = 1 := by
  let : IsCyclic A := (c.left_cyclic_and_card hTL hlin).1
  let : CommGroup A := IsCyclic.commGroup
  let C := (powMonoidHom (2^m+1) : A →* A).ker
  let E := C.map A.subtype
  have hAc := c.left_card hlin hTL
  have hdiv : 2^m+1 ∣ Nat.card A := by
    rw [hAc, Nat.mul_comm 2 m, pow_mul]
    have he : (2^m)^2-1 = (2^m-1)*(2^m+1) := by
      simpa only [one_pow,mul_comm] using Nat.sq_sub_sq (2^m) 1
    rw [he]
    exact dvd_mul_left _ _
  refine ⟨E,map_subtype_le C,?_,?_⟩
  · rw [card_map_of_injective A.subtype_injective]
    exact (IsCyclic.card_powMonoidHom_ker (G := A) (2^m+1)).trans
      (Nat.gcd_eq_right hdiv)
  · intro x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,congrArg Subtype.val ha⟩
    · rintro ⟨hx,hp⟩
      exact ⟨⟨x,hx⟩,Subtype.ext hp,rfl⟩

/-- At odd half-degree the original cubic lies in the constructed minus
torus, and its original inverter inverts that torus modulo the same Sylow. -/
theorem LocalCartanWitness.exists_inverted_minus_torus
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (d : LocalCartanWitness T H A Y X D)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B) (hm : Odd (n/2)) :
    ∃ E : Subgroup G, E ≤ A ∧ D ≤ E ∧ Nat.card E = 2^(n/2)+1 ∧
      (∀ x : G, x ∈ E ↔ x ∈ A ∧ x^(2^(n/2)+1) = 1) ∧
      ∃ t ∈ (T : Subgroup G) ⊓ X,
        ∀ x ∈ E, t*x*t⁻¹*x ∈ (T : Subgroup G) := by
  have hn : n = 2*(n/2) := by
    obtain ⟨k,hk⟩ := d.even_exponent h c
    omega
  have hl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^(2*(n/2))) := hn ▸ h.linear
  obtain ⟨E,hEA,hEc,hroot⟩ := c.exists_minus_torus h.sylow_normalizes hl
  have h3 : 3 ∣ 2^(n/2)+1 := by
    apply Nat.dvd_of_mod_eq_zero
    have hp := Nat.BinaryTorusParity.two_pow_mod_three (n/2)
    rw [Nat.odd_iff.mp hm] at hp
    norm_num at hp
    omega
  have hDE : D ≤ E := by
    intro x hx
    refine (hroot x).mpr ⟨(d.cubic_le.trans inf_le_left) hx,?_⟩
    apply orderOf_dvd_iff_pow_eq_one.mp
    apply (orderOf_dvd_of_pow_eq_one (show x^3=1 from ?_)).trans h3
    rw [←d.cubic_card]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨x,hx⟩ : D)))
  obtain ⟨t,ht,hi⟩ := d.cubic_inverted
  exact ⟨E,hEA,hDE,hEc,hroot,t,ht,c.inverts_minus_torus_mod_sylow
    h.sylow_normalizes hl hm (d.cubic_le.trans inf_le_left) d.cubic_card ht.1 hi hEA hEc⟩

/-- The original inverter, torus order and cubic containment are discharged.
Only the remaining module-theoretic centralization of the minus torus and
oddness of the half-degree are needed to complete the exceptional conclusion. -/
theorem localCartan_escape_of_minus_roots_centralize
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hm : Odd (n/2))
    (hc : ∀ x ∈ A, x^(2^(n/2)+1) = 1 → x ∈ omegaCentralizer T) :
    n = 2 ∧ CartanExceptionalConclusion T L W H := by
  obtain ⟨E,hEA,hDE,hEc,hroot,hi⟩ := d.exists_inverted_minus_torus h c hm
  have hEC : E ≤ omegaCentralizer T := fun x hx =>
    hc x (hroot x |>.mp hx).1 (hroot x |>.mp hx).2
  have hn := localCartan_degree_two_of_minus_torus h hH hgen c hY d hEA hDE hEC hEc hi
  exact ⟨hn,localCartan_escape_of_minus_torus h hH hgen c hY d hEA hDE hEC hEc hi⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
