module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericCartan
public import Theory.FieldTheory.SmallMultiplicativeDisplacement
public import Theory.GroupTheory.Hall.OddKernelProjection
public import Theory.GroupTheory.Hall.TwoClosedNormal
public import Theory.SpecificGroups.SL2.SylowNormalizerTorusAction
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.NormalizerQuotientInner

/-!
# Degree two from the original Cartan and its inverted cubic

Let the left Cartan normalize a subgroup K normalized by the original
Sylow. If A ∩ K has order at most three and an element of T ∩ K inverts
an actual cubic in A, then the original field degree is two.

Project the literal Borel through its Sylow kernel onto Fˣ. Its intersection
with K is normal, and the odd-subgroup projection lemma identifies its
image with that of A ∩ K. The inverter therefore has at most three
multiplicative displacements. Its action on the cubic is nontrivial, so
the finite-field bound forces |F| = 4. The original inverter need not
normalize the chosen Hall complement.

Source: Aschbacher–Smith 5.1.13, printed p.638, refs/quasithin.pdf. The
companion LocalTorus module applies this to the actual A₇ configuration;
normalization of K remains an explicit premise for the block argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The literal Hall complement and cubic inverter force the original degree two. -/
theorem CartanPair.degree_two_of_normalized_component
    {T : Sylow 2 G} {L H A B K D : Subgroup G} {n : ℕ}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hlin : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hAK : A ≤ normalizer (K : Set G))
    (hcap : Nat.card (A ⊓ K : Subgroup G) ≤ 3)
    (hDA : D ≤ A) (hDc : Nat.card D = 3)
    (hinv : ∃ t ∈ (T : Subgroup G) ⊓ K, ∀ x ∈ D, t*x*t⁻¹=x⁻¹) : n = 2 := by
  obtain ⟨t,ht,hti⟩ := hinv
  obtain ⟨F,_,_,hF,⟨e₀⟩⟩ := hlin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e := e₀.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F:=F)).symm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  let tN : normalizer (L : Set G) := ⟨t,hTL ht.1⟩
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
      exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht.1 hx)
        ((T : Subgroup G).inv_mem ht.1)
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
  let K₀ := K.comap j
  have hAj : A₀.map j = A := map_comap_eq_self (hjr.symm ▸ c.left_le)
  have hNKn : j.range ≤ normalizer (K : Set G) := by
    rw [hjr,←c.left_sup_intersection hTL]
    exact sup_le (inf_le_left.trans hTK) hAK
  let : K₀.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    intro x _
    apply mem_normalizer_iff.mpr
    intro y
    change j y ∈ K ↔ j (x*y*x⁻¹) ∈ K
    rw [map_mul,map_mul,map_inv]
    exact mem_normalizer_iff.mp (hNKn ⟨x,rfl⟩) (j y)
  have hfo : Odd (Nat.card A₀) := by
    rw [Nat.card_congr (A₀.equivMapOfInjective j hj).toEquiv,hAj]
    have hh := OddHall.odd_hall_odd c.left_hall
    rwa [Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv] at hh
  have hker : f.ker = (P : Subgroup L).subgroupOf N := by
    ext x
    exact hfk x
  have hfp : IsPGroup 2 f.ker := hker.symm ▸ P.isPGroup'.comap_subtype
  have hfr : A₀.map f = ⊤ := by
    have hgen : (P : Subgroup L).subgroupOf N ⊔ A₀ = ⊤ := by
      apply (map_injective hj)
      rw [Subgroup.map_sup,hAj,←MonoidHom.range_eq_map,hjr]
      have hPN : (P : Subgroup L) ≤ N := (P : Subgroup L).le_normalizer
      change ((P : Subgroup L).subgroupOf N).map (L.subtype.comp N.subtype) ⊔ A = _
      rw [←map_map,map_subgroupOf_eq_of_le hPN,hP,subgroupOf_map_subtype]
      exact c.left_sup_intersection hTL
    have hh := congrArg (map f) hgen
    rw [Subgroup.map_sup,←hker,(Subgroup.map_eq_bot_iff _).mpr le_rfl,bot_sup_eq,
      map_top_of_surjective _ hf] at hh
    exact hh
  have hKi : K₀.map f = (A₀ ⊓ K₀).map f := normal_image_eq_odd_intersection f A₀ K₀ hfp hfo hfr
  have hKc : Nat.card (K₀.map f) ≤ 3 := by
    rw [hKi]
    apply (Nat.card_le_card_of_surjective _ (f.subgroupMap_surjective (A₀ ⊓ K₀))).trans
    have hm : (A₀ ⊓ K₀).map j = A ⊓ K := by
      change ((A ⊓ K).comap j).map j = _
      exact map_comap_eq_self (inf_le_left.trans (hjr.symm ▸ c.left_le))
    rw [Nat.card_congr ((A₀ ⊓ K₀).equivMapOfInjective j hj).toEquiv,hm]
    exact hcap
  have hPN : N.map α.toMonoidHom = N := by
    have hh := map_equiv_normalizer_eq (P : Subgroup L) α
    rw [hPa] at hh
    exact hh
  let αN : MulAut N := (α.subgroupMap N).trans (MulEquiv.subgroupCongr hPN)
  have hα (x : N) : j (αN x) = t*j x*t⁻¹ := rfl
  have hfα (x : N) : f (αN x) = Units.map σ.toMonoidHom (f x) := hfe x (αN x) rfl
  have hdisp : (FiniteField.BinaryTorusInvolution.displacement σ).range ≤ K₀.map f := by
    rintro _ ⟨u,rfl⟩
    obtain ⟨x,hx,hxu⟩ := hfr.ge (show u ∈ (⊤ : Subgroup Fˣ) from trivial)
    have hd : αN x*x⁻¹ ∈ K₀ := by
      change j (αN x*x⁻¹) ∈ K
      rw [map_mul,map_inv,hα]
      have hh := le_normalizer_iff.mp hAK (j x) hx t⁻¹ (K.inv_mem ht.2)
      simpa only [mul_assoc] using K.mul_mem ht.2 hh
    refine ⟨αN x*x⁻¹,hd,?_⟩
    rw [map_mul,map_inv,hfα,hxu]
    rfl
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
  have hf4 := FiniteField.BinaryTorusInvolution.card_eq_four_of_small_displacement σ hsne
    ((card_le_of_le hdisp).trans hKc)
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  exact hF.symm.trans hf4

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
