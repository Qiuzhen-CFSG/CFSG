module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.RadicalAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Prime
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.PerfectSimpleImageKernel

/-!
# A size obstruction for the remaining prime component action

The common original Sylow image in the A₅/S₅ pair has order four or eight.
It is Sylow in the full image of N_G(R₁), so sixteen does not divide that
image's order. In the prime-PSL₂ row, the earlier radical identity makes
K normalize R₁. Its literal action on R₁/Φ(R₁) has a two-group kernel;
therefore the order of K/O₂(K) divides the action-image order.

An elementary two-group of order at most 256 has automorphism order dividing
|GL₈(2)|. The only prime divisors above seven are 17,31,127, and each
corresponding prime PSL₂ order is divisible by sixteen. This excludes
the prime row when R₁/Φ(R₁) has at most eight binary dimensions. The
original-subgroup application proves that every remaining prime-row
counterexample must have |R₁/Φ(R₁)|>256, without assuming a radical bound.
More generally, the same obstruction excludes a nontrivial action of K on
any normalized elementary two-subgroup of that size: perfectness and the
simple quotient put the action kernel in O₂(K). SymplecticDerived applies
this to [R₁,R₁] and closes the prime row using the field-four geometry.
The odd-extension row remains with this witness task.

The geometry, surviving list, full 11.3.2 and Kz=K retain the earlier-source
producers listed in RadicalAction. OddKernelNormalizer remains with
qt-d-1222-natural-odd-kernel-normalizer; qt-d-1222-shadow-components owns
its final discharge. No abstract A₅-overgroup uniqueness is used.
Source: Aschbacher–Smith 11.4.4–11.5.1, printed pp.778–779;
Burnside's basis theorem and the general-linear and PSL₂ order formulas.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation

private theorem no_sixteen_of_common_five_sylow
    {A : Type*} [Group A] [Finite A] {U N P : Subgroup A}
    (hm : Nonempty (U ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (U ≃* Equiv.Perm (Fin 5)))
    (hPU : Chapter1.IsSylowIn 2 P U) (hPN : Chapter1.IsSylowIn 2 P N) :
    ¬ 16 ∣ Nat.card N := by
  obtain ⟨Q,hQ⟩ := hPU
  obtain ⟨R,hR⟩ := hPN
  have hcard : Nat.card R = Nat.card Q := by
    rw [←card_map_of_injective N.subtype_injective, hR,
      ←hQ, card_map_of_injective U.subtype_injective]
  have hsmall : Nat.card Q ≤ 8 := by
    have hc := Q.card_eq_multiplicity
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      have hu : Nat.card U = 60 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
        norm_num [Nat.factorial]
      rw [hu] at hc
      have he : Nat.card Q = 4 := hc.trans (by decide +kernel)
      omega
    · obtain ⟨e⟩ := hm
      have hu : Nat.card U = 120 := by
        rw [Nat.card_congr e.toEquiv]
        norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
      rw [hu] at hc
      have he : Nat.card Q = 8 := hc.trans (by decide +kernel)
      omega
  intro hd
  have hdR : 16 ∣ Nat.card R := R.pow_dvd_card_of_pow_dvd_card (n := 4) hd
  have hlo := Nat.le_of_dvd (Nat.card_pos (α := R)) hdR
  omega

private theorem prime_psl_card_small_aut_impossible
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 256) {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hd : p * (p ^ 2 - 1) / 2 ∣ Nat.card (MulAut E))
    (h16 : ¬ 16 ∣ p * (p ^ 2 - 1) / 2) : False := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup (p := 2) (G := E)).exists_card_eq
  have hn8 : n ≤ 8 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [←hn]
    exact hE
  have hAut : Nat.card (MulAut E) ∣ 2^28 * 3^5 * 5^2 * 7^2 * 17 * 31 * 127 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E n hn]
    interval_cases n <;> norm_num [Fin.prod_univ_succ]
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  have htwo : 2 ∣ p ^ 2 - 1 := by
    obtain ⟨a,ha⟩ := ho
    have hpa : p = 2*a+1 := by omega
    rw [hpa]
    refine ⟨2*a*(a+1),?_⟩
    have hs : 1 ≤ (2*a+1)^2 := by nlinarith
    nlinarith [Nat.sub_add_cancel hs]
  have hpd : p ∣ Nat.card (MulAut E) :=
    (Nat.dvd_div_of_mul_dvd (show 2*p ∣ p*(p^2-1) by
      simpa only [Nat.mul_comm 2 p] using Nat.mul_dvd_mul_left p htwo)).trans hd
  have hpf := hpd.trans hAut
  rcases hp.dvd_mul.mp hpf with hpf | hpf
  · rcases hp.dvd_mul.mp hpf with hpf | hpf
    · rcases hp.dvd_mul.mp hpf with hpf | hpf
      · rcases hp.dvd_mul.mp hpf with hpf | hpf
        · rcases hp.dvd_mul.mp hpf with hpf | hpf
          · rcases hp.dvd_mul.mp hpf with hpf | hpf
            · have he := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two hpf
              omega
            · have he := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_three hpf
              omega
          · have he := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_five hpf
            omega
        · have he := Nat.prime_eq_prime_of_dvd_pow hp (by decide : Nat.Prime 7) hpf
          omega
      · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17)).mp hpf
        subst p
        exact h16 (by norm_num)
    · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31)).mp hpf
      subst p
      exact h16 (by norm_num)
  · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 127)).mp hpf
    subst p
    exact h16 (by norm_num)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- The actual prime-PSL₂ branch of a hypothetical generation-two H
needs more than eight generators in the original first radical. -/
theorem ofFlag_large_generation_prime_frattini_size
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hn : 1 < ChapterE.generationParameter H)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hm : ClassicalGroup.IsPSL ((ofFlag S f X z H).K ⧸
      pCore 2 (ofFlag S f X z H).K) 2 p) :
    256 < Nat.card (f.Ri 0 ⧸ frattini (f.Ri 0)) := by
  let E := ofFlag S f X z H
  let R := f.Ri 0
  let N := normalizer (R : Set G)
  let W := radicalFrattiniImage R N
  have hAK : f.Li 0 ≤ E.K := le_conjugateSpanBy _ _
  have hA : f.Li 0 ≠ ⊥ := by
    intro hbot
    have hlocal := Triangle.Reselection.flag_residual_mem_local D S f 0
    apply hlocal.1.ne_bot
    rw [hbot,bot_subgroupOf]
  have hKc : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) E.K :=
    ⟨⟨h.line_component_centralizes,h.line_component.2.subgroupOf_of_le
      h.line_component_centralizes (Subgroup.centralizer_le_normalizer _)⟩,
      normal_subgroupOf_of_le_normalizer
        ((Subgroup.centralizer_le_normalizer _).trans E.G₁_normalizes_K)⟩
  have hR := Radical.ofFlag_surviving_radical_containment S f X z H E.K hKc hA hAK
    ((f.invariant 0).trans E.G₁_normalizes_K) hcase
  have hcore := prime_radical_eq_core E h (f.invariant 0) hR (by omega : 3 < p) hm
  have hKN : E.K ≤ N := by
    change E.K ≤ normalizer (E.R₁ : Set G)
    rw [hcore]
    exact le_sup_left.trans ((E.K ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  let i := inclusion hKN
  let a := (radicalFrattiniAction R).comp i
  have hker : IsPGroup 2 a.ker := by
    change IsPGroup 2 ((radicalFrattiniAction R).ker.comap i)
    rw [ofFlag_radical_frattini_kernel S f]
    exact ((isPGroup_pCoreIn 2 (f.Li 0 ⊔ (T : Subgroup G))).comap_subtype).comap_of_injective
      i (inclusion_injective hKN)
  have hk : a.ker ≤ pCore 2 E.K := le_sSup ⟨inferInstance,hker⟩
  have hd : Nat.card (E.K ⧸ pCore 2 E.K) ∣ Nat.card a.range := by
    have hh := index_dvd_of_le hk
    rwa [index_ker] at hh
  have hW : W = (radicalFrattiniAction R).range := by
    change (N.subgroupOf N).map (radicalFrattiniAction R) = _
    rw [subgroupOf_self,←MonoidHom.range_eq_map]
  have hAW : a.range ≤ W := by
    rw [hW]
    rintro y ⟨k,rfl⟩
    exact ⟨i k,rfl⟩
  have hdW := hd.trans (card_dvd_of_le hAW)
  obtain ⟨_,_,hmodels,_,_,_,_,_,hSyl,_,hSylN,_⟩ :=
    ofFlag_large_generation_frattini_pair S f X z H h hcase he hlinear h1132 hcontrol hH hHz hn
  have h16 : ¬ 16 ∣ Nat.card (E.K ⧸ pCore 2 E.K) := by
    intro hdiv
    exact no_sixteen_of_common_five_sylow hmodels hSyl hSylN (hdiv.trans hdW)
  have hAut := hd.trans a.range.card_subgroup_dvd_card
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hcard : Nat.card (E.K ⧸ pCore 2 E.K) = p * (p ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv,
      GorensteinWalter.psl2_card_formula F
        ⟨p,1,hp,hp.odd_of_ne_two (by omega),by omega,by simpa using hF⟩,hF]
  rw [hcard] at h16 hAut
  let : Fact (IsPGroup 2 R) := ⟨isPGroup_pCoreIn 2 (f.Li 0 ⊔ (T : Subgroup G))⟩
  let : IsElementaryAbelian 2 (R ⧸ frattini R) := isElementaryAbelian_quotient_frattini
  by_contra! hsmall
  exact prime_psl_card_small_aut_impossible hsmall hp hp7 hAut h16

/-- The actual prime component cannot act nontrivially on a normalized
elementary two-subgroup having at most eight binary dimensions. -/
theorem ofFlag_large_generation_prime_small_action_impossible
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hn : 1 < ChapterE.generationParameter H)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hm : ClassicalGroup.IsPSL ((ofFlag S f X z H).K ⧸
      pCore 2 (ofFlag S f X z H).K) 2 p)
    (U : Subgroup G) (hU : IsElementaryAbelian 2 U) (hsmall : Nat.card U ≤ 256)
    (hKU : (ofFlag S f X z H).K ≤ normalizer (U : Set G))
    (hmove : ¬ (ofFlag S f X z H).K ≤ centralizer (U : Set G)) : False := by
  let E := ofFlag S f X z H
  let R := f.Ri 0
  let N := normalizer (R : Set G)
  let W := radicalFrattiniImage R N
  have hAK : f.Li 0 ≤ E.K := le_conjugateSpanBy _ _
  have hA : f.Li 0 ≠ ⊥ := by
    intro hbot
    have hlocal := Triangle.Reselection.flag_residual_mem_local D S f 0
    apply hlocal.1.ne_bot
    rw [hbot,bot_subgroupOf]
  have hKc : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) E.K :=
    ⟨⟨h.line_component_centralizes,h.line_component.2.subgroupOf_of_le
      h.line_component_centralizes (Subgroup.centralizer_le_normalizer _)⟩,
      normal_subgroupOf_of_le_normalizer
        ((Subgroup.centralizer_le_normalizer _).trans E.G₁_normalizes_K)⟩
  have hR := Radical.ofFlag_surviving_radical_containment S f X z H E.K hKc hA hAK
    ((f.invariant 0).trans E.G₁_normalizes_K) hcase
  have hcore := prime_radical_eq_core E h (f.invariant 0) hR (by omega : 3 < p) hm
  have hKN : E.K ≤ N := by
    change E.K ≤ normalizer (E.R₁ : Set G)
    rw [hcore]
    exact le_sup_left.trans ((E.K ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  let i := inclusion hKN
  let a := (radicalFrattiniAction R).comp i
  have hker : IsPGroup 2 a.ker := by
    change IsPGroup 2 ((radicalFrattiniAction R).ker.comap i)
    rw [ofFlag_radical_frattini_kernel S f]
    exact ((isPGroup_pCoreIn 2 (f.Li 0 ⊔ (T : Subgroup G))).comap_subtype).comap_of_injective
      i (inclusion_injective hKN)
  have hk : a.ker ≤ pCore 2 E.K := le_sSup ⟨inferInstance,hker⟩
  have hd : Nat.card (E.K ⧸ pCore 2 E.K) ∣ Nat.card a.range := by
    have hh := index_dvd_of_le hk
    rwa [index_ker] at hh
  have hW : W = (radicalFrattiniAction R).range := by
    change (N.subgroupOf N).map (radicalFrattiniAction R) = _
    rw [subgroupOf_self,←MonoidHom.range_eq_map]
  have hAW : a.range ≤ W := by
    rw [hW]
    rintro y ⟨k,rfl⟩
    exact ⟨i k,rfl⟩
  have hdW := hd.trans (card_dvd_of_le hAW)
  obtain ⟨_,_,hmodels,_,_,_,_,_,hSyl,_,hSylN,_⟩ :=
    ofFlag_large_generation_frattini_pair S f X z H h hcase he hlinear h1132 hcontrol hH hHz hn
  have h16 : ¬ 16 ∣ Nat.card (E.K ⧸ pCore 2 E.K) := by
    intro hdiv
    exact no_sixteen_of_common_five_sylow hmodels hSyl hSylN (hdiv.trans hdW)
  let b := U.normalizerMonoidHom.comp (inclusion hKU)
  have hbne : b ≠ 1 := by
    intro heq
    apply hmove
    intro k hk u hu
    have hh := congrArg (fun a : MulAut U => (a ⟨u,hu⟩ : G))
      (DFunLike.congr_fun heq ⟨k,hk⟩)
    change k*u*k⁻¹=u at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let : Group.IsPerfect E.K := Radical.relative_component_perfect h.line_component
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup (E.K ⧸ pCore 2 E.K) := e.isSimpleGroup
  let q := QuotientGroup.mk' (pCore 2 E.K)
  have hqk : q.ker = pCore 2 E.K := QuotientGroup.ker_mk' _
  let : Group.IsSolvable q.ker := by
    rw [hqk]
    let : Group.IsNilpotent (pCore 2 E.K) := pCore_isPGroup.isNilpotent
    infer_instance
  have hbker : b.ker ≤ pCore 2 E.K := hqk ▸
    ker_le_of_nontrivial_hom_of_simple_quotient q (QuotientGroup.mk'_surjective _) b hbne
  have hbdiv : Nat.card (E.K ⧸ pCore 2 E.K) ∣ Nat.card (MulAut U) := by
    have hh := index_dvd_of_le hbker
    rw [index_ker] at hh
    exact hh.trans b.range.card_subgroup_dvd_card
  have hcard : Nat.card (E.K ⧸ pCore 2 E.K) = p * (p ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv,
      GorensteinWalter.psl2_card_formula F
        ⟨p,1,hp,hp.odd_of_ne_two (by omega),by omega,by simpa using hF⟩,hF]
  rw [hcard] at hbdiv h16
  let := hU
  exact prime_psl_card_small_aut_impossible hsmall hp hp7 hbdiv h16

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
