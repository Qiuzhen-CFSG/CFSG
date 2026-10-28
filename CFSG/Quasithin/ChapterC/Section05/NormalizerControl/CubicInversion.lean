module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.QuotientOrders

/-!
# The original moving conjugate inverts the cubic action

An element of U₁ˣ moving U₁ remains a nonidentity involution in the
literal centralizer quotient. It normalizes the cubic image of K₁.
If it centralized that image, it would fix the K₁-span of Ω₁Z(T₁),
which contains U₁. Thus its automorphism of that group of order three
is inversion. This constructs the final input of the A₃ cubic
transvection normality argument from the actual source conjugate.

Source: Aschbacher–Smith C.5.13, printed p.162.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem centralizes_span_of_commutes_in_action
    (V Z K : Subgroup G) [V.Normal] (hZV : Z ≤ V)
    (b : G) (hbZ : b ∈ centralizer (Z : Set G))
    (hbK : QuotientGroup.mk' (centralizer (V : Set G)) b ∈
      centralizer (K.map (QuotientGroup.mk' (centralizer (V : Set G))) : Set _)) :
    b ∈ centralizer (conjugateSpanBy Z K : Set G) := by
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  let a := MulAut.quotientConjNormal V (centralizer (V : Set G)) le_rfl
  have hs : conjugateSpanBy Z K ≤ centralizer ({b} : Set G) := by
    apply (closure_le _).mpr
    rintro v ⟨k,hk,z,hz,rfl⟩
    have hc : a (q b) * a (q k) = a (q k) * a (q b) := by
      rw [← a.map_mul,← a.map_mul]
      exact congrArg a (hbK (q k) (mem_map_of_mem q hk)).symm
    let z₀ : V := ⟨z,hZV hz⟩
    have hzfix : a (q b) z₀ = z₀ := by
      apply Subtype.ext
      change b*z*b⁻¹=z
      rw [← hbZ z hz,mul_inv_cancel_right]
    have he : a (q b) (a (q k) z₀) = a (q k) z₀ := by
      have hh := congrArg (fun f : MulAut V => f z₀) hc
      change a (q b) (a (q k) z₀) = a (q k) (a (q b) z₀) at hh
      rwa [hzfix] at hh
    have he' := congrArg V.subtype he
    change b*(k*z*k⁻¹)*b⁻¹=k*z*k⁻¹ at he'
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he').symm
  intro v hv
  exact mem_centralizer_singleton_iff.mp (hs hv)
theorem cubic_normalizer_inverts (K : Subgroup G) (hK : Nat.card K = 3)
    (b : G) (hb : b ∈ normalizer (K : Set G)) (hbC : b ∉ centralizer (K : Set G)) :
    ∀ k ∈ K, b*k*b⁻¹=k⁻¹ := by
  classical
  let f := K.normalizerMonoidHom ⟨b,hb⟩
  have hfix (k : K) (hk : k ≠ 1) : f k ≠ k := by
    intro he
    apply hbC
    intro z hz
    have hgen := zpowers_eq_top_of_prime_card hK hk
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp (hgen ▸ (show (⟨z,hz⟩ : K) ∈ (⊤ : Subgroup K) from mem_top _))
    have hh : f (⟨z,hz⟩ : K) = ⟨z,hz⟩ := by
      rw [← hn,map_zpow,he]
    have hh' := congrArg K.subtype hh
    change b*z*b⁻¹=z at hh'
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  intro k hk
  by_cases hk1 : k = 1
  · simp [hk1]
  let k₀ : K := ⟨k,hk⟩
  have hk₀ : k₀ ≠ 1 := fun he => hk1 (congrArg K.subtype he)
  have hgen := zpowers_eq_top_of_prime_card hK hk₀
  have ho : orderOf k₀ = 3 := (orderOf_eq_card_of_zpowers_eq_top hgen).trans hK
  have hf := (mem_zpowers_iff_mem_range_orderOf (x := k₀) (y := f k₀)).mp
    (hgen ▸ mem_top _)
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hf
  rw [Finset.mem_range,ho] at hn
  interval_cases n
  · have hh : f k₀ = 1 := by simpa using he.symm
    exact (hk₀ (f.injective (hh.trans f.map_one.symm))).elim
  · have hh : f k₀ = k₀ := by simpa using he.symm
    exact (hfix k₀ hk₀ hh).elim
  · have hh : f k₀ = k₀⁻¹ := by
      rw [← he]
      apply eq_inv_iff_mul_eq_one.mpr
      simpa only [← pow_succ,ho] using pow_orderOf_eq_one k₀
    exact congrArg K.subtype hh

omit [Finite G] in
theorem relative_centralizes_span
    (X V Z K : Subgroup G) (hVX : V ≤ X) (hXV : X ≤ normalizer (V : Set G))
    (hZV : Z ≤ V) (hKX : K ≤ X) (b : X)
    (hbZ : (b : G) ∈ centralizer (Z : Set G)) :
    let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
    QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X)) b ∈
      centralizer ((K.subgroupOf X).map
        (QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))) : Set _) →
    (b : G) ∈ centralizer (conjugateSpanBy Z K : Set G) := by
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  dsimp only
  intro hc
  have hz : b ∈ centralizer (Z.subgroupOf X : Set X) := by
    intro z hz
    exact Subtype.ext (hbZ z hz)
  have hh := centralizes_span_of_commutes_in_action (V.subgroupOf X) (Z.subgroupOf X)
    (K.subgroupOf X) (subgroupOf_mono _ hZV) b hz hc
  have he : (conjugateSpanBy (Z.subgroupOf X) (K.subgroupOf X)).map X.subtype =
      conjugateSpanBy Z K := by
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le (hZV.trans hVX),map_subgroupOf_eq_of_le hKX]
  intro z hz
  rw [← he] at hz
  obtain ⟨z,hz,rfl⟩ := hz
  exact congrArg X.subtype (hh z hz)
open ConjugateSource.RankOne
/-- The original moving conjugate supplies an actual inverting involution
in the literal action quotient of the constructed source span. -/
theorem alternating_three_source_inverter
    {T K : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) (ha : ChapterC.IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (X : Subgroup G) (hAX : K ⊔ T ≤ X)
    (hcore : T ⊓ centralizer (U K : Set G) = (K ⊔ T).pCoreIn 2)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let X₁ := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V₁ := conjugateSpanBy (omegaOneCenterAmbient T) X₁
    let hp := alternating_three_source_span h ha hT hTK P hP hA X hAX hcore
    let : (V₁.subgroupOf X₁).Normal :=
      (normal_subgroupOf_iff_le_normalizer hp.2.1).mpr hp.2.2.1
    let q := QuotientGroup.mk' (centralizer (V₁.subgroupOf X₁ : Set X₁))
    ∃ b : X₁, (b : G) ∈ (U K).map (MulAut.conj x⁻¹).toMonoidHom ∧
      IsInvolution (q b) ∧ ∀ c ∈ (K.subgroupOf X₁).map q, q b*c*(q b)⁻¹=c⁻¹ := by
  let A := K ⊔ T
  let X₁ := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  let V₁ := conjugateSpanBy (omegaOneCenterAmbient T) X₁
  obtain ⟨_he,hVX,hXV,hUV,_hVT,_hCV⟩ := alternating_three_source_span h ha hT hTK P hP hA X hAX hcore
  have hAX₁ : A ≤ X₁ := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hCV := (normalizer_core_omega_span A X T P hP hA hAX).2.2.1
  let : (V₁.subgroupOf X₁).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let q := QuotientGroup.mk' (centralizer (V₁.subgroupOf X₁ : Set X₁))
  let Kstar := (K.subgroupOf X₁).map q
  have hcK : Nat.card Kstar = 3 := alternating_three_quotient_image_card K T X₁ V₁
    ha hTK hAX₁ hVX hXV hUV hCV
  obtain ⟨b,hb,hbC⟩ := Set.not_subset.mp hnc
  have hbT : b ∈ T := (h.conjugate_le hx).trans inf_le_left hb
  have hbX : b ∈ X₁ := (le_sup_right.trans hAX₁) hbT
  let b₀ : X₁ := ⟨b,hbX⟩
  have hbK : b₀ ∈ normalizer (K.subgroupOf X₁ : Set X₁) := by
    rw [← subgroupOf_normalizer_eq (le_sup_left.trans hAX₁)]
    exact hTK hbT
  have hbn : q b₀ ∈ normalizer (Kstar : Set _) :=
    (K.subgroupOf X₁).le_normalizer_map q (mem_map_of_mem q hbK)
  have hbnc : q b₀ ∉ centralizer (Kstar : Set _) := by
    intro hc
    have hh := relative_centralizes_span X₁ V₁ (omegaOneCenterAmbient T) K hVX hXV
      (le_conjugateSpanBy _ _) (le_sup_left.trans hAX₁) b₀ (by
        intro z hz
        exact ((mem_omegaOneCenterAmbient_iff T z).mp hz).2.2 b hbT |>.symm) hc
    exact hbC (centralizer_le (alternating_three_omega_span h ha hT hTK) hh)
  have hbi : IsInvolution (q b₀) := by
    refine ⟨?_,?_⟩
    · intro he
      exact hbnc (he ▸ one_mem _)
    · have hb2 : b^2=1 := by
        let := h.elementary
        let : IsElementaryAbelian 2 ((U K).map (MulAut.conj x⁻¹).toMonoidHom) :=
          IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
        exact elemPow_eq_one_of_isElementaryAbelian b hb
      rw [← map_pow,show b₀^2=1 from Subtype.ext hb2,map_one]
  exact ⟨b₀,hb,hbi,cubic_normalizer_inverts Kstar hcK (q b₀) hbn hbnc⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
