module
public import Theory.SpecificGroups.PSL2.ThreeInvolutionGeneration
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.SmallPrimes
public import Theory.SpecificGroups.PSL2.BinaryTwentyFiveRatio
public import Theory.Representation.BinaryOffender.CubicConjugateBound
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.FrobeniusExclusions
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.MovedFixed
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.InnerModels
/-!
# The odd-prime parameter bound on the original C.5.13 moved dual

The source moved dual has no full fixed vectors and is faithful. Three
conjugates of an inner involution generate PSL₂(p) when p>25. Dihedral
Sylow groups and cubic ratio at most two then bound its degree by twelve,
whereas the actual Borel Frobenius subgroup forces degree at least (p−1)/2.
The resulting bound p≤25 retains the original dual and all central layers;
no irreducibility or outer-action hypothesis is assumed.
Source: Aschbacher–Smith C.5.13, printed p.163, and K.2, printed p.453.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
theorem prime_bound_of_fixed_cubic {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hfix : fixedSpace ρ ⊤ = ⊥) (hq : cubicRatio ρ ≤ 2)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL G 2 p) : p ≤ 25 := by
  by_contra! hlarge
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  have hr : primeRank 2 G ≤ 2 := by
    rw [primeRank_equiv 2 e]
    let P : Sylow 2 PSL(2,F) := Classical.choice inferInstance
    have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
      ⟨p,1,hp,ho,by decide,by simpa using hF⟩
    obtain ⟨n,_,⟨en⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd P
    rw [P.primeRank_eq,primeRank_equiv 2 en]
    exact dihedral_rank_le_two n
  obtain ⟨t,ht,ht2,hd⟩ := exists_small_involution_of_cubicRatio_le ρ hr hq
  obtain ⟨c,hc⟩ := Theory.PSL2.exists_three_involution_conjugates ho (Or.inl rfl : 1=1 ∨ 1=2)
    (by simpa using hF) (by simpa using hlarge) (e t)
    (fun he => ht (e.injective (he.trans e.map_one.symm))) (by simpa only [← map_pow,map_one] using congrArg e ht2)
  let d : Fin 3 → G := fun i => e.symm (c i)
  have hg : (⊤ : Subgroup G) ≤ closure (Set.range fun i => d i*t*(d i)⁻¹) := by
    have hz : closure (Set.range fun i => c i * e t * (c i)⁻¹) ≤
        (closure (Set.range fun i => d i*t*(d i)⁻¹)).comap e.symm.toMonoidHom := by
      apply (closure_le _).mpr
      rintro _ ⟨i,rfl⟩
      change e.symm (c i * e t * (c i)⁻¹) ∈ closure (Set.range fun j => d j*t*(d j)⁻¹)
      rw [map_mul,map_mul,map_inv,MulEquiv.symm_apply_apply]
      exact subset_closure ⟨i,rfl⟩
    intro g _
    have hh := hz (show e g ∈ closure (Set.range fun i => c i * e t * (c i)⁻¹) from hc ▸ mem_top _)
    change e.symm (e g) ∈ closure (Set.range fun j => d j*t*(d j)⁻¹) at hh
    simpa only [MulEquiv.symm_apply_apply] using hh
  have hdim : Module.finrank (ZMod 2) V ≤ 12 :=
    (finrank_le_mul_fixedCodim_of_conjugate_generation ρ ⊤ hfix t d hg).trans
      (Nat.mul_le_mul_left 3 hd)
  have hlo := ChapterG.Section07.OddCharacteristic.psl2_frobenius_degree_bound ρ hf ho
    (show ClassicalGroup.IsPSL G 2 p from ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩)
  obtain ⟨k,hk⟩ := ho
  omega


open Stellmacher ConjugateSource ConjugateSource.RankOne
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem natural_not_three {K : Subgroup G} {n : ℕ} (hn : IsL2EvenBlock K n) :
    ¬ IsAlternatingBlock K 3 := by
  intro h3
  obtain ⟨F,_,_,hF,_,hm⟩ := hn.2.2
  obtain ⟨e⟩ := hm.quotient_iso
  obtain ⟨e3⟩ := h3.2.2.quotient_iso
  have hc : Nat.card (K ⧸ pCore 2 K) = 3 := by
    rw [Nat.card_congr e3.toEquiv,Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  have hle := Nat.card_le_card_of_injective (Matrix.SpecialLinearGroup.upperUnipotentHom F)
    (Matrix.SpecialLinearGroup.upperUnipotentHom_injective F)
  change Nat.card F ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) at hle
  rw [← Nat.card_congr e.toEquiv,hF,hc] at hle
  have hlo : 4 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn.1
  omega
omit [Finite G] in
private theorem alternating_not_three {K : Subgroup G} (h : IsAlternatingBlock K 5) :
    ¬ IsAlternatingBlock K 3 := by
  intro h3
  obtain ⟨e5⟩ := h.2.2.quotient_iso
  obtain ⟨e3⟩ := h3.2.2.quotient_iso
  have hc := Nat.card_congr (e5.symm.trans e3).toEquiv
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  have hthree : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  rw [h5,hthree] at hc
  norm_num at hc

/-- The original natural source marking bounds the actual odd-prime component parameter. -/
theorem natural_source_moved_prime_bound {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    ∀ p : ℕ, p.Prime → Odd p →
      ClassicalGroup.IsPSL (closureImage (V.subgroupOf N) (K.subgroupOf N)) 2 p → p ≤ 25 := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  have hf := (noncubic_source_moved_faithful K T X (Or.inl ⟨n,hn⟩) (natural_not_three hn) hT (h.module_le.trans inf_le_left) hTK P hP hA hAX S hS).2
  have hfix := noncubic_source_moved_dual_fixed K T X (Or.inl ⟨n,hn⟩) (natural_not_three hn) hT (h.module_le.trans inf_le_left) hTK P hP hA hAX S hS
  have hq := natural_source_moved_dual_ratio h hn hT hTK P hP X hA hAX hx hnc
  change ∀ p : ℕ, p.Prime → Odd p →
    ClassicalGroup.IsPSL (closureImage (V.subgroupOf N) (K.subgroupOf N)) 2 p → p ≤ 25
  intro p hp ho hm
  exact prime_bound_of_fixed_cubic _ hf hfix ((cubicRatio_le_quadraticRatio _).trans hq) hp ho hm

/-- The original A₅ source marking bounds the actual odd-prime component parameter. -/
theorem alternating_source_moved_prime_bound {K T L : Subgroup G}
    (h : AlternatingPairSetup T K L) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := alternating_five_source_omega_span h hTK P hP X hA hAX
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    ∀ p : ℕ, p.Prime → Odd p →
      ClassicalGroup.IsPSL (closureImage (V.subgroupOf N) (K.subgroupOf N)) 2 p → p ≤ 25 := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := alternating_five_source_omega_span h hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  have hf := (noncubic_source_moved_faithful K T X (Or.inr (Or.inr h.block)) (alternating_not_three h.block) h.twoGroup (h.module_le.trans inf_le_left) hTK P hP hA hAX S hS).2
  have hfix := noncubic_source_moved_dual_fixed K T X (Or.inr (Or.inr h.block)) (alternating_not_three h.block) h.twoGroup (h.module_le.trans inf_le_left) hTK P hP hA hAX S hS
  have hq := alternating_source_moved_dual_ratio h hTK P hP X hA hAX hx hnc
  change ∀ p : ℕ, p.Prime → Odd p →
    ClassicalGroup.IsPSL (closureImage (V.subgroupOf N) (K.subgroupOf N)) 2 p → p ≤ 25
  intro p hp ho hm
  exact prime_bound_of_fixed_cubic _ hf hfix ((cubicRatio_le_quadraticRatio _).trans hq) hp ho hm


/-- The source exceptional-prime congruences leave no fixed-free faithful cubic actor. -/
theorem not_exceptional_prime_of_fixed_cubic {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hfix : fixedSpace ρ ⊤ = ⊥) (hq : cubicRatio ρ ≤ 2)
    {p : ℕ} (hp : Chapter1.Section02.A312ExceptionalPrime p) :
    ¬ ClassicalGroup.IsPSL D 2 p := by
  intro hm
  have hb := prime_bound_of_fixed_cubic ρ hf hfix hq hp.1 hp.2.1 hm
  have hc : p=11 ∨ p=19 := by
    have arithmetic : ∀ i : Fin 26, i.val.Prime → i.val^2 % 5=1 →
        i.val=11 ∨ i.val=19 := by decide
    exact arithmetic ⟨p,by omega⟩ hp.1 hp.2.2.1
  rcases hc with rfl | rfl
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact (not_lt_of_ge hq) (Theory.PSL2.two_lt_cubicRatio_of_eleven_fixed ρ hf hfix hF e)
  · exact (not_lt_of_ge hq) (two_lt_cubicRatio_of_nineteen_fixed ρ hf hfix hm)

/-- The original natural source excludes every exceptional odd-prime actor. -/
theorem natural_source_moved_not_exceptional_prime {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    ∀ p : ℕ, Chapter1.Section02.A312ExceptionalPrime p →
      ¬ ClassicalGroup.IsPSL (closureImage (V.subgroupOf N) (K.subgroupOf N)) 2 p := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  have hf := (noncubic_source_moved_faithful K T X (Or.inl ⟨n,hn⟩) (natural_not_three hn) hT (h.module_le.trans inf_le_left) hTK P hP hA hAX S hS).2
  have hfix := noncubic_source_moved_dual_fixed K T X (Or.inl ⟨n,hn⟩) (natural_not_three hn) hT (h.module_le.trans inf_le_left) hTK P hP hA hAX S hS
  have hq := natural_source_moved_dual_ratio h hn hT hTK P hP X hA hAX hx hnc
  change ∀ p : ℕ, Chapter1.Section02.A312ExceptionalPrime p →
    ¬ ClassicalGroup.IsPSL (closureImage (V.subgroupOf N) (K.subgroupOf N)) 2 p
  intro p hp
  exact not_exceptional_prime_of_fixed_cubic _ hf hfix
    ((cubicRatio_le_quadraticRatio _).trans hq) hp

/-- The original A₅ source excludes every exceptional odd-prime actor. -/
theorem alternating_source_moved_not_exceptional_prime {K T L : Subgroup G}
    (h : AlternatingPairSetup T K L) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := alternating_five_source_omega_span h hTK P hP X hA hAX
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    ∀ p : ℕ, Chapter1.Section02.A312ExceptionalPrime p →
      ¬ ClassicalGroup.IsPSL (closureImage (V.subgroupOf N) (K.subgroupOf N)) 2 p := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := alternating_five_source_omega_span h hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  have hf := (noncubic_source_moved_faithful K T X (Or.inr (Or.inr h.block)) (alternating_not_three h.block) h.twoGroup (h.module_le.trans inf_le_left) hTK P hP hA hAX S hS).2
  have hfix := noncubic_source_moved_dual_fixed K T X (Or.inr (Or.inr h.block)) (alternating_not_three h.block) h.twoGroup (h.module_le.trans inf_le_left) hTK P hP hA hAX S hS
  have hq := alternating_source_moved_dual_ratio h hTK P hP X hA hAX hx hnc
  change ∀ p : ℕ, Chapter1.Section02.A312ExceptionalPrime p →
    ¬ ClassicalGroup.IsPSL (closureImage (V.subgroupOf N) (K.subgroupOf N)) 2 p
  intro p hp
  exact not_exceptional_prime_of_fixed_cubic _ hf hfix
    ((cubicRatio_le_quadraticRatio _).trans hq) hp
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
