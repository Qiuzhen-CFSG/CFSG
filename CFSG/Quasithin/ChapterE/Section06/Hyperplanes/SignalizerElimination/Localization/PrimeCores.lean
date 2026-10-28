module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination.Localization.Inversion
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination.Globalization
public import Theory.GroupTheory.PCoreImage

/-!
# The local prime-core identity (*)

Completeness identifies X ∩ C_G(A) with O(C_G(A)). Restriction of O_p(X)
to that odd core is contained in O_p(C_G(A)); abelianness of X gives the
reverse containment. The valid coprime fixed-point generation theorem,
applied to the actual conjugation action of V on O_p(X), then generates
O_p(X) by the prime cores of the hyperplane centralizers above U₀.
The whole-actor fixed term vanishes by the earlier characteristic-two input.

All normality assertions are relative to the named subgroup. The argument
includes O_p(X)=1 and uses no direct-sum claim from the misprinted A.1.17.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.20,
printed p.253 (PDF p.264), identity (*).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U₀ : Subgroup G}

omit [Finite G] in
private theorem le_pCoreIn_of_abelian {p : ℕ} {P X : Subgroup G}
    [IsMulCommutative X] (hPX : P ≤ X) (hp : IsPGroup p P) : P ≤ X.pCoreIn p :=
  le_pCoreIn_of_normalizes hp hPX
    ((X.le_centralizer.trans (Subgroup.centralizer_le hPX)).trans (Subgroup.centralizer_le_normalizer _))

/-- Completeness restricts the prime core of X to the exact centralizer prime
core. Normality in this calculation is always relative to its displayed group. -/
theorem localOddClosure_pCoreIn_inter_eq
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hcpl : CompletedLocalOddClosure V) (hUV : U₀ ≤ V)
    (hcor : subgroupCorank V U₀ = 3)
    (p : ℕ) [Fact p.Prime] (hp : Odd p)
    {A : Subgroup G} (hUA : U₀ < A) (hAV : A ≤ V) :
    (localOddClosure V U₀).pCoreIn p ⊓ centralizer (A : Set G) =
      primeCentralizer p A := by
  let _ := localOddClosure_isMulCommutative h earlier hcpl hUV hcor
  have hAX := oddCentralizer_le_localOddClosure hUA hAV
  apply le_antisymm
  · have hQO : (localOddClosure V U₀).pCoreIn p ⊓ centralizer (A : Set G) ≤
        oddCentralizer A := by
      rw [← (hcpl U₀ hUV hcor).2 A hUA hAV]
      exact inf_le_inf (pCoreIn_le p _) le_rfl
    exact ((le_inf hQO inf_le_left).trans (inf_pCoreIn_le_of_le p hAX)).trans
      (pCoreIn_mono_of_normalizes (oddCentralizer_le A)
        (centralizer_le_normalizer_oddCentralizer A))
  · exact le_inf (le_pCoreIn_of_abelian
      ((primeCentralizer_le_oddCentralizer p hp A).trans hAX)
      (isPGroup_pCoreIn p _)) (pCoreIn_le p _)

private theorem cyclic_corank_le_one [IsElementaryAbelian 2 V]
    (B : Subgroup V) (hB : IsCyclic (V ⧸ B)) :
    subgroupCorank V (B.map V.subtype) ≤ 1 := by
  let _ := hB
  have hd : Nat.card (V ⧸ B) ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 (V ⧸ B)
  have hrel : (B.map V.subtype).relIndex V = Nat.card (V ⧸ B) := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf, Subgroup.comap_map_eq,
      V.ker_subtype, sup_bot_eq, Subgroup.index_eq_card]
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
  rw [← hrel, Subgroup.relIndex_eq_two_pow_quotient_finrank V,
    ← subgroupCorank_eq_quotient_finrank] at hle
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by simpa using hle)

omit [Finite G] in
/-- A proper decrease in corank makes a containing subspace strictly larger. -/
theorem lt_of_corank_lt {A : Subgroup G}
    (hUA : U₀ ≤ A) (hcor : subgroupCorank V A < subgroupCorank V U₀) : U₀ < A := by
  exact lt_of_le_of_ne hUA (fun he => by rw [he] at hcor; exact (lt_irrefl _ hcor))

/-- The odd-prime cores of C_G(V) vanish by the actual characteristic-two input. -/
theorem primeCentralizer_V_eq_bot
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (p : ℕ) [Fact p.Prime] (hp : Odd p) : primeCentralizer p V = ⊥ := by
  obtain ⟨z, hz, hne⟩ := Components.exists_sylow_fixed h
  exact le_bot_iff.mp ((primeCentralizer_le_oddCentralizer p hp V).trans_eq
    (oddCentralizer_eq_bot_of_sylow_fixed h earlier hz hne le_rfl hz.1))

/-- Identity (*) of E.6.20, including primes that do not divide |X|.
Only the valid coprime generation clause is used. -/
theorem localPrimeClosure_eq_pCoreIn
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hcpl : CompletedLocalOddClosure V) (hUV : U₀ ≤ V)
    (hcor : subgroupCorank V U₀ = 3)
    (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    localPrimeClosure p V U₀ = (localOddClosure V U₀).pCoreIn p := by
  let _ := h.elementary
  let X := localOddClosure V U₀
  let P := X.pCoreIn p
  have hn : V ≤ normalizer (P : Set G) :=
    le_normalizer_localOddClosure.trans (normalizer_le_normalizer_characteristic_image X (pCore p X))
  have hPU : P ≤ centralizer (U₀ : Set G) := (pCoreIn_le p X).trans (localOddClosure_le V U₀)
  have hfixed := fun A hUA hAV =>
    localOddClosure_pCoreIn_inter_eq h earlier hcpl hUV hcor p hp (A := A) hUA hAV
  apply le_antisymm
  · refine iSup_le fun W => ?_
    have hUW : U₀ < W.val := lt_of_corank_lt W.property.1 (by rw [hcor, W.property.2.2]; decide)
    rw [← hfixed W.val hUW W.property.2.1]
    exact inf_le_left
  · let act : V →* MulAut P := P.normalizerMonoidHom.comp (inclusion hn)
    let _ : MulDistribMulAction V P := MulDistribMulAction.compHom P act
    let _ : Fact (IsPGroup 2 V) := ⟨IsElementaryAbelian.isPGroup 2 V⟩
    have hcop : Nat.Coprime 2 (Nat.card P) := by
      obtain ⟨n, hn⟩ := (isPGroup_pCoreIn p X).exists_card_eq
      rw [hn]
      exact hp.pow.coprime_two_left
    have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup_action
      (G := P) (A := V) 2 hcop
    have htop : (⊤ : Subgroup P) ≤ (localPrimeClosure p V U₀).comap P.subtype := by
      rw [← hgen]
      refine iSup₂_le fun B hB y hy => ?_
      let W := U₀ ⊔ B.map V.subtype
      have hWV : W ≤ V := sup_le hUV (map_subtype_le B)
      have hWc : subgroupCorank V W ≤ 1 :=
        (subgroupCorank_antitone (show B.map V.subtype ≤ W from le_sup_right)).trans
          (cyclic_corank_le_one B hB)
      have hUW : U₀ < W := lt_of_corank_lt le_sup_left (by rw [hcor]; omega)
      have hcentral : (y : G) ∈ centralizer (W : Set G) := by
        have hW : W ≤ centralizer ({(y : G)} : Set G) := by
          apply sup_le
          · intro u hu
            exact mem_centralizer_singleton_iff.mpr ((hPU y.property) u hu)
          · rintro b ⟨a, ha, rfl⟩
            have he := (show ∀ a : B, a • y = y from hy) ⟨a, ha⟩
            have he' : (a : G) * (y : G) * (a : G)⁻¹ = (y : G) := congrArg Subtype.val he
            exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he')
        intro w hw
        exact mem_centralizer_singleton_iff.mp (hW hw)
      have hyW : (y : G) ∈ primeCentralizer p W := hfixed W hUW hWV ▸ ⟨y.property, hcentral⟩
      change (y : G) ∈ localPrimeClosure p V U₀
      by_cases h0 : subgroupCorank V W = 0
      · have heq : W = V := le_antisymm hWV ((corank_eq_zero_iff W).mp h0)
        rw [heq, primeCentralizer_V_eq_bot h earlier p hp, mem_bot] at hyW
        exact hyW ▸ (localPrimeClosure p V U₀).one_mem
      · exact (le_iSup (fun A : {A : Subgroup G // U₀ ≤ A ∧ IsHyperplane V A} =>
          primeCentralizer p A.val) ⟨W, le_sup_left, hWV, by omega⟩) hyW
    intro y hy
    exact htop (mem_top (⟨y, hy⟩ : P))

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination
