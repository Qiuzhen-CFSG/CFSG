module

public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.SpecificGroups.SL2.TwoCore
public import Theory.SpecificGroups.SL2.OriginalSylowPair

/-!
# The original Sylow-center action in binary pushing-up

Let V be the normal closure of Ω₁(Z(P)) for a Sylow two-subgroup P of L.
If O₂(L) is self-centralizing, V is elementary and reduced. The characteristic
Sylow obstruction makes V noncentral. When L/O₂(L) is the marked SL₂(2ⁿ),
this forces C_L(V)=O₂(L). For n>1 use simplicity; for n=1, the possible
proper nontrivial quotient of S₃ has nontrivial two-core and is excluded by
reducedness. Thus the same argument retains the small field.

These are preparatory reductions for DGS85, *Groups and Graphs*, (6.3),
printed p.120. They do not assert the Baumann commutator bound or naturality.
The literal DGS (6.5) subgroup application is in
`CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.BaumannApplication.Action`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.GroupTheory.BaumannBinary
variable {G : Type*} [Group G] [Finite G]

@[expose] def centerClosure (P : Subgroup G) : Subgroup G :=
  normalClosure (omegaCenterIn P : Set G)

omit [Finite G] in
instance centerClosure_normal (P : Subgroup G) : (centerClosure P).Normal := by
  unfold centerClosure
  infer_instance

theorem centerClosure_reduced (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    IsPReduced 2 (centerClosure (P : Subgroup G)) :=
  omegaCenter_normalClosure_reduced P hc

theorem centerClosure_not_le_center (P : Sylow 2 G)
    (hP : ∀ K : Subgroup P, K.Characteristic →
      (K.map (P : Subgroup G).subtype).Normal → K = ⊥)
    (hne : (P : Subgroup G) ≠ ⊥) :
    ¬ centerClosure (P : Subgroup G) ≤ center G := by
  intro hc
  let K := (omega₁ (center P) (p := 2)).map (center P).subtype
  let : (omega₁ (center P) (p := 2)).Characteristic := omega₁_characteristic _
  let : K.Characteristic := inferInstance
  have hK : K.map (P : Subgroup G).subtype ≤ center G :=
    (show omegaCenterIn (P : Subgroup G) ≤ centerClosure (P : Subgroup G) from
      le_normalClosure).trans hc
  let : (K.map (P : Subgroup G).subtype).Normal := ⟨by
    intro z hz g
    simpa only [(mem_center_iff.mp (hK hz)) g, mul_inv_cancel_right] using hz⟩
  let : Nontrivial P := (nontrivial_iff_ne_bot _).mpr hne
  exact omega_center_ne_bot P.isPGroup' (hP K inferInstance inferInstance)

end Theory.GroupTheory.BaumannBinary

open scoped MatrixGroups
namespace Theory.GroupTheory.BaumannBinary
private theorem injective_of_card_six_of_core_free
    {D H : Type*} [Group D] [Finite D] [Group H] [Finite H] [Nontrivial H]
    (hD : Nat.card D = 6) (hcD : pCore 2 D = ⊥) (hcH : pCore 2 H = ⊥)
    (f : D →* H) (hf : Function.Surjective f) : Function.Injective f := by
  apply f.ker_eq_bot_iff.mp
  have hmul := f.ker.card_mul_index
  rw [index_ker, f.range_eq_top_of_surjective hf, card_top, hD] at hmul
  have hd : Nat.card f.ker ∣ 6 := hD ▸ f.ker.card_subgroup_dvd_card
  have hc : Nat.card f.ker ∈ Nat.divisors 6 := Nat.mem_divisors.mpr ⟨hd,by decide⟩
  have hcases : Nat.card f.ker = 1 ∨ Nat.card f.ker = 2 ∨
      Nat.card f.ker = 3 ∨ Nat.card f.ker = 6 := by
    have he : Nat.divisors 6 = {1,2,3,6} := by decide
    rw [he] at hc
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hc
  rcases hcases with h1 | h2 | h3 | h6
  · exact card_eq_one.mp h1
  · have htwo : IsPGroup 2 f.ker := IsPGroup.of_card (n := 1) (by simpa using h2)
    have hle : f.ker ≤ pCore 2 D := le_sSup ⟨inferInstance,htwo⟩
    exact bot_unique (hle.trans hcD.le)
  · have hH : Nat.card H = 2 := by rw [h3] at hmul; omega
    have htwo : IsPGroup 2 H := IsPGroup.of_card (n := 1) (by simpa using hH)
    have ht : (⊤ : Subgroup H) ≤ pCore 2 H := le_sSup ⟨inferInstance,htwo.to_subgroup ⊤⟩
    have he : (⊤ : Subgroup H) = ⊥ := le_antisymm (ht.trans hcH.le) bot_le
    have hcard := congrArg (fun K : Subgroup H => Nat.card K) he
    simp only [card_top,card_bot,hH] at hcard
    omega
  · have hH : Nat.card H = 1 := by rw [h6] at hmul; omega
    exact ((Finite.one_lt_card (α := H)).ne' hH).elim

variable {F D H : Type*} [Field F] [Finite F] [CharP F 2]
  [Group D] [Finite D] [Group H] [Finite H] [Nontrivial H]

private theorem binarySL2_injective_of_core_free
    (f : SL(2,F) →* H) (hf : Function.Surjective f) (hcH : pCore 2 H = ⊥)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) : Function.Injective f := by
  by_cases hn1 : n = 1
  · have hF2 : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
    let : Fintype F := Fintype.ofFinite F
    let eF : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hF2)).symm
    let e : SL(2,F) ≃* SL(2,ZMod 2) :=
      { toFun := Matrix.SpecialLinearGroup.map eF.toRingHom
        invFun := Matrix.SpecialLinearGroup.map eF.symm.toRingHom
        left_inv := by intro g; ext i j; exact eF.symm_apply_apply (g i j)
        right_inv := by intro g; ext i j; exact eF.apply_symm_apply (g i j)
        map_mul' := (Matrix.SpecialLinearGroup.map eF.toRingHom).map_mul }
    obtain ⟨a⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    have hc : Nat.card SL(2,F) = 6 := by
      rw [Nat.card_congr (e.trans a).toEquiv,Nat.card_perm]
      norm_num
    exact injective_of_card_six_of_core_free hc (Matrix.SL2.twoCore_eq_bot F) hcH f hf
  · have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
    let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    let : IsSimpleGroup SL(2,F) := (Theory.PSL2.sl2QuotientEquiv F).isSimpleGroup
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact f.ker_eq_bot_iff.mp hb
    · have hone : ∀ h : H, h = 1 := by
        intro h
        obtain ⟨g,rfl⟩ := hf h
        exact (show g ∈ f.ker from ht.symm ▸ mem_top g)
      obtain ⟨h,hh⟩ := exists_ne (1 : H)
      exact (hh (hone h)).elim

variable {G : Type*} [Group G] [Finite G]

theorem centerClosure_centralizer
    (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : ∀ K : Subgroup P, K.Characteristic →
      (K.map (P : Subgroup G).subtype).Normal → K = ⊥)
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    centralizer (centerClosure (P : Subgroup G) : Set G) = pCore 2 G := by
  let V := centerClosure (P : Subgroup G)
  have hr := centerClosure_reduced P hc
  let : V.Normal := hr.normal
  let C := centralizer (V : Set G)
  have hQC : pCore 2 G ≤ C := le_centralizer_iff.mp hr.le_centralizer_pCore
  have hPne : (P : Subgroup G) ≠ ⊥ := by
    intro hb
    let T := P.mapSurjective hq
    have hT : (T : Subgroup SL(2,F)) = ⊥ := by
      change (P : Subgroup G).map q = ⊥
      rw [hb,Subgroup.map_bot]
    exact Matrix.SpecialLinearGroup.no_normal_sylow F 2 T (by rw [hT]; infer_instance)
  have hCne : C ≠ ⊤ := by
    intro he
    apply centerClosure_not_le_center P hP hPne
    have hh : V ≤ centralizer ((⊤ : Subgroup G) : Set G) :=
      le_centralizer_iff.mp he.ge
    simpa only [coe_top,centralizer_univ] using hh
  let : Nontrivial (G ⧸ C) := QuotientGroup.nontrivial_iff.mpr hCne
  let f : SL(2,F) →* G ⧸ C := q.liftOfSurjective hq
    ⟨QuotientGroup.mk' C,by simpa only [QuotientGroup.ker_mk',hk] using hQC⟩
  have he (g : G) : f (q g) = QuotientGroup.mk' C g := by
    dsimp only [f]
    rw [MonoidHom.liftOfRightInverse_comp_apply]
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective C x
    exact ⟨q g,he g⟩
  have hfi := binarySL2_injective_of_core_free f hf hr.quotient_pCore_eq_bot hn hF
  apply le_antisymm ?_ hQC
  intro g hg
  rw [←hk]
  apply hfi
  rw [map_one,he]
  exact (QuotientGroup.eq_one_iff g).mpr hg

end Theory.GroupTheory.BaumannBinary
