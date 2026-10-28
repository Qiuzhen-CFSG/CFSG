module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.WreathedNormalizer.Base
public import ABG.ChapterII.Section2.QDCharacterization
public import ABG.ChapterII.Section1.WreathedFusionFrame
public import ABG.ChapterII.Section1.WreathedUHighInvolutions
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# The wreathed base normalizer moves the central involution

In a finite simple group with a wreathed Sylow subgroup, the base normalizer
induces every automorphism of the Klein four Frattini quotient. The half-exponent
power map kills the Frattini subgroup. Lift an automorphism moving two root
classes and take powers to obtain a conjugator in the literal normalizer
moving the central involution. The cyclic Sylow center identifies any supplied
central involution with the distinguished one. No matrix conjugator is assumed.

The power-map argument refines ABG.Wreathed.u_involutions_isConj by retaining
the normalizer witness, following ABG II.1 Proposition 2, article pp.12--13.
Application: Aschbacher--Smith E.1.14(7), printed p.214.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.WreathedNormalizer

private theorem power_kills_frattini
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (hA : IsPGroup 2 A) (k : ℕ) (hk : ∀ a : A, a ^ (2*k) = 1) :
    frattini A ≤ (powMonoidHom k : A →* A).ker := by
  let : Fact (IsPGroup 2 A) := ⟨hA⟩
  rw [frattini_eq_closure_commutator_union_powers (p := 2)]
  apply (Subgroup.closure_le _).mpr
  rintro a (ha | ⟨b, rfl⟩)
  · have hc : _root_.commutator A = ⊥ := by
      rw [commutator_eq_bot_iff_center_eq_top]
      exact Subgroup.center_eq_top
    rw [hc] at ha
    have ha' : a = 1 := ha
    simp [ha']
  · change (b ^ 2) ^ k = 1
    rw [← pow_mul]
    exact hk b

private theorem quotient_action_normalizer_conj
    {G : Type*} [Group G] [Finite G] (U : Subgroup G)
    [IsMulCommutative U] [IsKleinFour (U ⧸ frattini U)]
    (hU : IsPGroup 2 U) (k : ℕ) (hk : ∀ a : U, a ^ (2*k) = 1)
    (hfull : Function.Surjective
      ((Subgroup.quotientAut (frattini U)).comp U.normalizerMonoidHom))
    (x y a b : U) (hx : x ≠ 1) (hy : y ≠ 1)
    (ha : a ^ k = x) (hb : b ^ k = y) : ∃ g : Subgroup.normalizer (U : Set G), (g : G) * (x : G) * (g : G)⁻¹ = (y : G) := by
  classical
  let f := QuotientGroup.lift (frattini U) (powMonoidHom k : U →* U)
    (power_kills_frattini hU k hk)
  let qa := QuotientGroup.mk' (frattini U) a
  let qb := QuotientGroup.mk' (frattini U) b
  have hfa : f qa = x := ha
  have hfb : f qb = y := hb
  have hqa : qa ≠ 1 := by
    intro h
    apply hx
    rw [← hfa, h, map_one]
  have hqb : qb ≠ 1 := by
    intro h
    apply hy
    rw [← hfb, h, map_one]
  let alpha : MulAut (U ⧸ frattini U) :=
    IsKleinFour.mulEquiv (Equiv.swap qa qb)
      (Equiv.swap_apply_of_ne_of_ne hqa.symm hqb.symm)
  have halpha : alpha qa = qb := Equiv.swap_apply_left qa qb
  obtain ⟨g, hg⟩ := hfull alpha
  have hq : QuotientGroup.mk' (frattini U) (U.normalizerMonoidHom g a) = qb := by
    have h := DFunLike.congr_fun hg qa
    change (Subgroup.quotientAut (frattini U) (U.normalizerMonoidHom g))
      (QuotientGroup.mk' (frattini U) a) = alpha qa at h
    simpa only [Subgroup.quotientAut_apply_mk, halpha] using h
  have hp := congrArg f hq
  have hxy : U.normalizerMonoidHom g x = y := by
    change (U.normalizerMonoidHom g a) ^ k = f qb at hp
    rw [← map_pow, ha, hfb] at hp
    exact hp
  exact ⟨g, congrArg Subtype.val hxy⟩

private theorem base_period {S : Type*} [Group S] {n : ℕ}
    (P : ABG.Wreathed.Presentation S n) (a : P.U) : a ^ (2 ^ n) = 1 := by
  apply P.baseEquiv.injective
  rw [map_pow, map_one]
  apply Prod.ext
  · simpa using (pow_card_eq_one' (x := (P.baseEquiv a).1))
  · simpa using (pow_card_eq_one' (x := (P.baseEquiv a).2))

/-- In a simple group, the actual normalizer of a wreathed Sylow base moves
its central involution. The full Frattini action supplies the conjugator. -/
theorem presentation_normalizer_moves {K : Type*} [Group K] [Finite K]
    [IsSimpleGroup K] (S : Sylow 2 K) {n : ℕ} (P : ABG.Wreathed.Presentation S n)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S) :
    ¬ normalizer (P.U.map (S : Subgroup K).subtype : Set K) ≤
      centralizer ({(z : K)} : Set K) := by
  let : IsCyclic (center S) := P.center_cyclic
  have hzP : z = P.x := congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨z, hzc⟩ : center S)) (y := ⟨P.x, P.x_mem_center⟩)
    (by simpa only [orderOf_mk] using hz)
    (by simpa only [orderOf_mk] using P.x_orderOf))
  rw [hzP]
  let U := P.U.map (S : Subgroup K).subtype
  have hf := P.fusionFrame S
  have hno : ABG.HasNoNormalIndexTwoSubgroup K := by
    intro D hDn hDi
    rcases hDn.eq_bot_or_eq_top with rfl | rfl
    · rw [index_bot] at hDi
      have hdvd := (S : Subgroup K).card_subgroup_dvd_card
      rw [P.card, hDi] at hdvd
      have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
      have hlt : 2 ^ 1 < 2 ^ (2 * n + 1) :=
        Nat.pow_lt_pow_right (by decide) (by have := P.height; omega)
      norm_num at hlt
      omega
    · simp at hDi
  have hQD := ABG.wreathed_qdPattern_of_no_normal_index_two S n _ _ hf hno
  let := (ABG.Wreathed.u_frattini_action S n _ _ hf).1
  have hfull := ABG.Wreathed.u_frattini_action_surjective S n _ _ hf hQD.2.2.1
  let : IsMulCommutative P.U := P.abelian_maximal_unique.1
  let : IsMulCommutative U := inferInstance
  let e : P.U ≃* U := P.U.equivMapOfInjective (S : Subgroup K).subtype
    (S : Subgroup K).subtype_injective
  have hs : P.s ∈ P.U := subset_closure (by simp)
  have ht : P.t ∈ P.U := subset_closure (by simp)
  have hu : P.u ∈ P.U := P.U.mul_mem hs ht
  have hx : P.x ∈ P.U := P.U.pow_mem hu _
  have hx₂ : P.x₂ ∈ P.U := P.U.pow_mem hs _
  let x : U := e ⟨P.x, hx⟩
  let y : U := e ⟨P.x₂, hx₂⟩
  let a : U := e ⟨P.u, hu⟩
  let b : U := e ⟨P.s, hs⟩
  have hU : IsPGroup 2 U := (S.isPGroup'.to_subgroup P.U).of_equiv e
  have hk : ∀ c : U, c ^ (2 * 2 ^ (n - 1)) = 1 := by
    intro c
    apply e.symm.injective
    rw [map_pow, map_one]
    have hpow : 2 * 2 ^ (n - 1) = 2 ^ n := by
      rw [Nat.mul_comm, ← pow_succ]
      congr 1
      have := P.height
      omega
    rw [hpow]
    exact base_period P _
  obtain ⟨g, hg⟩ := quotient_action_normalizer_conj U hU (2 ^ (n - 1)) hk hfull x y a b
    (by intro he
        have hh : P.x = 1 := congrArg Subtype.val (e.injective
          (he.trans (map_one e).symm))
        have ho := P.x_orderOf
        simp [hh] at ho)
    (by intro he; have hh : P.x₂ = 1 := congrArg Subtype.val (e.injective
          (he.trans (map_one e).symm)); exact P.x₂_ne_one hh)
    (by change e (⟨P.u, hu⟩ : P.U) ^ _ = _; rw [← map_pow]; rfl)
    (by change e (⟨P.s, hs⟩ : P.U) ^ _ = _; rw [← map_pow]; rfl)
  intro hcent
  have hc := mem_centralizer_singleton_iff.mp (hcent g.property)
  change (g : K) * (P.x : K) * (g : K)⁻¹ = (P.x₂ : K) at hg
  rw [hc, mul_assoc, mul_inv_cancel, mul_one] at hg
  exact P.x_not_isConj_x₂ (isConj_iff.mpr
    ⟨1, by simpa using (show P.x = P.x₂ from Subtype.ext hg)⟩)

/-- The movement contract is discharged for the specified unitary models;
the companion Solvability module supplies its matrix calculation. -/
theorem intrinsicMovement_of_isPSU {K : Type*} [Group K] [Finite K] [IsSimpleGroup K]
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hmod : p % 4 = 3)
    (hmodel : ClassicalGroup.IsPSU K 3 p) : IntrinsicMovement K := by
  intro S A ha hi z hz hzc
  obtain ⟨n, hn⟩ := isPSU_sylow_wreathed hp hodd hmod hmodel S
  obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation hn
  have he : A = P.U := P.abelian_eq_U_of_card_eq A ha (by
    have hA := A.card_mul_index
    have hU := P.U.card_mul_index
    rw [hi] at hA
    rw [P.index_U] at hU
    omega)
  rw [he]
  exact presentation_normalizer_moves S P z hz hzc
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.WreathedNormalizer
