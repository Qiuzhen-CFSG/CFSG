module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicPair
public import Theory.GroupAction.FrattiniFixedGeneration
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct

/-!
# The fixed-layer and elementary-square exclusions in 12.2.23

Set Φ to the literal image of the Frattini subgroup of P. Coprime fixed-point
generation on C_W(Φ) supplies factors centralized by cyclic-quotient
preimages. Noncyclicity and Φ = P ∩ N_G(L) force each preimage to escape
N_G(L). NoEscape therefore makes its fixed factor disjoint from V.
The inverter fixes that factor; inversion modulo Φ and coprime splitting
then make it trivial. Consequently C_W(Φ) = 1.

The elementary-square case has Φ = 1 and is excluded by the nonzero order
of the pair core U. The surviving extraspecial case has W = [W,Φ].
The numerical reduction and binary-three module/core argument remain separate
source obligations. No cyclicity or irreducibility conclusion is assumed here.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
12.2.22--23, printed pp.803--804 (the fixed-layer paragraph on p.803).
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U W : Subgroup G} {d p : ℕ} {g v : G}
namespace InvariantOddLocalAnalysis
variable (S : InvariantOddLocalAnalysis T L V d p H P U W g v)
include S

omit [Finite G] in
private theorem odd_normalizes_module : P ≤ normalizer (W : Set G) := by
  apply le_trans _ S.normalizes
  rw [S.overgroup]
  exact le_sup_left

/-- The noncyclic odd subgroup has no fixed points on W under Φ(P). -/
theorem frattini_fixed_eq_bot_of_noncyclic
    (D : ChosenModule T L V) (hnone : NoEscape L V) (hnc : ¬ IsCyclic P) :
    W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ := by
  let : Fact p.Prime := ⟨S.prime⟩
  let : Fact (IsPGroup p P) := ⟨S.pgroup⟩
  let : IsElementaryAbelian 2 W := S.elementary
  let Φ := (frattini P).map P.subtype
  let F := W ⊓ centralizer (Φ : Set G)
  let E := P ⧸ frattini P
  let q := QuotientGroup.mk' (frattini P)
  let : IsElementaryAbelian p E := isElementaryAbelian_quotient_frattini
  have hPΦ : P ≤ normalizer (Φ : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (frattini P))
  have hPF : P ≤ normalizer (F : Set G) :=
    (le_inf S.odd_normalizes_module
      (hPΦ.trans (normalizer_le_normalizer_centralizer Φ))).trans
      inf_normalizer_le_normalizer_inf
  let : Normalizes P F := ⟨hPF⟩
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le (show F ≤ W from inf_le_left)
  let : Fact (IsPGroup 2 F) := ⟨IsElementaryAbelian.isPGroup 2 F⟩
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := S.pgroup.exists_card_eq
    rw [hn]
    exact S.odd_prime.pow
  have hcop : Nat.Coprime (Nat.card P) (Nat.card W) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr hodd).pow_right n
  have hfixed : W ⊓ centralizer (P : Set G) = ⊥ := by
    have hd := commutator_disjoint_centralizer_of_coprime W P S.odd_normalizes_module hcop
    rw [S.moved] at hd
    simpa only [← inf_assoc, inf_idem] using disjoint_iff.mp hd
  have hphi : frattini P ≤ (MulDistribMulAction.toMulAut P F).ker := by
    intro a ha
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (a : G) * (x : G) * (a : G)⁻¹ = (x : G)
    have he := x.property.2 (a : G) (mem_map_of_mem P.subtype ha)
    rw [he, mul_inv_cancel_right]
  have hg := iSup_frattini_fixedPoints_cyclicQuot_eq_top
    (q := 2) (A := P) (X := F) (Nat.coprime_two_right.mpr hodd) hphi
  have hfactor (Y : Subgroup E) (hc : IsCyclic (E ⧸ Y)) :
      FixedPoints.subgroup (Y.comap q) F = ⊥ := by
    let B₀ := Y.comap q
    let B := B₀.map P.subtype
    let X := W ⊓ centralizer (B : Set G)
    have hBP : B ≤ P := map_subtype_le _
    have hΦB : Φ ≤ B := map_mono (by
      intro a ha
      change q a ∈ Y
      have he : q a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
      rw [he]
      exact Y.one_mem)
    have hout : ¬ B ≤ normalizer (L : Set G) := by
      intro hBM
      have hBΦ : B ≤ Φ := by
        change B ≤ (frattini P).map P.subtype
        rw [S.frattini_intersection]
        exact le_inf hBP hBM
      have hB₀Φ : B₀ ≤ frattini P := (map_le_map_iff_of_injective P.subtype_injective).mp hBΦ
      have hYbot : Y = ⊥ := by
        rw [← map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Y]
        exact bot_unique (by
          simpa only [q, B₀, QuotientGroup.map_mk'_self] using map_mono (f := q) hB₀Φ)
      have : IsCyclic E := by
        let : IsCyclic (E ⧸ (⊥ : Subgroup E)) := hYbot ▸ hc
        exact (QuotientGroup.quotientBot : E ⧸ (⊥ : Subgroup E) ≃* E).isCyclic.mp inferInstance
      exact hnc (isCyclic_of_isCyclic_frattini_quotient (P := P))
    have hPB : P ≤ normalizer (B : Set G) := by
      have : B₀.Normal := inferInstance
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, P.range_subtype] using
        (le_normalizer_map (H := B₀) P.subtype)
    have hPX : P ≤ normalizer (X : Set G) :=
      (le_inf S.odd_normalizes_module
        (hPB.trans (normalizer_le_normalizer_centralizer B))).trans
        inf_normalizer_le_normalizer_inf
    have hvB : v ∈ normalizer (B : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      change B.map (MulAut.conj v).toMonoidHom = B
      apply eq_of_le_of_card_ge
      · rintro b ⟨a, ha, rfl⟩
        have hh := B.mul_mem (hΦB (S.inverts_frattini_quotient a (hBP ha))) (B.inv_mem ha)
        change v * a * v⁻¹ ∈ B
        simpa only [mul_inv_cancel_right] using hh
      · exact (show Nat.card (B.map (MulAut.conj v).toMonoidHom) = Nat.card B from
          card_map_of_injective (MulAut.conj v).injective).ge
    have hTH : (T : Subgroup G) ≤ H := by
      rw [S.overgroup]
      exact le_sup_right
    have hvW : v ∈ normalizer (W : Set G) :=
      S.normalizes (hTH (D.le_sylow S.inverter_mem))
    have hvX : v ∈ normalizer (X : Set G) :=
      inf_normalizer_le_normalizer_inf ⟨hvW, normalizer_le_normalizer_centralizer B hvB⟩
    have hXV : X ⊓ V = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      by_contra hx1
      have hxne : x ≠ 1 := by simpa only [mem_bot] using hx1
      apply hout
      intro b hb
      apply hnone x hx.2 hxne
      apply mem_centralizer_singleton_iff.mpr
      exact hx.1.2 b hb
    have hvCX : v ∈ centralizer (X : Set G) := by
      have hd : ⁅X, zpowers v⁆ ≤ X ⊓ V := by
        apply le_inf
        · exact le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hvX)
        · exact (commutator_mono inf_le_left (zpowers_le.mpr S.inverter_mem)).trans
            (S.transvections.le.trans inf_le_right)
      have hb : ⁅X, zpowers v⁆ = ⊥ := bot_unique (hXV ▸ hd)
      exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb) (mem_zpowers v)
    have hPCX : P ≤ centralizer (X : Set G) :=
      odd_centralizes_of_centralizing_inverter P X hodd v hPX hvCX (by
        intro a ha
        exact le_centralizer_iff.mp (inf_le_right : X ≤ centralizer (B : Set G))
          (hΦB (S.inverts_frattini_quotient a ha)))
    have hXbot : X = ⊥ := bot_unique (hfixed ▸
      le_inf (show X ≤ W from inf_le_left) (le_centralizer_iff.mp hPCX))
    apply eq_bot_iff.mpr
    intro x hx
    have hxB : (x : G) ∈ centralizer (B : Set G) := by
      rintro b ⟨a, ha, rfl⟩
      have he := congrArg (fun y : F => (y : G)) (hx (⟨a, ha⟩ : B₀))
      change (a : G) * (x : G) * (a : G)⁻¹ = x at he
      exact mul_inv_eq_iff_eq_mul.mp he
    have hx1 : (x : G) = 1 := by
      have hh : (x : G) ∈ X := ⟨x.property.1, hxB⟩
      simpa only [hXbot, mem_bot] using hh
    exact mem_bot.mpr (Subtype.ext hx1)
  have hFbot : (⊤ : Subgroup F) = ⊥ := by
    rw [← hg]
    exact bot_unique (iSup₂_le fun Y hY => (hfactor Y hY).le)
  apply eq_bot_iff.mpr
  intro x hx
  have he : (⟨x, hx⟩ : F) ∈ (⊥ : Subgroup F) := hFbot ▸ mem_top _
  exact congrArg Subtype.val (mem_bot.mp he)

omit [Finite G] in
/-- The nonprime alternatives cannot themselves be cyclic. -/
theorem noncyclic_of_card_ne_prime (hne : Nat.card P ≠ p) : ¬ IsCyclic P := by
  intro hc
  let : IsCyclic P := hc
  have hpdiv : p ∣ Nat.card P := S.generator_order ▸ P.orderOf_dvd_natCard S.generator_mem
  apply hne
  rcases S.alternatives with he | ⟨he, _⟩ | ⟨_, _, he⟩
  · exact he
  · let : IsElementaryAbelian p P := he
    exact Nat.dvd_antisymm (hc.exponent_eq_card ▸ IsElementaryAbelian.exponent_dvd_p p P) hpdiv
  · exact hc.exponent_eq_card.symm.trans he

/-- After the fixed-layer argument, only the extraspecial alternative survives. -/
theorem extraspecial_of_card_ne_prime
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hnone : NoEscape L V) (hne : Nat.card P ≠ p) :
    IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧ Monoid.exponent P = p ∧
      W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ := by
  have hf := S.frattini_fixed_eq_bot_of_noncyclic D hnone (S.noncyclic_of_card_ne_prime hne)
  rcases S.alternatives with h | ⟨he, _⟩ | ⟨he, hc, hx⟩
  · exact (hne h).elim
  · let : Fact p.Prime := ⟨S.prime⟩
    let : Fact (IsPGroup p P) := ⟨S.pgroup⟩
    let : IsElementaryAbelian p P := he
    have hΦ : frattini P = ⊥ := frattini_eq_bot_of_isElementaryAbelian (p := p)
    have hC : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
      ext x
      simp [mem_centralizer_iff]
    have hW : W = ⊥ := by simpa only [hΦ, Subgroup.map_bot, hC, inf_top_eq] using hf
    have hU : U = ⊥ := bot_unique (hW ▸ S.core_le_module)
    have hc := S.core_card
    rw [hU, card_bot] at hc
    have hd := A.dimension.1
    have hpow : 1 < 2 ^ (2 * (d - 1)) := one_lt_pow₀ (by decide) (by omega)
    omega
  · exact ⟨he, hc, hx, hf⟩

/-- The surviving Frattini subgroup moves all of W. -/
theorem frattini_moves_module
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥) :
    ⁅W, (frattini P).map P.subtype⁆ = W := by
  let : Fact p.Prime := ⟨S.prime⟩
  let : IsElementaryAbelian 2 W := S.elementary
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := S.pgroup.exists_card_eq
    rw [hn]
    exact S.odd_prime.pow
  have hcop : Nat.Coprime (Nat.card P) (Nat.card W) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr hodd).pow_right n
  have hΦP : (frattini P).map P.subtype ≤ P := map_subtype_le _
  have he := eq_commutator_sup_centralizer_of_solvable_coprime W
    ((frattini P).map P.subtype) (hΦP.trans S.odd_normalizes_module)
    (Group.isSolvable_of_comm fun x y => mul_comm x y)
    (hcop.of_dvd_left (card_dvd_of_le hΦP))
  simpa only [hf, sup_bot_eq] using he.symm

end InvariantOddLocalAnalysis
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
