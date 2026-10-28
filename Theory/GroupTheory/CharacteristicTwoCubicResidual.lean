module
public import Theory.GroupTheory.CentralPPerfectCoprime
public import Theory.GroupTheory.CharacteristicTwoCommutatorKernel
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Mathlib.GroupTheory.SchurZassenhaus
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Splitting the core under a cubic residual action

A two-perfect subgroup acts on a central elementary part V of the self-centralizing
two-core, and fixes the core modulo V. If its faithful quotient on V is elementary
of exponent three, its action kernel is exactly V. The two-layer centralizer
lemma first puts that kernel in the core. Two-perfectness then kills the central
two-kernel after quotienting by V. Schur–Zassenhaus and coprime action split the
core as V times its residual centralizer. A subgroup normalizing the residual
and commuting with the core modulo V centralizes the fixed factor.

Source: Aschbacher–Smith15.1.11, printed p.1089. The source consumer uses the
literal N_M(C_T(V)) and retains the separate model hypotheses on its residual.
-/

public section
open Subgroup
namespace MonoidHom
variable {G D : Type*} [Group G] [Group D] {p n : ℕ} [Fact p.Prime]

theorem ker_eq_of_pPerfect_of_coprime_abelian_image
    (hG : IsPPerfect p G) (f : G →* D) (V : Subgroup G) [V.Normal]
    (hV : V ≤ f.ker) (hp : IsPGroup p f.ker)
    (hc : ⁅f.ker, (⊤ : Subgroup G)⁆ ≤ V)
    (hcomm : ∀ x y, Commute (f x) (f y))
    (hn : Nat.Coprime p n) (hexp : ∀ x, f x ^ n = 1) : f.ker = V := by
  let q := QuotientGroup.mk' V
  let g := QuotientGroup.lift V f hV
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective V
  have hgc : g.ker ≤ center (G ⧸ V) := by
    rw [QuotientGroup.ker_lift]
    apply commutator_top_right_eq_bot_iff_le_center.mp
    rw [←map_top_of_surjective q hq, ←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [QuotientGroup.ker_mk'] using hc
  have hgp : IsPGroup p g.ker := by
    rw [QuotientGroup.ker_lift]
    exact hp.map q
  have hi : Function.Injective g :=
    g.injective_of_isPPerfect_of_coprime_abelian_image (hG.of_surjective q hq) hgc hgp
      (by
        intro x y
        obtain ⟨x,rfl⟩ := hq x
        obtain ⟨y,rfl⟩ := hq y
        exact hcomm x y) hn (by
        intro x
        obtain ⟨x,rfl⟩ := hq x
        exact hexp x)
  exact ((QuotientGroup.injective_lift_iff V f hV).mp hi).symm
end MonoidHom

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
open scoped IsMulCommutative

theorem cubic_residual_core_splitting
    (V X : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hV : V ≤ pCore 2 G) (hVX : V ≤ X)
    (hcentral : V ≤ centralizer (pCore 2 G : Set G))
    (hG : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hX : IsPPerfect 2 X) (hcomm : ⁅pCore 2 G,X⁆ ≤ V)
    (hfixed : V ⊓ centralizer (X : Set G) = ⊥)
    (himage : IsElementaryAbelian 3
      (X.map (QuotientGroup.mk' (centralizer (V : Set G))))) :
    X ⊓ centralizer (V : Set G) = V ∧
      pCore 2 G = V ⊔ (pCore 2 G ⊓ centralizer (X : Set G)) ∧
      Disjoint V (pCore 2 G ⊓ centralizer (X : Set G)) := by
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  let f := q.subgroupMap X
  let W := V.subgroupOf X
  have hk : f.ker = (centralizer (V : Set G)).subgroupOf X := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
  have hK : X ⊓ centralizer (V : Set G) ≤ pCore 2 G :=
    centralizer_intersection_le_twoCore_of_core_commutator V X
      (IsElementaryAbelian.isPGroup 2 V) hG hcomm
  have hkp : IsPGroup 2 f.ker := by
    rw [hk]
    exact (pCore_isPGroup (p := 2) (G := G)).comap_of_injective X.subtype
      X.subtype_injective |>.to_le (fun x hx => hK ⟨x.property,hx⟩)
  have hWK : W ≤ f.ker := by
    rw [hk]
    exact fun x hx => Subgroup.le_centralizer (H := V) hx
  have hkc : ⁅f.ker,(⊤ : Subgroup X)⁆ ≤ W := by
    have hm : (⁅f.ker,(⊤ : Subgroup X)⁆).map X.subtype ≤ V := by
      rw [map_commutator,hk,subgroupOf_map_subtype,
        ←MonoidHom.range_eq_map,range_subtype]
      exact (commutator_mono (by simpa only [inf_comm] using hK) le_rfl).trans hcomm
    exact fun x hx => hm (mem_map_of_mem X.subtype hx)
  let := himage
  have hker : f.ker = W :=
    f.ker_eq_of_pPerfect_of_coprime_abelian_image hX W hWK hkp hkc
      (fun x y => (IsMulCommutative.is_comm (M := X.map q)).comm _ _)
      (by decide : Nat.Coprime 2 3)
      (fun x => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 (X.map q)) (f x))
  have hKV : X ⊓ centralizer (V : Set G) = V := by
    have he := congrArg (map X.subtype) hker
    dsimp only [W] at he
    rw [hk,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hVX] at he
    simpa only [inf_comm] using he
  have hWindex : Odd W.index := by
    rw [←hker,index_ker,f.range_eq_top_of_surjective (q.subgroupMap_surjective X),card_top]
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 (X.map q)).exists_card_eq
    rw [hn]
    exact Odd.pow (by decide : Odd 3)
  have hWcop : Nat.Coprime (Nat.card W) W.index := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 V).of_equiv
      (subgroupOfEquivOfLe hVX).symm |>.exists_card_eq
    rw [hn]
    exact hWindex.coprime_two_left.pow_left n
  obtain ⟨A₀,hA₀⟩ := exists_right_complement'_of_coprime hWcop
  let A := A₀.map X.subtype
  have hAX : A ≤ X := map_subtype_le _
  have hXA : X = V ⊔ A := by
    have he := congrArg (map X.subtype) hA₀.sup_eq_top
    simpa only [map_sup,W,map_subgroupOf_eq_of_le hVX,←MonoidHom.range_eq_map,
      range_subtype] using he.symm
  have hAodd : Odd (Nat.card A) := by
    rw [card_map_of_injective X.subtype_injective,←hA₀.symm.index_eq_card]
    exact hWindex
  have hAR : Nat.Coprime (Nat.card A) (Nat.card (pCore 2 G)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn]
    exact hAodd.coprime_two_right.pow_right n
  have hfixA : pCore 2 G ⊓ centralizer (A : Set G) =
      pCore 2 G ⊓ centralizer (X : Set G) := by
    apply le_antisymm
    · refine le_inf inf_le_left ?_
      apply le_centralizer_iff.mp
      rw [hXA]
      exact sup_le (hcentral.trans (centralizer_le inf_le_left))
        (le_centralizer_iff.mp inf_le_right)
    · exact inf_le_inf_left _ (centralizer_le hAX)
  let : Group.IsNilpotent (pCore 2 G) := (pCore_isPGroup (p := 2) (G := G)).isNilpotent
  have hsplit : pCore 2 G = V ⊔ (pCore 2 G ⊓ centralizer (X : Set G)) := by
    apply le_antisymm
    · have hs := eq_commutator_sup_centralizer_of_solvable_coprime (pCore 2 G) A
        le_normalizer_of_normal inferInstance hAR
      rw [hfixA] at hs
      exact hs.le.trans (sup_le_sup ((commutator_mono le_rfl hAX).trans hcomm) le_rfl)
    · exact sup_le hV inf_le_left
  refine ⟨hKV,hsplit,disjoint_iff.mpr ?_⟩
  apply bot_unique
  exact (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans hfixed.le

omit [Finite G] in
/-- A normalized residual splits off the core centralizer from a supplement. -/
theorem centralizes_core_fixed_of_normalizes_residual
    (V X P R : Subgroup G) (hPR : P ≤ normalizer (R : Set G))
    (hPX : P ≤ normalizer (X : Set G))
    (hcomm : ⁅R,P⁆ ≤ V) (hfixed : V ⊓ centralizer (X : Set G) = ⊥) :
    P ≤ centralizer (R ⊓ centralizer (X : Set G) : Set G) := by
  let C := R ⊓ centralizer (X : Set G)
  have hPC : P ≤ normalizer (C : Set G) :=
    (le_inf hPR (hPX.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hCV : ⁅C,P⁆ ≤ V := (commutator_mono inf_le_left le_rfl).trans hcomm
  have hCC : ⁅C,P⁆ ≤ centralizer (X : Set G) :=
    (le_normalizer_iff_commutator_le_left.mp hPC).trans inf_le_right
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (bot_unique ((le_inf hCV hCC).trans hfixed.le)))
end Subgroup
