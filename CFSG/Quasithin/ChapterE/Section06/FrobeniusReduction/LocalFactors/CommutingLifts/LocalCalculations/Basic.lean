module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.Construction
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.Normalization

/-!
# Local action kernels and odd normalization in E.6.25

A faithful subgroup X detects the full odd part of a local group B when
|B| = 2^k |X|. The conjugation kernel on V is then a normal two-subgroup of
B, so lies in its intrinsic two-core. Separately, an odd actor whose action
commutes with X normalizes U = C_V(X). The earlier C-component theorem in
N_G(U) therefore makes it normalize L and L ∩ M.

These are common deductions for the local model calculations. The order
hypothesis is verified for the actual L₂-block Borel in `BlockCore`; it
is not asserted for the other Borel or symplectic models.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.11 and
the factor-count paragraph of E.6.25, printed pp.249–250,255.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
variable {G : Type*} [Group G] [Finite G]

private theorem kernel_two_of_faithful_card {A : Type*} [Group A]
    (f : G →* A) (X : Subgroup G) (hf : Function.Injective (f.comp X.subtype))
    {k : ℕ} (hc : Nat.card G = 2 ^ k * Nat.card X) : IsPGroup 2 f.ker := by
  let g : X →* f.range := f.rangeRestrict.comp X.subtype
  have hg : Function.Injective g := fun a b hab => hf (congrArg Subtype.val hab)
  obtain ⟨t, ht⟩ := card_dvd_of_injective g hg
  have hh := f.ker.card_mul_index
  rw [index_ker, ht, hc] at hh
  have he : Nat.card f.ker * t = 2 ^ k := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := X))
    calc
      Nat.card f.ker * t * Nat.card X = Nat.card f.ker * (Nat.card X * t) := by ring
      _ = 2 ^ k * Nat.card X := hh
  exact IsPGroup.of_card_dvd_pow ⟨t, he.symm⟩

/-- A faithful subgroup accounting for the whole odd part forces the
local conjugation kernel into the intrinsic two-core. -/
theorem local_kernel_le_core_of_card {V B X : Subgroup G}
    (hB : B ≤ normalizer (V : Set G)) (hX : X ≤ B)
    (hf : X ⊓ centralizer (V : Set G) = ⊥)
    {k : ℕ} (hc : Nat.card B = 2 ^ k * Nat.card X) :
    B ⊓ centralizer (V : Set G) ≤ B.pCoreIn 2 := by
  let f : B →* MulAut V := V.normalizerMonoidHom.comp (inclusion hB)
  have hinj : Function.Injective (f.comp (X.subgroupOf B).subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hxC : (x.val : G) ∈ centralizer (V : Set G) := by
      have hh : inclusion hB x.val ∈ V.normalizerMonoidHom.ker := hx
      rwa [normalizerMonoidHom_ker] at hh
    apply mem_bot.mpr
    apply Subtype.ext
    apply Subtype.ext
    exact mem_bot.mp (hf ▸ (show (x.val : G) ∈ X ⊓ centralizer (V : Set G) from
      ⟨x.property, hxC⟩))
  have hk : IsPGroup 2 f.ker := kernel_two_of_faithful_card f (X.subgroupOf B) hinj
    (by simpa only [Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv] using hc)
  have hkcore : f.ker ≤ pCore 2 B := le_sSup ⟨inferInstance, hk⟩
  rintro x ⟨hxB, hxC⟩
  refine ⟨⟨x, hxB⟩, hkcore ?_, rfl⟩
  change inclusion hB ⟨x, hxB⟩ ∈ V.normalizerMonoidHom.ker
  rwa [normalizerMonoidHom_ker]

/-- An odd subgroup normalizing U normalizes each of its C-components.
The earlier source theorem is applied in N_G(U), not in G. -/
theorem odd_normalizes_local_component {K : GroupClass} {T : Sylow 2 G}
    {M V U L A : Subgroup G}
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hA : A ≤ normalizer (U : Set G)) (ho : Odd (Nat.card A)) :
    A ≤ normalizer (L : Set G) := by
  let _ := h.elementary
  let N := normalizer (U : Set G)
  have hN : IsSQTK K N := h.simpleQTKE.twoLocal_sqtk
    ⟨U, hU.2.1, (IsElementaryAbelian.isPGroup 2 V).to_le hU.1, rfl⟩
  have hn := earlier N hN (L.subgroupOf N) (local_cComponent_in_normalizer hL)
  have hLN : L ≤ N := hL.1.trans (Subgroup.centralizer_le_normalizer _)
  have hr : A ≤ (pResidual 2 N).map N.subtype := by
    intro x hx
    have hxR : (⟨x, hx⟩ : A) ∈ pResidual 2 A :=
      mem_pResidual_of_orderOf_coprime
        (ho.coprime_two_left.of_dvd_right (orderOf_dvd_natCard (⟨x, hx⟩ : A)))
    exact ⟨inclusion hA ⟨x, hx⟩,
      map_pResidual_le 2 (inclusion hA) (mem_map_of_mem _ hxR), rfl⟩
  apply hr.trans
  have hm := (map_mono (f := N.subtype) hn).trans (le_normalizer_map N.subtype)
  rwa [map_subgroupOf_eq_of_le hLN] at hm

/-- Odd actors with action commuting with X normalize the local intersection.
This applies uniformly to the component and block branches. -/
theorem odd_normalizes_local_intersection {K : GroupClass} {T : Sylow 2 G}
    {M V U X L A : Subgroup G} [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hA : A ≤ normalizer (V : Set G)) (ho : Odd (Nat.card A))
    (hc : ∀ a ∈ inducedAutomizer V A, ∀ x ∈ inducedAutomizer V X, Commute a x) :
    A ≤ normalizer ((L ⊓ M : Subgroup G) : Set G) := by
  have hAU : A ≤ normalizer (U : Set G) := by
    have hh := normalizes_fixed_of_image_commutes hX
      (A.subgroupOf (normalizer (V : Set G))) hc
    rwa [map_subgroupOf_eq_of_le hA] at hh
  exact (le_inf (odd_normalizes_local_component h earlier hU hL hAU ho)
    ((hA.trans h.normalizer_le).trans M.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

omit [Finite G] in
/-- Commuting induced actions have their commutator in the actual
centralizer of V. No two-group conclusion is inferred here. -/
theorem cross_commutator_le_kernel {V A B : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (hB : B ≤ normalizer (V : Set G))
    (hc : ∀ a ∈ inducedAutomizer V A, ∀ b ∈ inducedAutomizer V B, Commute a b) :
    ⁅A, B⁆ ≤ centralizer (V : Set G) := by
  let N := normalizer (V : Set G)
  let f := V.normalizerMonoidHom.rangeRestrict
  have hmap : (⁅A.subgroupOf N, B.subgroupOf N⁆).map f = ⊥ := by
    rw [map_commutator]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro a ha
    apply mem_centralizer_iff.mpr
    intro b hb
    exact (hc a ha b hb).eq.symm
  have hk := (Subgroup.map_eq_bot_iff _).mp hmap
  dsimp only [f] at hk
  rw [MonoidHom.ker_rangeRestrict, normalizerMonoidHom_ker] at hk
  have hm := map_mono (f := N.subtype) hk
  rwa [map_commutator, map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hB,
    map_subgroupOf_eq_of_le (centralizer_le_normalizer (V : Set G))] at hm


end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
