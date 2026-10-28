module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenFixed
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryPermutation.OddOffenderTransport
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Fixed and moved orders in the natural A7 block layer

The intrinsic layer U(K) of an ordinary A7 block has no fixed kernel and
is the natural six-dimensional module. Its invariant dot product gives
self-duality, so every subgroup A has fixed dimension equal to the
codimension of [U(K),A]. Consequently the product of those two subgroup
orders is64. Injective ambient transport retains the actual subgroup A
and the literal conjugation and two-core quotient maps.

This supplies the fixed-line calculation for the original A6 subgroup in
the conclusion of Aschbacher--Smith12.6.2, printed p.828, combined
manuscript of1 March2004, using the natural module of B.3 and I.1.6.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {K : Type*} [Group K]

theorem IsAlternatingBlock.seven_fixed_card_mul_moved_card
    (h : IsAlternatingBlock K 7) (A : Subgroup K) :
    Nat.card (blockU K ⊓ centralizer (A : Set K) : Subgroup K) *
      Nat.card (⁅blockU K,A⁆ : Subgroup K) = 64 := by
  let := h.2.1.finite
  let := h.2.1.elementary
  let U := blockU K
  let q := QuotientGroup.mk' (pCore 2 K)
  have hk : q.ker = centralizer (U : Set K) := by
    rw [QuotientGroup.ker_mk',h.2.1.centralizer_blockU]
  let ρ := NormalElementaryQuotient.representation U q (QuotientGroup.mk'_surjective _) hk
  obtain ⟨r,⟨m⟩,hr⟩ := h.2.2
  have hq : Function.Bijective (QuotientGroup.mk' (blockFixed K)) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',h.seven_fixed_eq_bot]),
      QuotientGroup.mk'_surjective _⟩
  let eM := (MulEquiv.ofBijective (QuotientGroup.mk' (blockFixed K)) hq).trans m.moduleIso
  let e : Additive U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 7) :=
    { eM.toAdditiveLeft with map_smul' := fun a v => ZMod.map_smul eM.toAdditiveLeft a v }
  let σ := BinaryPermutation.alternatingNaturalRepresentation (Fin 7)
  have he (g : K ⧸ pCore 2 K) (u : Additive U) :
      e (ρ g u) = σ (m.quotientIso g) (e u) := by
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) g
    have hh : ρ (q g) u = Additive.ofMul (blockConjugate K g u.toMul) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact NormalElementaryQuotient.representation_apply U q (QuotientGroup.mk'_surjective _) hk g u
    rw [hh]
    change (m.moduleIso (QuotientGroup.mk' _ (blockConjugate K g u.toMul))).toAdd = _
    rw [m.intertwining]
    exact hr _ _
  let d := (e.trans (BinaryPermutation.naturalDualEquiv (Fin 7))).trans e.dualMap
  have hd (g : K ⧸ pCore 2 K) (u : Additive U) : d (ρ g u) = ρ.dual g (d u) := by
    change e.dualMap (BinaryPermutation.naturalDualEquiv (Fin 7) (e (ρ g u))) = _
    rw [he]
    have hn := BinaryPermutation.naturalDualEquiv_equivariant (Fin 7) (m.quotientIso g).val (e u)
    change BinaryPermutation.naturalDualEquiv (Fin 7) (σ (m.quotientIso g) (e u)) =
      σ.dual (m.quotientIso g) (BinaryPermutation.naturalDualEquiv (Fin 7) (e u)) at hn
    rw [hn]
    ext v
    change (BinaryPermutation.naturalDualEquiv (Fin 7) (e u))
      (σ (m.quotientIso g)⁻¹ (e v)) =
      (BinaryPermutation.naturalDualEquiv (Fin 7) (e u)) (e (ρ g⁻¹ v))
    rw [he,m.quotientIso.map_inv]
  have hdims := OddTransport.fixedCodim_eq_of_equivariant ρ ρ.dual d hd (A.map q)
  rw [fixedCodim_dual_eq_moved_finrank] at hdims
  have hsum := fixedCodim_add_finrank ρ (A.map q)
  rw [hdims, e.finrank_eq, BinaryPermutation.finrank_natural_odd (Fin 7) (by decide)] at hsum
  let : IsElementaryAbelian 2 (⁅U,A⁆ : Subgroup K) :=
    IsElementaryAbelian.of_le (commutator_le_left U A)
  rw [←Nat.card_congr (NormalElementaryQuotient.fixedSpaceEquiv U q
    (QuotientGroup.mk'_surjective _) hk A),
    Nat.card_congr (Additive.ofMul : (⁅U,A⁆ : Subgroup K) ≃ Additive (⁅U,A⁆ : Subgroup K)),
    Nat.card_congr (NormalElementaryQuotient.movedEquiv U q
      (QuotientGroup.mk'_surjective _) hk A).toEquiv,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ (A.map q)),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := subspaceCommutator ρ ⊤ (A.map q)),
    Nat.card_zmod,←pow_add]
  rw [Nat.add_comm,hsum]
  rfl
variable {G : Type*} [Group G]

/-- The same duality formula on an actual ambient block and subgroup. -/
theorem IsAlternatingBlock.seven_ambient_fixed_card_mul_moved_card
    {K A : Subgroup G} (h : IsAlternatingBlock K 7) (hAK : A ≤ K) :
    let W := (blockU K).map K.subtype
    Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) *
      Nat.card (⁅W,A⁆ : Subgroup G) = 64 := by
  have hh := h.seven_fixed_card_mul_moved_card (A.subgroupOf K)
  rw [←card_map_of_injective (f := K.subtype) K.subtype_injective,
    ←map_inf_centralizer_of_injective K.subtype K.subtype_injective,
    map_subgroupOf_eq_of_le hAK] at hh
  rw [←card_map_of_injective (f := K.subtype) K.subtype_injective
    (K := (⁅blockU K,A.subgroupOf K⁆ : Subgroup K)),
    map_commutator,map_subgroupOf_eq_of_le hAK] at hh
  exact hh
end CFSG.Quasithin.ChapterC
