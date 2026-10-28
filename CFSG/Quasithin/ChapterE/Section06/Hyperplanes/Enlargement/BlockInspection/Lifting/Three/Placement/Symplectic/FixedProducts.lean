module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Setup
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Contracts
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Reduction of the solvable block action to commuting normal factors

Two-perfection kills the actual outer action when the outer group is a
two-group. For a centerless component, uniqueness of product coordinates
then splits the fixed subgroup of X C_G(X). The normalizer orbit bound
makes the restricted normalizer a normal subgroup of C_G(U), so it inherits
characteristic two and the original block's relative subnormality.

Factor separation for the solvable block remains an explicit new obligation.
The coordinate argument follows `GeneralizedFitting.FixedNormalizerPlacement`,
replacing perfectness by two-perfection and a two-group outer quotient.
The private block-module transport is reused from `BlockInspection.Transport`,
preserving the actual quotient map and intertwining equation.
Source: Aschbacher–Smith E.6.23, printed pp.254–255, and 1.2.1(3), p.504.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Symplectic
universe u

/-- The independent algebraic separation obligation. All factors and the
block are subgroups of the same characteristic-two ambient group. -/
def ThreeFactorSeparation : Prop :=
  ∀ (D : Type u) [Group D] [Finite D],
    generalizedFitting D = pCore 2 D →
    ∀ (P R B : Subgroup D), P.Normal → R.Normal → Disjoint P R →
      ⁅P, R⁆ = ⊥ → ChapterC.IsBlock B → ChapterC.IsAlternatingBlock B 3 →
      B ≤ P ⊔ R → B ≤ P ∨ B ≤ R

open ChapterC

variable {A B : Type*} [Group A] [Group B]

private theorem transport_blockU (e : A ≃* B) :
    (blockU A).map e.toMonoidHom = blockU B := by
  rw [blockU, map_commutator, pCore_map_iso,
    map_top_of_surjective _ e.surjective, blockU]

private def blockUEquiv (e : A ≃* B) : blockU A ≃* blockU B :=
  (e.subgroupMap (blockU A)).trans (MulEquiv.subgroupCongr (transport_blockU e))

private theorem transport_blockFixed (e : A ≃* B) :
    (blockFixed A).map (blockUEquiv e).toMonoidHom = blockFixed B := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.centerCongr e ⟨x, hx⟩).property
  · intro x hx
    exact ⟨(blockUEquiv e).symm x,
      (Subgroup.centerCongr e).symm ⟨x, hx⟩ |>.property,
      (blockUEquiv e).apply_symm_apply x⟩

private def coreQuotientEquiv (e : A ≃* B) :
    (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B) :=
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

private def blockModuleEquiv (e : A ≃* B) : BlockModule A ≃* BlockModule B :=
  QuotientGroup.congr _ _ (blockUEquiv e) (transport_blockFixed e)

private theorem blockUEquiv_conjugate (e : A ≃* B) (a : A) (u : blockU A) :
    blockUEquiv e (blockConjugate A a u) =
      blockConjugate B (e a) (blockUEquiv e u) := by
  apply Subtype.ext
  change e (a * (u : A) * a⁻¹) = e a * e (u : A) * (e a)⁻¹
  simp only [map_mul, map_inv]

/-- Pull back the actual core quotient and conjugation module along an isomorphism. -/
private def pullbackModel {X V : Type*} [Group X] [Group V]
    {rho : X →* MulAut V} (model : BlockModuleModel A rho) (e : B ≃* A) :
    BlockModuleModel B rho where
  quotientIso := (coreQuotientEquiv e).trans model.quotientIso
  moduleIso := (blockModuleEquiv e).trans model.moduleIso
  intertwining b u := by
    change model.moduleIso (QuotientGroup.mk' (blockFixed A)
      (blockUEquiv e (blockConjugate B b u))) =
      rho (model.quotientIso (QuotientGroup.mk' (pCore 2 A) (e b)))
        (model.moduleIso (QuotientGroup.mk' (blockFixed A) (blockUEquiv e u)))
    rw [blockUEquiv_conjugate]
    exact model.intertwining (e b) (blockUEquiv e u)

/-- The full equivariant linear model is invariant under group isomorphism. -/
private theorem linearModel_of_equiv {X V k : Type*} [Group X]
    [AddCommGroup V] [Semiring k] [Module k V]
    {pi : Representation k X V} (h : IsLinearBlockModel A pi) (e : A ≃* B) :
    IsLinearBlockModel B pi := by
  obtain ⟨rho, ⟨model⟩, hpi⟩ := h
  exact ⟨rho, ⟨pullbackModel model e.symm⟩, hpi⟩

private theorem alternating_of_equiv {m : ℕ} (h : IsAlternatingBlock A m)
    (e : A ≃* B) : IsAlternatingBlock B m :=
  ⟨h.1, h.2.1.of_mulEquiv e, linearModel_of_equiv h.2.2 e⟩


variable {G : Type u} [Group G]

/-- Two-perfection annihilates the actual outer conjugation homomorphism. -/
private theorem twoPerfect_le_inner_product {L X : Subgroup G}
    (hp : IsPPerfect 2 L) (hn : L ≤ normalizer (X : Set G))
    (ho : IsPGroup 2 (MulAut.Outer X)) : L ≤ X ⊔ centralizer (X : Set G) := by
  let f : L →* MulAut.Outer X :=
    (QuotientGroup.mk' (MulAut.innerSubgroup X)).comp
      (X.normalizerMonoidHom.comp (inclusion hn))
  have hf := hp.hom_eq_one_of_isPGroup ho f
  intro l hl
  have hi : X.normalizerMonoidHom ⟨l, hn hl⟩ ∈ MulAut.innerSubgroup X :=
    (QuotientGroup.eq_one_iff _).mp (DFunLike.congr_fun hf ⟨l, hl⟩)
  obtain ⟨x, hx⟩ := hi
  let xN : normalizer (X : Set G) := ⟨x, X.le_normalizer x.property⟩
  have hxN : X.normalizerMonoidHom xN = MulAut.conj x := by ext y; rfl
  have hk : xN⁻¹ * ⟨l, hn hl⟩ ∈ X.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxN, hx, inv_mul_cancel]
  rw [normalizerMonoidHom_ker] at hk
  have hm := (X ⊔ centralizer (X : Set G)).mul_mem
    (mem_sup_left x.property)
    (mem_sup_right (show (x : G)⁻¹ * l ∈ centralizer (X : Set G) from hk))
  simpa only [mul_inv_cancel_left] using hm

/-- Fixed points split over commuting factors with trivial intersection. -/
private theorem fixed_product {P R U : Subgroup G}
    (hd : Disjoint P R) (hc : P ≤ centralizer (R : Set G))
    (hP : U ≤ normalizer (P : Set G)) (hR : U ≤ normalizer (R : Set G)) :
    (P ⊔ R) ⊓ centralizer (U : Set G) ≤
      (P ⊓ centralizer (U : Set G)) ⊔ (R ⊓ centralizer (U : Set G)) := by
  intro x hx
  have hRP : R ≤ normalizer (P : Set G) :=
    (le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)
  have hp : x ∈ (P : Set G) * (R : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hRP]
    exact hx.1
  obtain ⟨p, hp, r, hr, hpr⟩ := hp
  change p * r = x at hpr
  have hfix (t : G) (ht : t ∈ U) :
      t * p * t⁻¹ = p ∧ t * r * t⁻¹ = r := by
    have hmul : (t * p * t⁻¹) * (t * r * t⁻¹) = p * r := by
      calc
        _ = t * (p * r) * t⁻¹ := by group
        _ = t * x * t⁻¹ := by rw [hpr]
        _ = x := by rw [hx.2 t ht, mul_inv_cancel_right]
        _ = p * r := hpr.symm
    have he := mul_injective_of_disjoint hd
      (a₁ := (⟨t * p * t⁻¹, (mem_normalizer_iff.mp (hP ht) p).mp hp⟩,
        ⟨t * r * t⁻¹, (mem_normalizer_iff.mp (hR ht) r).mp hr⟩))
      (a₂ := (⟨p, hp⟩, ⟨r, hr⟩)) hmul
    exact ⟨congrArg (fun v : P × R => (v.1 : G)) he,
      congrArg (fun v : P × R => (v.2 : G)) he⟩
  have hpC : p ∈ centralizer (U : Set G) := fun t ht =>
    mul_inv_eq_iff_eq_mul.mp (hfix t ht).1
  have hrC : r ∈ centralizer (U : Set G) := fun t ht =>
    mul_inv_eq_iff_eq_mul.mp (hfix t ht).2
  exact hpr ▸ mul_mem_sup ⟨hp, hpC⟩ ⟨hr, hrC⟩

private theorem twoPerfect_normalizes {H L X : Subgroup G}
    (hLH : L ≤ H) (hXH : X ≤ H) (hp : IsPPerfect 2 L)
    (horbit : (X.subgroupOf H).Normal ∨
      (normalizer (X.subgroupOf H : Set H)).index = 2) :
    L ≤ normalizer (X : Set G) := by
  let B := L.subgroupOf H
  let N := normalizer (X.subgroupOf H : Set H)
  have hpB : IsPPerfect 2 B := hp.of_surjective
    (subgroupOfEquivOfLe hLH).symm.toMonoidHom
    (subgroupOfEquivOfLe hLH).symm.surjective
  have hBN : B ≤ N := by
    rcases horbit with hn | hi
    · let := hn
      exact le_normalizer_of_normal
    · let : N.Normal := normal_of_index_eq_two hi
      have hq : IsPGroup 2 (H ⧸ N) := IsPGroup.of_card (n := 1) hi
      exact (le_pResidual_of_isPPerfect B hpB).trans (sInf_le ⟨inferInstance, hq⟩)
  apply le_normalizer_iff.mpr
  intro l hl x hx
  exact le_normalizer_iff.mp hBN ⟨l, hLH hl⟩ hl ⟨x, hXH hx⟩ hx

variable [Finite G]

/-- The restricted normalizer is normal in the original centralizer and
inherits characteristic two. No component placement is used. -/
theorem fixed_normalizer_characteristic_two {H U X : Subgroup G}
    (hCH : centralizer (U : Set G) ≤ H) (hXH : X ≤ H)
    (horbit : (X.subgroupOf H).Normal ∨
      (normalizer (X.subgroupOf H : Set H)).index = 2)
    (hchar : generalizedFitting (centralizer (U : Set G)) =
      pCore 2 (centralizer (U : Set G))) :
    generalizedFitting ↥(normalizer (X : Set G) ⊓ centralizer (U : Set G)) =
      pCore 2 ↥(normalizer (X : Set G) ⊓ centralizer (U : Set G)) := by
  let C := centralizer (U : Set G)
  let J := normalizer (X : Set G) ⊓ C
  have hN : (normalizer (X.subgroupOf H : Set H)).Normal := by
    rcases horbit with hn | hi
    · let := hn
      rw [normalizer_eq_top]
      infer_instance
    · exact normal_of_index_eq_two hi
  have hJ : (J.subgroupOf C).Normal := by
    have hh := hN.comap (inclusion hCH)
    rw [← subgroupOf_normalizer_eq hXH] at hh
    have he : ((normalizer (X : Set G)).subgroupOf H).comap (inclusion hCH) =
        J.subgroupOf C := by
      ext x
      exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩
    exact he ▸ hh
  have hc : centralizer (pCore 2 C : Set C) ≤ pCore 2 C := by
    have hf : generalizedFitting C = pCore 2 C := hchar
    simpa only [hf] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := C))
  have hj := subnormal_core_selfCentralizing hc (J.subgroupOf C) hJ.isSubnormal
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    ((Theory.Quasithin.centralizer_pCore_le_iff 2
      (subgroupOfEquivOfLe (show J ≤ C from inf_le_right))).mp hj)

/-- The genuine mixed action reduces to separation of commuting normal
factors in a characteristic-two group. Its premise is an independent new
algebraic obligation, not a source theorem or an assumed localization. -/
theorem interaction_of_factor_separation (hsep : ThreeFactorSeparation.{u})
    {H U L X : Subgroup G} (hL : SmallBlock U L)
    (h3 : ChapterC.IsAlternatingBlock L 3)
    (hCH : centralizer (U : Set G) ≤ H) (hXH : X ≤ H)
    (horbit : (X.subgroupOf H).Normal ∨
      (normalizer (X.subgroupOf H : Set H)).index = 2)
    (hchar : generalizedFitting (centralizer (U : Set G)) =
      pCore 2 (centralizer (U : Set G)))
    (hUX : U ≤ normalizer (X : Set G))
    (hd : Disjoint X (centralizer (X : Set G)))
    (ho : IsPGroup 2 (MulAut.Outer X)) : L ≤ X ∨ ⁅L, X⁆ = ⊥ := by
  let C := centralizer (U : Set G)
  let J := normalizer (X : Set G) ⊓ C
  let P := X ⊓ C
  let R := centralizer (X : Set G) ⊓ C
  have hLN : L ≤ normalizer (X : Set G) :=
    twoPerfect_normalizes (hL.1.trans hCH) hXH h3.2.1.twoPerfect horbit
  have hLJ : L ≤ J := le_inf hLN hL.1
  have hPJ : P ≤ J := le_inf (inf_le_left.trans X.le_normalizer) inf_le_right
  have hRJ : R ≤ J :=
    le_inf (inf_le_left.trans (Subgroup.centralizer_le_normalizer _)) inf_le_right
  have hnP : J ≤ normalizer (P : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans C.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hnR : J ≤ normalizer (R : Set G) :=
    (le_inf (inf_le_left.trans (normalizer_le_normalizer_centralizer X))
      (inf_le_right.trans C.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hp : L ≤ X ⊔ centralizer (X : Set G) :=
    twoPerfect_le_inner_product h3.2.1.twoPerfect hLN ho
  have hsplit : L ≤ P ⊔ R := (le_inf hp hL.1).trans
    (fixed_product hd (le_centralizer_iff.mpr le_rfl) hUX
      (hUX.trans (normalizer_le_normalizer_centralizer X)))
  have hcharJ := fixed_normalizer_characteristic_two hCH hXH horbit hchar
  have hblock : ChapterC.IsBlock (L.subgroupOf J) :=
    ⟨inferInstance, h3.2.1.of_mulEquiv (subgroupOfEquivOfLe hLJ).symm,
      hL.2.1.subnormal.comap (inclusion (show J ≤ C from inf_le_right))⟩
  have h3J : ChapterC.IsAlternatingBlock (L.subgroupOf J) 3 :=
    alternating_of_equiv h3 (subgroupOfEquivOfLe hLJ).symm
  have hdJ : Disjoint (P.subgroupOf J) (R.subgroupOf J) := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    apply Subtype.ext
    exact (disjoint_iff_inf_le.mp hd) ⟨hx.1.1, hx.2.1⟩
  have hcJ : ⁅P.subgroupOf J, R.subgroupOf J⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro p hp r hr
    exact Subtype.ext (hr.1 p hp.1).symm
  have hsJ : L.subgroupOf J ≤ P.subgroupOf J ⊔ R.subgroupOf J := by
    rw [← subgroupOf_sup hPJ hRJ]
    exact fun x hx => hsplit hx
  rcases hsep J hcharJ (P.subgroupOf J) (R.subgroupOf J) (L.subgroupOf J)
      (normal_subgroupOf_of_le_normalizer hnP) (normal_subgroupOf_of_le_normalizer hnR)
      hdJ hcJ hblock h3J hsJ with hP | hR
  · exact Or.inl (fun l hl => (hP (show (⟨l, hLJ hl⟩ : J) ∈ L.subgroupOf J from hl)).1)
  · exact Or.inr (commutator_eq_bot_iff_le_centralizer.mpr
      (fun l hl => (hR (show (⟨l, hLJ hl⟩ : J) ∈ L.subgroupOf J from hl)).1))

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Symplectic
