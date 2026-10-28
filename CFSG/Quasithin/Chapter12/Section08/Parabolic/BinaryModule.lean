module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryCore
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryModule.SourceQuotient
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Theory.Representation.BinaryConjugationSection.Canonical

/-!
# The natural binary module of the marked parabolic

The source commutator and square bounds first make the literal quotient
S/E, with S=O₂(I₂), elementary abelian. Its conjugation action descends
through I₂/S. The marked complementary images W/E and X/E force the
natural S₃ action: [U,U]≤V₁ fixes W/E, and two-core normalization puts
every U-displacement into W/E. The quadratic-pair theorem gives the full
natural tensor model and the three fixed/moved-space equalities.

The conjugator in P is preserved: its two-core factor normalizes W,
so an internal I₂ representative has the same X. No involutory lift of
the chosen element of U−W is assumed. The final theorem constructs the
binary quotient, its representation, and its natural-module equivalence.

Source: Aschbacher–Smith, G.2.3(6) and 12.8.9(2–3), printed pp.334,853.
-/

open Subgroup
open scoped IsMulCommutative Pointwise _root_.TensorProduct
open InvertedCubicTensor

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

omit [Finite G] in
/-- The earlier parabolic supplement places its two-core in the original
point normalizer, so the characteristic two-core of I₂ normalizes U. -/
public theorem binary_core_normalizes_U
    (F : InvariantFlag T V n) (L : Subgroup G)
    (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L)
    (hPH : (F.P L).pCoreIn 2 ≤ F.H) :
    (F.I₂ L).pCoreIn 2 ≤ normalizer (F.U : Set G) := by
  have hIP : F.I₂ L ≤ F.P L := le_sup_right.trans hfactor.ge
  have hnormal : normalizer (F.I₂ L : Set G) ≤
      normalizer ((F.I₂ L).pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L))
  have hS : (F.I₂ L).pCoreIn 2 ≤ (F.P L).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (F.I₂ L))
      ((pCoreIn_le 2 (F.I₂ L)).trans hIP)
      ((le_normalizer_conjugateSpanBy F.U (F.P L)).trans hnormal)
  exact (hS.trans hPH).trans (le_normalizer_conjugateSpanBy V F.H)

/-- The source action quotient of I₂ by its actual two-core. -/
public def binaryCoreProjection (F : InvariantFlag T V n) (L : Subgroup G)
    (e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* S₃) : F.I₂ L →* S₃ :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (F.I₂ L)))

omit [Finite G] in
private theorem binaryCoreProjection_ker (F : InvariantFlag T V n) (L : Subgroup G)
    (e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* S₃) :
    (F.binaryCoreProjection L e).ker = pCore 2 (F.I₂ L) := by
  ext i
  change e (QuotientGroup.mk i) = 1 ↔ i ∈ pCore 2 (F.I₂ L)
  constructor
  · intro hi
    exact (QuotientGroup.eq_one_iff i).mp (e.injective (hi.trans e.map_one.symm))
  · intro hi
    rw [(QuotientGroup.eq_one_iff i).mpr hi, map_one]

omit [Finite G] in
private theorem binaryCoreProjection_involution
    (F : InvariantFlag T V n) (L : Subgroup G)
    (e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* S₃)
    (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2)
    (hindex : F.W.relIndex F.U = 2)
    (u : F.I₂ L) (hu : (u : G) ∈ F.U) (huw : (u : G) ∉ F.W) :
    (F.binaryCoreProjection L e u) ^ 2 = 1 ∧ F.binaryCoreProjection L e u ≠ 1 := by
  let I := F.I₂ L
  let U := F.U.subgroupOf I
  let f := F.binaryCoreProjection L e
  have hk : f.ker = pCore 2 I := F.binaryCoreProjection_ker L e
  have hUI : F.U ≤ I := le_conjugateSpanBy _ _
  have hW : F.U ⊓ I.pCoreIn 2 = F.W := by
    rw [← hcore, ← inf_assoc, inf_eq_left.mpr hUI]
    rfl
  have hUf : Nat.card (U.map f) = 2 := by
    rw [← relIndex_ker U f, hk]
    have he := relIndex_map_map_of_injective (pCore 2 I) U I.subtype_injective
    rw [show U.map I.subtype = F.U from map_subgroupOf_eq_of_le hUI] at he
    change (I.pCoreIn 2).relIndex F.U = (pCore 2 I).relIndex U at he
    rw [← he, ← inf_relIndex_left, hW]
    exact hindex
  constructor
  · have hp := pow_card_eq_one' (x := (⟨f u, mem_map_of_mem f hu⟩ : U.map f))
    rw [hUf] at hp
    exact congrArg Subtype.val hp
  · intro he
    have huS : (u : G) ∈ I.pCoreIn 2 :=
      mem_map_of_mem I.subtype (hk ▸ (show u ∈ f.ker from he))
    exact huw (hW ▸ (show (u : G) ∈ F.U ⊓ I.pCoreIn 2 from ⟨hu, huS⟩))

/-- The complete natural-module and marked fixed/moved-space conclusions
of the binary G.2.3 application, on a specified literal section O₂(I₂)/E.
The final theorem below constructs this section and its action from the
stated 12.8.4 and 12.8.9(1) inputs. -/
public theorem binary_natural_module_and_marks
    (F : InvariantFlag T V n) [IsMulCommutative V] (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) (g : G) (hgP : g ∈ F.P L)
    (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L)
    (hPH : (F.P L).pCoreIn 2 ≤ F.H)
    (hgen : F.U ⊔ conjugate F.U g = F.I₂ L)
    (e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* S₃)
    (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2)
    (hindex : F.W.relIndex F.U = 2) (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) S₃ M)
    (d : Representation.BinaryConjugationSection (F.I₂ L) ((F.I₂ L).pCoreIn 2)
      (F.E g) (σ.comp (F.binaryCoreProjection L e)))
    (u : F.I₂ L) (hu : (u : G) ∈ F.U) (huw : (u : G) ∉ F.W) :
    (∃ j : multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2] M,
      ∀ a z, j ((Representation.tprod (Representation.trivial (ZMod 2) S₃
          (multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a z) =
        σ a (j z)) ∧
      LinearMap.ker (σ (F.binaryCoreProjection L e u) - 1) = d.imageSpace F.W ∧
      LinearMap.range (σ (F.binaryCoreProjection L e u) - 1) = d.imageSpace F.W ∧
      (d.imageSpace (F.X g)).map (σ (F.binaryCoreProjection L e u) - 1) =
        d.imageSpace F.W := by
  have hUI : F.U ≤ F.I₂ L := le_conjugateSpanBy _ _
  have hIP : F.I₂ L ≤ F.P L := le_sup_right.trans hfactor.ge
  have hnormal : normalizer (F.I₂ L : Set G) ≤
      normalizer ((F.I₂ L).pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L))
  have hPnormal : F.P L ≤ normalizer ((F.P L).pCoreIn 2 : Set G) :=
    (F.P L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (F.P L) (pCore 2 (F.P L)))
  have hnorm : (F.I₂ L).pCoreIn 2 ≤ normalizer (F.U : Set G) :=
    F.binary_core_normalizes_U L hfactor hPH
  have hW : F.U ⊓ (F.I₂ L).pCoreIn 2 = F.W := by
    rw [← hcore, ← inf_assoc, inf_eq_left.mpr hUI]
    rfl
  have hUS : ⁅F.U, (F.I₂ L).pCoreIn 2⁆ ≤ F.W := by
    rw [← hW]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hnorm)
      (le_normalizer_iff_commutator_le_right.mp
        (hUI.trans ((F.I₂ L).le_normalizer.trans hnormal)))
  have hUW : ⁅F.U, F.W⁆ ≤ F.E g :=
    ((commutator_mono le_rfl (show F.W ≤ F.U from inf_le_left)).trans hcomm).trans
      ((F.le_seed 1).trans (F.seed_le_E_of_normalizes g (F.P_le_seed_normalizer L hL hgP)))
  have hfactorS := F.binary_core_factorization L g hgP hfactor hPH hgen e hcore hindex
  have hgprod : g ∈ ((F.P L).pCoreIn 2 : Set G) * (F.I₂ L : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (hIP.trans hPnormal), ← hfactor]
    exact hgP
  obtain ⟨k, hk, h, hh, hkh⟩ := hgprod
  have hkU : conjugate F.U k = F.U := (conjugate_eq_iff _ _).mpr
    (le_normalizer_conjugateSpanBy V F.H (hPH hk))
  have hkS : conjugate ((F.I₂ L).pCoreIn 2) k = (F.I₂ L).pCoreIn 2 :=
    (conjugate_eq_iff _ _).mpr
      (hnormal (le_normalizer_conjugateSpanBy F.U (F.P L) (pCoreIn_le 2 (F.P L) hk)))
  have hkW : conjugate F.W k = F.W := by
    rw [← hW, conjugate_inf, hkU, hkS]
  have hX : F.X g = F.W.conjBy h⁻¹ := by
    change conjugate F.W g = conjugate F.W h
    calc
      conjugate F.W g = conjugate F.W (k * h) := congrArg (conjugate F.W) hkh.symm
      _ = conjugate (conjugate F.W k) h := by
        unfold conjugate
        rw [map_map]
        congr 1
        ext x
        simp [mul_assoc]
      _ = conjugate F.W h := by rw [hkW]
  obtain ⟨ht, ht1⟩ := F.binaryCoreProjection_involution L e hcore hindex u hu huw
  exact d.natural_tensor_and_marks_of_subgroup_pair σ (F.binaryCoreProjection L e)
    F.U F.W (F.X g) u ⟨h, hh⟩ hu hfactorS rfl hX hUW hUS ht ht1

/-- Construct the literal elementary section and its full natural action
from the original source inputs. No binary quotient, representation, marked
decomposition or natural-module witness is assumed. The multiplicity space
is finite, and every original element of U−W has the prescribed marks. -/
public theorem binary_natural_quotient
    (F : InvariantFlag T V n) [IsMulCommutative V] (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) (g : G) (hgP : g ∈ F.P L)
    (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L)
    (hPH : (F.P L).pCoreIn 2 ≤ F.H)
    (hgen : F.U ⊔ conjugate F.U g = F.I₂ L)
    (e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* S₃)
    (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2)
    (hindex : F.W.relIndex F.U = 2) (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1) :
    letI := F.binary_source_E_normal_in_core L hL g hgP hgen hcomm
    letI := F.binary_source_quotient_elementary L hL g hgP hgen hcore
      (F.binary_core_normalizes_U L hfactor hPH)
      (F.binary_core_factorization L g hgP hfactor hPH hgen e hcore hindex) hcomm hsquare
    ∃ (σ : Representation (ZMod 2) S₃
        (Additive (((F.I₂ L).pCoreIn 2) ⧸ (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2))))
      (d : Representation.BinaryConjugationSection (F.I₂ L) ((F.I₂ L).pCoreIn 2)
        (F.E g) (σ.comp (F.binaryCoreProjection L e))),
      (∀ s : (F.I₂ L).pCoreIn 2, (d.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)) s)) ∧
      Finite (multiplicitySpace σ) ∧
      (∃ j : multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2]
            Additive (((F.I₂ L).pCoreIn 2) ⧸ (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)),
          ∀ a z, j ((Representation.tprod (Representation.trivial (ZMod 2) S₃
              (multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a z) =
            σ a (j z)) ∧
      ∀ u : F.I₂ L, (u : G) ∈ F.U → (u : G) ∉ F.W →
          LinearMap.ker (σ (F.binaryCoreProjection L e u) - 1) = d.imageSpace F.W ∧
          LinearMap.range (σ (F.binaryCoreProjection L e u) - 1) = d.imageSpace F.W ∧
          (d.imageSpace (F.X g)).map (σ (F.binaryCoreProjection L e u) - 1) =
            d.imageSpace F.W := by
  have hnorm := F.binary_core_normalizes_U L hfactor hPH
  have hsplit := F.binary_core_factorization L g hgP hfactor hPH hgen e hcore hindex
  let := F.binary_source_E_normal_in_core L hL g hgP hgen hcomm
  let := F.binary_source_quotient_elementary L hL g hgP hgen hcore hnorm hsplit hcomm hsquare
  have hES : F.E g ≤ (F.I₂ L).pCoreIn 2 := inf_le_left.trans (le_sup_left.trans hsplit.ge)
  have hNS : F.I₂ L ≤ normalizer ((F.I₂ L).pCoreIn 2 : Set G) :=
    (F.I₂ L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L)))
  have hπ : Function.Surjective (F.binaryCoreProjection L e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : (F.binaryCoreProjection L e).ker = ((F.I₂ L).pCoreIn 2).subgroupOf (F.I₂ L) := by
    rw [F.binaryCoreProjection_ker L e]
    exact ((pCore 2 (F.I₂ L)).comap_map_eq_self_of_injective (F.I₂ L).subtype_injective).symm
  obtain ⟨σ, d, hc⟩ := Representation.BinaryConjugationSection.exists_canonical
    (F.I₂ L) ((F.I₂ L).pCoreIn 2) (F.E g) (pCoreIn_le 2 (F.I₂ L)) hES hNS
    (F.binary_source_E_normalized L hL g hgP hgen hcomm) (F.binaryCoreProjection L e) hπ hk
  have hex : ∃ v : G, v ∈ F.U ∧ v ∉ F.W := by
    by_contra! h
    have he : F.W.relIndex F.U = 1 := relIndex_eq_one.mpr h
    omega
  obtain ⟨v, hv, hvw⟩ := hex
  have hUI : F.U ≤ F.I₂ L := le_conjugateSpanBy _ _
  obtain ⟨hm, _⟩ := F.binary_natural_module_and_marks L hL g hgP hfactor hPH hgen e hcore
    hindex hcomm σ d ⟨v, hUI hv⟩ hv hvw
  refine ⟨σ, d, hc, inferInstance, hm, ?_⟩
  intro u hu huw
  exact (F.binary_natural_module_and_marks L hL g hgP hfactor hPH hgen e hcore hindex
    hcomm σ d u hu huw).2

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
