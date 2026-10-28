module

public import CFSG.Quasithin.ChapterG.Section02.Binary.Quotient
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# Natural modules in the binary almost-special quotient

Conjugation on the actual elementary quotient S/S₂ factors through I/S:
the kernel acts by inner automorphisms of an abelian group. The complementary
marked factors and their quadratic action then construct an equivariant
natural S₃ tensor decomposition, with its fixed and moved spaces. No
semisimplicity or module-decomposition hypothesis is used.

Source: Aschbacher–Smith, G.2.3(6), printed p.334. Earlier S₃ recognition,
the index-two image and normalization by the core remain explicit.
-/

open Subgroup InvertedCubicTensor
open scoped IsMulCommutative _root_.TensorProduct

namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]

/-- The source action quotient of I₂ by its actual two-core. -/
public def binaryCoreProjection (D : Setup G) (g : G)
    (e : ((D.I g) ⧸ pCore 2 (D.I g)) ≃* S₃) : D.I g →* S₃ :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I g)))

omit [Finite G] in
/-- The action projection is the quotient map followed by the chosen equivalence. -/
public theorem binaryCoreProjection_eq (D : Setup G) (g : G)
    (e : ((D.I g) ⧸ pCore 2 (D.I g)) ≃* S₃) :
    D.binaryCoreProjection g e =
      e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I g))) := by
  unfold binaryCoreProjection
  rfl

omit [Finite G] in
private theorem binaryCoreProjection_ker (D : Setup G) (g : G)
    (e : ((D.I g) ⧸ pCore 2 (D.I g)) ≃* S₃) :
    (D.binaryCoreProjection g e).ker = pCore 2 (D.I g) := by
  ext i
  change e (QuotientGroup.mk i) = 1 ↔ i ∈ pCore 2 (D.I g)
  constructor
  · intro hi
    exact (QuotientGroup.eq_one_iff i).mp (e.injective (hi.trans e.map_one.symm))
  · intro hi
    rw [(QuotientGroup.eq_one_iff i).mpr hi, map_one]

omit [Finite G] in
private theorem binaryCoreProjection_involution
    (D : Setup G) (g : G)
    (e : ((D.I g) ⧸ pCore 2 (D.I g)) ≃* S₃)
    (hindex : (D.W g).relIndex D.U = 2)
    (u : D.I g) (hu : (u : G) ∈ D.U) (huw : (u : G) ∉ D.W g) :
    (D.binaryCoreProjection g e u) ^ 2 = 1 ∧ D.binaryCoreProjection g e u ≠ 1 := by
  let I := D.I g
  let U := D.U.subgroupOf I
  let f := D.binaryCoreProjection g e
  have hk : f.ker = pCore 2 I := D.binaryCoreProjection_ker g e
  have hUI : D.U ≤ I := le_sup_left
  have hW : D.U ⊓ I.pCoreIn 2 = D.W g := rfl
  have hUf : Nat.card (U.map f) = 2 := by
    rw [← relIndex_ker U f, hk]
    have he := relIndex_map_map_of_injective (pCore 2 I) U I.subtype_injective
    rw [show U.map I.subtype = D.U from map_subgroupOf_eq_of_le hUI] at he
    change (I.pCoreIn 2).relIndex D.U = (pCore 2 I).relIndex U at he
    rw [← he, ← inf_relIndex_left, hW]
    exact hindex
  constructor
  · have hp := pow_card_eq_one' (x := (⟨f u, mem_map_of_mem f hu⟩ : U.map f))
    rw [hUf] at hp
    exact congrArg Subtype.val hp
  · intro he
    have huS : (u : G) ∈ I.pCoreIn 2 :=
      mem_map_of_mem I.subtype (hk ▸ (show u ∈ f.ker from he))
    exact huw (hW ▸ (show (u : G) ∈ D.U ⊓ I.pCoreIn 2 from ⟨hu, huS⟩))


/-- The marked natural module, once the literal quotient representation
has been constructed. Every original element of U−W gives the same marks. -/
public theorem binary_natural_module_and_marks (D : Setup G) (g : G)
    (hg : g ∈ D.I g)
    (e : ((D.I g) ⧸ pCore 2 (D.I g)) ≃* S₃)
    (hnorm : D.S g ≤ normalizer (D.U : Set G))
    (hindex : (D.W g).relIndex D.U = 2)
    (hVE : D.V ≤ D.S₂ g) (hES : D.S₂ g ≤ D.S g)
    (hpoint : D.V₁ ≤ D.V) (hcomm : ⁅D.U, D.U⁆ ≤ D.V₁)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) S₃ M)
    (d : Representation.BinaryConjugationSection (D.I g) (D.S g)
      (D.S₂ g) (σ.comp (D.binaryCoreProjection g e)))
    (u : D.I g) (hu : (u : G) ∈ D.U) (huw : (u : G) ∉ D.W g) :
    (∃ j : multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2] M,
      ∀ a z, j ((Representation.tprod (Representation.trivial (ZMod 2) S₃
          (multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a z) =
        σ a (j z)) ∧
      LinearMap.ker (σ (D.binaryCoreProjection g e u) - 1) = d.imageSpace (D.W g) ∧
      LinearMap.range (σ (D.binaryCoreProjection g e u) - 1) = d.imageSpace (D.W g) ∧
      (d.imageSpace (conjugate (D.W g) g)).map (σ (D.binaryCoreProjection g e u) - 1) =
        d.imageSpace (D.W g) := by
  have hUS : ⁅D.U, D.S g⁆ ≤ D.W g :=
    le_inf (le_normalizer_iff_commutator_le_left.mp hnorm)
      (le_normalizer_iff_commutator_le_right.mp
        ((show D.U ≤ D.I g from le_sup_left).trans (D.binary_core_normalized g)))
  have hUW : ⁅D.U, D.W g⁆ ≤ D.S₂ g :=
    ((commutator_mono le_rfl (show D.W g ≤ D.U from inf_le_left)).trans hcomm).trans
      (hpoint.trans hVE)
  obtain ⟨ht, ht1⟩ := D.binaryCoreProjection_involution g e hindex u hu huw
  exact d.natural_tensor_and_marks_of_subgroup_pair σ (D.binaryCoreProjection g e)
    D.U (D.W g) (conjugate (D.W g) g) u ⟨g, hg⟩ hu
    (D.binary_core_factorization g hg e hnorm hindex)
    (D.binary_marked_intersection g hg hES) rfl hUW hUS ht ht1

/-- Construct the literal quotient and its action from the earlier
rank-one layer bounds, with no elementary-quotient or action witness. -/
public theorem binary_natural_quotient (D : Setup G) (g : G)
    (hg : g ∈ D.I g) (hgV : g ∈ normalizer (D.V : Set G))
    (hpoint : D.V₁ ≤ D.V) (hVE : D.V ≤ D.S₂ g) (hES : D.S₂ g ≤ D.S g)
    (hEN : D.I g ≤ normalizer (D.S₂ g : Set G))
    (e : ((D.I g) ⧸ pCore 2 (D.I g)) ≃* S₃)
    (hnorm : D.S g ≤ normalizer (D.U : Set G))
    (hindex : (D.W g).relIndex D.U = 2)
    (hcomm : ⁅D.U, D.U⁆ ≤ D.V₁) (hsquare : ∀ u ∈ D.U, u ^ 2 ∈ D.V₁) :
    letI : ((D.S₂ g).subgroupOf (D.S g)).Normal := normal_subgroupOf_of_le_normalizer ((pCoreIn_le 2 (D.I g)).trans hEN)
    letI := D.binary_quotient_elementary g hg hgV hpoint hVE hES hEN hnorm
      (D.binary_core_factorization g hg e hnorm hindex) hsquare
    ∃ (σ : Representation (ZMod 2) S₃
        (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))
      (d : Representation.BinaryConjugationSection (D.I g) (D.S g)
        (D.S₂ g) (σ.comp (D.binaryCoreProjection g e))),
      (∀ s : D.S g, (d.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((D.S₂ g).subgroupOf (D.S g)) s)) ∧
      Finite (multiplicitySpace σ) ∧
      IsCompl (d.imageSpace (D.W g)) (d.imageSpace (conjugate (D.W g) g)) ∧
      (∃ j : multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2]
            Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g)),
          ∀ a z, j ((Representation.tprod (Representation.trivial (ZMod 2) S₃
              (multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a z) =
            σ a (j z)) ∧
      ∀ u : D.I g, (u : G) ∈ D.U → (u : G) ∉ D.W g →
          LinearMap.ker (σ (D.binaryCoreProjection g e u) - 1) = d.imageSpace (D.W g) ∧
          LinearMap.range (σ (D.binaryCoreProjection g e u) - 1) = d.imageSpace (D.W g) ∧
          (d.imageSpace (conjugate (D.W g) g)).map (σ (D.binaryCoreProjection g e u) - 1) =
            d.imageSpace (D.W g) := by
  have hsplit := D.binary_core_factorization g hg e hnorm hindex
  let : ((D.S₂ g).subgroupOf (D.S g)).Normal := normal_subgroupOf_of_le_normalizer ((pCoreIn_le 2 (D.I g)).trans hEN)
  let := D.binary_quotient_elementary g hg hgV hpoint hVE hES hEN hnorm hsplit hsquare
  have hπ : Function.Surjective (D.binaryCoreProjection g e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : (D.binaryCoreProjection g e).ker = (D.S g).subgroupOf (D.I g) := by
    rw [D.binaryCoreProjection_ker g e]
    exact ((pCore 2 (D.I g)).comap_map_eq_self_of_injective (D.I g).subtype_injective).symm
  obtain ⟨σ, d, hc⟩ := Representation.BinaryConjugationSection.exists_canonical
    (D.I g) (D.S g) (D.S₂ g) (pCoreIn_le 2 (D.I g)) hES
    (D.binary_core_normalized g) hEN (D.binaryCoreProjection g e) hπ hk
  have hex : ∃ v : G, v ∈ D.U ∧ v ∉ D.W g := by
    by_contra! h
    have he : (D.W g).relIndex D.U = 1 := relIndex_eq_one.mpr h
    omega
  obtain ⟨v, hv, hvw⟩ := hex
  have hUI : D.U ≤ D.I g := le_sup_left
  obtain ⟨hm, _⟩ := D.binary_natural_module_and_marks g hg e hnorm hindex hVE hES
    hpoint hcomm σ d ⟨v, hUI hv⟩ hv hvw
  refine ⟨σ, d, hc, inferInstance, ?_, hm, ?_⟩
  · exact d.isCompl_imageSpace _ _ hsplit (D.binary_marked_intersection g hg hES)
  · intro u hu huw
    exact (D.binary_natural_module_and_marks g hg e hnorm hindex hVE hES
      hpoint hcomm σ d u hu huw).2

end CFSG.Quasithin.ChapterG.Section02.Setup
