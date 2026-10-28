module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.Sections
public import Theory.Representation.InvertedFiveTensor.Marked
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.CoreAction

/-!
# The two dihedral marked tensor rows of 8.2.8(5)

The fixed-point-free rotation on the literal P/U constructs its F₄ scalars.
A lift of the inverter in the elementary abelian V fixes the literal B/U,
where B=V∩P. The two-copy dimension identity then identifies B/U with the
entire inverter-fixed space. Thus the original inclusion, rather than an
unrelated multiplicity space, is the distinguished line of the tensor.

This construction applies to both the L₃(4) and M₂₄ code dihedral rows.
E.2.14 supplies the marked dihedral action and its rotation fixed-point
freeness, and 8.2.5 supplies the two-copy rank identity. Selection of the
row and discharge of those earlier-source inputs remain with the normalizer
assembly. The cocode SL₂(4) row requires its separate scalar recognition.

In the canonical application the ambient group is the local group Y=R I;
normality of I and U is relative to Y.

Source: Aschbacher–Smith, Proposition 8.2.8(5), printed pp.718–719.
-/

public section
open Subgroup InvertedFiveTensor
open scoped TensorProduct IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
variable {G K : Type*} [Group G] [Group K] [Finite G]
  (I V U : Subgroup G)
  [(U.subgroupOf (I.pCoreIn 2)).Normal]
  [(U.subgroupOf (V ⊓ I.pCoreIn 2 : Subgroup G)).Normal]
  [IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))]
  [IsElementaryAbelian 2 ((V ⊓ I.pCoreIn 2 : Subgroup G) ⧸ U.subgroupOf (V ⊓ I.pCoreIn 2))]

omit [Finite G] in
/-- Conjugation by the actual inverter lift fixes the original quotient B/U. -/
theorem dihedral_inverter_fixes_intersection [IsElementaryAbelian 2 V]
    (σ : Representation (ZMod 2) D (CoreSection I U)) (v : V)
    (hn : (v : G) ∈ normalizer (I.pCoreIn 2 : Set G))
    (ha : ∀ p : I.pCoreIn 2,
      σ invt (Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) p)) =
        Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2))
          ⟨(v : G) * (p : G) * (v : G)⁻¹,
            (mem_normalizer_iff.mp hn p).mp p.property⟩)) :
    ∀ b : IntersectionSection I V U,
      σ invt (intersectionInclusion I V U b) = intersectionInclusion I V U b := by
  intro b
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf (V ⊓ I.pCoreIn 2)) b.toMul
  change σ invt (quotientInclusion (I.pCoreIn 2) (V ⊓ I.pCoreIn 2) U inf_le_right
    (Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (V ⊓ I.pCoreIn 2)) b))) = _
  rw [quotientInclusion_mk, ha]
  have hc : (v : G) * (b : G) = (b : G) * (v : G) :=
    congrArg Subtype.val (mul_comm v (⟨b, b.property.1⟩ : V))
  let p : I.pCoreIn 2 := ⟨b, b.property.2⟩
  have hq : QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2))
      ⟨(v : G) * (p : G) * (v : G)⁻¹, (mem_normalizer_iff.mp hn (p : G)).mp p.property⟩ =
      QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) p := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (v : G) * (b : G) * (v : G)⁻¹ / (b : G) ∈ U
    rw [hc, mul_inv_cancel_right]
    simp
  exact congrArg Additive.ofMul hq

/-- The dihedral tensor constructs F₄ on both original quotients and marks
its first coordinate using their literal quotient maps. -/
theorem dihedral_marked_tensor
    (σ : Representation (ZMod 2) D (CoreSection I U))
    (κ : Representation (ZMod 2) K (CoreSection I U))
    (τ : Representation (ZMod 2) K (IntersectionSection I V U))
    (hc : ∀ k g p, κ k (σ g p) = σ g (κ k p))
    (he : ∀ k b, intersectionInclusion I V U (τ k b) = κ k (intersectionInclusion I V U b))
    (hf : ∀ p, σ rot p = p → p = 0)
    (hfix : ∀ b, σ invt (intersectionInclusion I V U b) = intersectionInclusion I V U b)
    (hd : Module.finrank (ZMod 2) (CoreSection I U) =
      2 * Module.finrank (ZMod 2) (IntersectionSection I V U)) :
    letI := fieldModule σ hf
    ∃ mB : Module F (IntersectionSection I V U), letI := mB
      IsScalarTower (ZMod 2) F (IntersectionSection I V U) ∧
      ∃ τF : Representation F K (IntersectionSection I V U), (∀ k b, τF k b = τ k b) ∧
      ∃ e : (Fin 2 → F) ⊗[F] IntersectionSection I V U ≃ₗ[F] CoreSection I U,
        (∀ n b, e (n ⊗ₜ[F] b) = n 0 • intersectionInclusion I V U b +
          n 1 • σ rot (intersectionInclusion I V U b)) ∧
        (∀ b : ↥(V ⊓ I.pCoreIn 2),
          e (![1, 0] ⊗ₜ[F] Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (V ⊓ I.pCoreIn 2)) b)) =
            Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) ⟨b, b.property.2⟩)) ∧
        ∀ k g z, e (TensorProduct.map (natural g) (τF k) z) = κ k (σ g (e z)) := by
  obtain ⟨mB, htower, τF, hτ, e, ht, heq⟩ := marked_tensor σ hf
    (intersectionInclusion I V U)
    (quotientInclusion_injective (I.pCoreIn 2) (V ⊓ I.pCoreIn 2) U inf_le_right)
    hfix hd κ τ hc he
  let := fieldModule σ hf
  let := mB
  refine ⟨mB, htower, τF, hτ, e, ht, ?_, heq⟩
  intro b
  rw [ht]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_smul, zero_smul, add_zero]
  rfl

/-- The original inverter lift discharges fixedness, so the two dihedral
source rows need no assumed identification of B/U with a multiplicity space. -/
theorem dihedral_marked_tensor_of_inverter [IsElementaryAbelian 2 V]
    (σ : Representation (ZMod 2) D (CoreSection I U))
    (κ : Representation (ZMod 2) K (CoreSection I U))
    (τ : Representation (ZMod 2) K (IntersectionSection I V U))
    (hc : ∀ k g p, κ k (σ g p) = σ g (κ k p))
    (he : ∀ k b, intersectionInclusion I V U (τ k b) = κ k (intersectionInclusion I V U b))
    (hf : ∀ p, σ rot p = p → p = 0)
    (v : V) (hn : (v : G) ∈ normalizer (I.pCoreIn 2 : Set G))
    (ha : ∀ p : I.pCoreIn 2,
      σ invt (Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) p)) =
        Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2))
          ⟨(v : G) * (p : G) * (v : G)⁻¹,
            (mem_normalizer_iff.mp hn p).mp p.property⟩))
    (hd : Module.finrank (ZMod 2) (CoreSection I U) =
      2 * Module.finrank (ZMod 2) (IntersectionSection I V U)) :
    letI := fieldModule σ hf
    ∃ mB : Module F (IntersectionSection I V U), letI := mB
      IsScalarTower (ZMod 2) F (IntersectionSection I V U) ∧
      ∃ τF : Representation F K (IntersectionSection I V U), (∀ k b, τF k b = τ k b) ∧
      ∃ e : (Fin 2 → F) ⊗[F] IntersectionSection I V U ≃ₗ[F] CoreSection I U,
        (∀ n b, e (n ⊗ₜ[F] b) = n 0 • intersectionInclusion I V U b +
          n 1 • σ rot (intersectionInclusion I V U b)) ∧
        (∀ b : ↥(V ⊓ I.pCoreIn 2),
          e (![1, 0] ⊗ₜ[F] Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (V ⊓ I.pCoreIn 2)) b)) =
            Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) ⟨b, b.property.2⟩)) ∧
        ∀ k g z, e (TensorProduct.map (natural g) (τF k) z) = κ k (σ g (e z)) :=
  dihedral_marked_tensor I V U σ κ τ hc he hf
    (dihedral_inverter_fixes_intersection I V U σ v hn ha) hd

/-- Application to the canonical conjugation action on P/U. The model
isomorphism marks the actual I/O₂(I) quotient map, and the tensor action
is conjugation by the original product r*i in the local group. -/
theorem dihedral_tensor_of_quotient_action [IsElementaryAbelian 2 V] [I.Normal] [U.Normal]
    (R : Subgroup G) (eI : (I ⧸ pCore 2 I) ≃* D)
    (σ : Representation (ZMod 2) D (CoreSection I U))
    (κ : Representation (ZMod 2) R (CoreSection I U))
    (τ : Representation (ZMod 2) R (IntersectionSection I V U))
    (hc : ∀ k g p, κ k (σ g p) = σ g (κ k p))
    (he : ∀ k b, intersectionInclusion I V U (τ k b) = κ k (intersectionInclusion I V U b))
    (hf : ∀ p, σ rot p = p → p = 0)
    (hσ : ∀ (i : I) p,
      σ (eI (QuotientGroup.mk' (pCore 2 I) i)) p =
        Additive.ofMul (coreQuotientAction I U i p.toMul))
    (hκ : ∀ (r : R) p, κ r p = Additive.ofMul (coreQuotientAction I U r p.toMul))
    (v : V) (hvI : (v : G) ∈ I)
    (hv : eI (QuotientGroup.mk' (pCore 2 I) ⟨v, hvI⟩) = invt)
    (hd : Module.finrank (ZMod 2) (CoreSection I U) =
      2 * Module.finrank (ZMod 2) (IntersectionSection I V U)) :
    letI := fieldModule σ hf
    ∃ mB : Module F (IntersectionSection I V U), letI := mB
      IsScalarTower (ZMod 2) F (IntersectionSection I V U) ∧
      ∃ τF : Representation F R (IntersectionSection I V U), (∀ k b, τF k b = τ k b) ∧
      ∃ e : (Fin 2 → F) ⊗[F] IntersectionSection I V U ≃ₗ[F] CoreSection I U,
        (∀ n b, e (n ⊗ₜ[F] b) = n 0 • intersectionInclusion I V U b +
          n 1 • σ rot (intersectionInclusion I V U b)) ∧
        (∀ b : ↥(V ⊓ I.pCoreIn 2),
          e (![1, 0] ⊗ₜ[F] Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (V ⊓ I.pCoreIn 2)) b)) =
            Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) ⟨b, b.property.2⟩)) ∧
        ∀ (r : R) (i : I) z,
          e (TensorProduct.map (natural (eI (QuotientGroup.mk' (pCore 2 I) i))) (τF r) z) =
            Additive.ofMul (coreQuotientAction I U ((r : G) * (i : G)) (e z).toMul) := by
  let _ : (I.pCoreIn 2).Normal := by unfold pCoreIn; infer_instance
  have hn : (v : G) ∈ normalizer (I.pCoreIn 2 : Set G) :=
    le_normalizer_of_normal (mem_top _)
  have ha (p : I.pCoreIn 2) :
      σ invt (Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) p)) =
        Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2))
          ⟨(v : G) * (p : G) * (v : G)⁻¹,
            (mem_normalizer_iff.mp hn p).mp p.property⟩) := by
    have hh := hσ ⟨v, hvI⟩ (Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) p))
    rw [hv] at hh
    rw [hh]
    change Additive.ofMul (coreQuotientAction I U (v : G)
      (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) p)) = _
    rw [coreQuotientAction_mk]
    rfl
  obtain ⟨mB, hT, τF, hτ, e, ht, hm, heq⟩ :=
    dihedral_marked_tensor_of_inverter I V U σ κ τ hc he hf v hn ha hd
  let := fieldModule σ hf
  let := mB
  refine ⟨mB, hT, τF, hτ, e, ht, hm, ?_⟩
  intro r i z
  rw [heq, hκ, hσ, map_mul]
  rfl

end CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
