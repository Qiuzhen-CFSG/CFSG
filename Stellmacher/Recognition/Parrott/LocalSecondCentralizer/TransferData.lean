module

public import Stellmacher.Recognition.Parrott.SecondCentralizerUnrestrictedContainment
public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Sylow

/-!
# The literal second-transfer configuration

The two transfers produce nested index-two subgroups M of C_G(v) and L of M.
The image Y of a Sylow two-subgroup of L has order 128, omega subgroup F,
and center Z(Ω₁(O₂(N_G(F)))). The compatible order-four root is excluded
from L. All embeddings below are the original subgroup inclusions.

This is an interface for the transfer construction, not an existence assertion.
The quotient is formed by the actual lift of v in L. Quotient-centralizer
containment then supplies the unrestricted ambient-containment theorem.

Source: Parrott (1972), Lemma 8, printed pp.682–683.
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
  {d : ParrottSecondElementaryData z} (n : ParrottNormalizerFusionData d)

/-- The two transfer subgroups and their actual Sylow image, with no
ambient centralizer-containment or quotient-centralizer premise. -/
public structure ParrottSecondTransferData where
  M : Subgroup (centralizer ({n.v} : Set G))
  L : Subgroup M
  M_normal : M.Normal
  M_index : M.index = 2
  M_inf_sylow : M.map (centralizer ({n.v} : Set G)).subtype ⊓
    ((d.sylow : Subgroup G) ⊓ centralizer ({n.v} : Set G)) =
      (omega₁ (pCore 2 (normalizer (d.F : Set G))) (p := 2)).map
        ((normalizer (d.F : Set G)).subtype.comp (pCore 2 (normalizer (d.F : Set G))).subtype)
  L_normal : L.Normal
  L_index : L.index = 2
  b : G
  b_mem_core : b ∈ (pCore 2 (normalizer (d.F : Set G))).map
    (normalizer (d.F : Set G)).subtype
  b_order : orderOf b = 4
  b_sq : b ^ 2 = n.v
  core_fixed : (pCore 2 (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype ⊓
      centralizer ((n.Q : Subgroup (normalizer (d.F : Set G))).map
        (normalizer (d.F : Set G)).subtype : Set G) = zpowers b
  b_not_mem : b ∉ L.map ((centralizer ({n.v} : Set G)).subtype.comp M.subtype)
  Y_card : Nat.card
    ((omega₁ (pCore 2 (normalizer (d.F : Set G))) (p := 2)).map
      ((normalizer (d.F : Set G)).subtype.comp (pCore 2 (normalizer (d.F : Set G))).subtype) ⊓
      L.map ((centralizer ({n.v} : Set G)).subtype.comp M.subtype) : Subgroup G) = 128
  Y_omega :
    let W := (omega₁ (pCore 2 (normalizer (d.F : Set G))) (p := 2)).map
      ((normalizer (d.F : Set G)).subtype.comp (pCore 2 (normalizer (d.F : Set G))).subtype)
    let Y := W ⊓ L.map ((centralizer ({n.v} : Set G)).subtype.comp M.subtype)
    (omega₁ Y (p := 2)).map Y.subtype = d.F
  Y_center :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let Y := W ⊓ L.map ((centralizer ({n.v} : Set G)).subtype.comp M.subtype)
    (center Y).map Y.subtype = (center (omega₁ K (p := 2))).map
      ((N.subtype.comp K.subtype).comp (omega₁ K (p := 2)).subtype)
  S : Sylow 2 L
  S_image :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    (S : Subgroup L).map ((centralizer ({n.v} : Set G)).subtype.comp
      (M.subtype.comp L.subtype)) =
      W ⊓ L.map ((centralizer ({n.v} : Set G)).subtype.comp M.subtype)

namespace ParrottSecondTransferData
variable {n} (t : ParrottSecondTransferData n)

/-- The original inclusion of the second-transfer group in the ambient group. -/
@[expose] public def embedding : t.L →* G :=
  (centralizer ({n.v} : Set G)).subtype.comp (t.M.subtype.comp t.L.subtype)

public theorem embedding_injective : Function.Injective t.embedding :=
  (centralizer ({n.v} : Set G)).subtype_injective.comp
    (t.M.subtype_injective.comp t.L.subtype_injective)

public theorem embedding_range_le_centralizer :
    t.embedding.range ≤ centralizer ({n.v} : Set G) := by
  rintro _ ⟨x, rfl⟩
  exact x.val.val.property

public theorem elementary_le_sylow_image :
    d.F ≤ (t.S : Subgroup t.L).map t.embedding := by
  change d.F ≤ (t.S : Subgroup t.L).map
    ((centralizer ({n.v} : Set G)).subtype.comp (t.M.subtype.comp t.L.subtype))
  rw [t.S_image]
  exact t.Y_omega.symm.le.trans (map_subtype_le _)

public theorem exists_lift : ∃ v : t.L, t.embedding v = n.v := by
  obtain ⟨v, _, hv⟩ := t.elementary_le_sylow_image n.v_mem_inf.2
  exact ⟨v, hv⟩

/-- The actual lift of the specified involution; injectivity makes it unique. -/
public noncomputable def v : t.L := t.exists_lift.choose

public theorem v_image : t.embedding t.v = n.v := t.exists_lift.choose_spec

public theorem v_mem_center : t.v ∈ center t.L := by
  apply mem_center_iff.mpr
  intro x
  apply t.embedding_injective
  simp only [map_mul, t.v_image]
  exact mem_centralizer_singleton_iff.mp (t.embedding_range_le_centralizer ⟨x, rfl⟩)

public instance v_zpowers_normal : (zpowers t.v).Normal := by
  constructor
  intro x hx g
  rw [mem_center_iff.mp ((zpowers_le.mpr t.v_mem_center) hx) g, mul_inv_cancel_right]
  exact hx

/-- The literal quotient of L by its chosen central involution. -/
public abbrev Quotient := t.L ⧸ zpowers t.v

/-- The Sylow image under the literal quotient map. -/
@[expose] public noncomputable def quotientSylow : Subgroup t.Quotient :=
  (t.S : Subgroup t.L).map (QuotientGroup.mk' (zpowers t.v))

/-- The final unrestricted containment application. The quotient-centralizer
premise is the remaining calculation on this very transfer quotient. -/
public theorem le_normalizer_of_quotient_centralizers [Finite G]
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hcent : ∀ x ∈ t.quotientSylow, orderOf x = 2 →
      centralizer ({x} : Set t.Quotient) ≤ t.quotientSylow) :
    centralizer ({n.v} : Set G) ≤ normalizer (d.F : Set G) := by
  exact n.second_centralizer_le_normalizer_of_quotient_centralizers h
    t.M t.L t.M_index t.M_inf_sylow t.L_normal t.Y_omega
    (d.normalizer_fixed_sylow_card_of_local_inputs h hlocal n.sylow_lt_normalizer
      n.Q n.v n.v_order n.elementary_fixed)
    t.S t.S_image t.Quotient t.v t.v_image (QuotientGroup.mk' (zpowers t.v))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hcent

end ParrottSecondTransferData
end Stellmacher.Recognition
