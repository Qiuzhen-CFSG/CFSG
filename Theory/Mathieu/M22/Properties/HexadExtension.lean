module

public import Theory.Mathieu.M22.Properties.HexadExtension.Kernel
public import Theory.Mathieu.M22.Properties.LocalSubgroups
public import Theory.GroupTheory.AlternatingBySixteen

/-!
# Hexad stabilizers in M22 are E16-by-A6

The kernel of the actual six-point restriction is the binary translation
kernel of the augmented M23 heptad. Three-transitivity and unique hexad
extension give order 5760 for every hexad stabilizer. Thus the restriction
image has order 360 and index two in S6, so it is exactly A6. The first
isomorphism theorem supplies the quotient equivalence.

This establishes the extension shape in Aschbacher--Smith 2.3.9(7)(f),
printed p.525, without asserting or requiring a splitting.
-/

@[expose] public section
namespace Sporadic.Mathieu
open scoped Pointwise
open Theory.GroupTheory

/-- Label the six points of a hexad. -/
noncomputable def m22HexadLabels {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    B ≃ Fin 6 := Fintype.equivFinOfCardEq (by simpa using m22Block_card B hB)

/-- The restriction action on six labels, retaining the actual point action. -/
noncomputable def m22HexadAction {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    MulAction.stabilizer M22 B →* Equiv.Perm (Fin 6) :=
  (m22HexadLabels hB).permCongrHom.toMonoidHom.comp (m22SetAction B)

@[simp] theorem m22HexadAction_apply {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : MulAction.stabilizer M22 B) (a : B) :
    m22HexadAction hB g (m22HexadLabels hB a) =
      m22HexadLabels hB (m22SetAction B g a) := by
  change m22HexadLabels hB (m22SetAction B g
    ((m22HexadLabels hB).symm (m22HexadLabels hB a))) = _
  rw [Equiv.symm_apply_apply]

/-- Labelling preserves the actual pointwise kernel. -/
theorem m22HexadAction_ker {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (m22HexadAction hB).ker = (m22SetAction B).ker :=
  MonoidHom.ker_mulEquiv_comp _ (m22HexadLabels hB).permCongrHom

/-- Every hexad is a translate of the standard hexad in the degree-22 action. -/
theorem exists_smul_m22Hexad123_eq {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ∃ g : M22, g • m22Hexad123 = B := by
  classical
  let e : Fin 6 ≃ B := (m22HexadLabels hB).symm
  let e₀ : Fin 6 ≃ m22Hexad123 := (m22HexadLabels m22Hexad123_mem).symm
  let j : Fin 3 ↪ Fin 6 := Fin.castLEEmb (by decide)
  let a : Fin 3 ↪ Fin 22 := (j.trans e₀.toEmbedding).trans (Function.Embedding.subtype _)
  let b : Fin 3 ↪ Fin 22 := (j.trans e.toEmbedding).trans (Function.Embedding.subtype _)
  obtain ⟨g, hg⟩ := (MulAction.isMultiplyPretransitive_iff.mp
    m22_isThreePretransitive) a b
  have happ (i : Fin 3) : g • a i = b i :=
    congrArg (fun f : Fin 3 ↪ Fin 22 => f i) hg
  refine ⟨g, m22Blocks_eq_of_common_triple (Finset.univ.image b) _ _ ?_
    (m22_smul_block_mem g _ m22Hexad123_mem) hB ?_ ?_⟩
  · rw [Finset.card_image_of_injective _ b.injective, Finset.card_univ, Fintype.card_fin]
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    rw [← happ i]
    exact Finset.smul_mem_smul_finset (e₀ (j i)).property
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact (e (j i)).property

/-- Every hexad stabilizer has order 5760. -/
theorem m22Hexad_stabilizer_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Nat.card (MulAction.stabilizer M22 B) = 5760 := by
  obtain ⟨g, hg⟩ := exists_smul_m22Hexad123_eq hB
  exact (Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv).symm.trans
    m22HexadStabilizer_card

/-- The six-point restriction image is exactly A6. -/
theorem m22HexadAction_range {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (m22HexadAction hB).range = alternatingGroup (Fin 6) := by
  have hk : Nat.card (m22HexadAction hB).ker = 16 := by
    rw [m22HexadAction_ker hB]
    exact m22HexadKernel_card hB
  have hr : Nat.card (m22HexadAction hB).range = 360 := by
    rw [← Subgroup.index_ker]
    have hc := Subgroup.card_mul_index (m22HexadAction hB).ker
    rw [hk, m22Hexad_stabilizer_card hB] at hc
    omega
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have hc := Subgroup.card_mul_index (m22HexadAction hB).range
  rw [hr] at hc
  have hp : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  rw [hp] at hc
  omega

/-- The actual quotient by the pointwise hexad kernel is the alternating group on six points. -/
noncomputable def m22HexadQuotientAlternatingEquiv {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) :
    ((MulAction.stabilizer M22 B) ⧸ (m22SetAction B).ker) ≃* alternatingGroup (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq (m22HexadAction_ker hB).symm).trans
    ((QuotientGroup.quotientKerEquivRange (m22HexadAction hB)).trans
      (MulEquiv.subgroupCongr (m22HexadAction_range hB)))

/-- The quotient equivalence is induced by the restriction to the six hexad points. -/
@[simp] theorem m22HexadQuotientAlternatingEquiv_mk {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) (g : MulAction.stabilizer M22 B) :
    (m22HexadQuotientAlternatingEquiv hB (QuotientGroup.mk g) : Equiv.Perm (Fin 6)) =
      m22HexadAction hB g := rfl

/-- Normality is relative to the actual hexad stabilizer. -/
theorem m22HexadKernel_normal (B : Finset (Fin 22)) : (m22SetAction B).ker.Normal :=
  inferInstance

/-- The complete pointwise-kernel extension statement for every hexad. -/
theorem m22Hexad_pointwise_extension {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    IsElementaryAbelian 2 (m22SetAction B).ker ∧
    Nat.card (m22SetAction B).ker = 16 ∧
    Nonempty (((MulAction.stabilizer M22 B) ⧸ (m22SetAction B).ker) ≃*
      alternatingGroup (Fin 6)) :=
  ⟨m22HexadKernel_elementaryAbelian hB, m22HexadKernel_card hB,
    ⟨m22HexadQuotientAlternatingEquiv hB⟩⟩

/-- The source E16-by-A6 extension shape of every actual hexad stabilizer. -/
theorem m22Hexad_extension {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    AlternatingBySixteen (MulAction.stabilizer M22 B) 6 :=
  ⟨(m22SetAction B).ker, inferInstance, m22Hexad_pointwise_extension hB⟩

/-- In particular the standard hexad stabilizer has the genuine extension structure. -/
theorem m22HexadStabilizer_extension : AlternatingBySixteen m22HexadStabilizer 6 :=
  m22Hexad_extension m22Hexad123_mem

end Sporadic.Mathieu
