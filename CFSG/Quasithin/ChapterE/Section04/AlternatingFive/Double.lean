module
public import CFSG.Quasithin.ChapterE.Section04.ThreeTensor
public import CFSG.Quasithin.ChapterE.Section04.AlternatingFive
public import CFSG.Quasithin.ChapterE.Section03.Parameters.SectionNormalizer
public import Theory.Representation.BinaryPermutation.FiveDoubleNormalizer
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# The full local parameter for two copies of the binary A₅ module

The actual full normalizer embeds in S₅ × S₃ acting on the tensor of
the five- and three-point augmentation cores. The tensor fixed-space
bound is at most one. Equivariant section coordinates transport this
bound to the literal local automizer, including all outer actors.
Source: Aschbacher–Smith, 12.3.2 and 12.4.1, printed pp.807,812.
-/
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE
abbrev fiveDoubleRepresentation :=
  Representation.prod ((naturalRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype)
    ((naturalRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype)

private theorem five_double_faithful : Function.Injective fiveDoubleRepresentation.asGroupHom := by
  intro a b he
  apply Subtype.ext
  apply naturalRepresentation_injective (Fin 5) (by decide)
  apply LinearMap.ext
  intro v
  exact congrArg Prod.fst (LinearMap.congr_fun (congrArg Units.val he) (v,0))

private theorem double_core_equivariant (a : alternatingGroup (Fin 5))
    (v : natural (Fin 5) × natural (Fin 5)) :
    let c := coreEquivNatural (Fin 5) (by decide)
    let E := c.symm.prodCongr c.symm
    E (fiveDoubleRepresentation a v) =
      (alternatingCoreRepresentation (Fin 5) a (E v).1,
       alternatingCoreRepresentation (Fin 5) a (E v).2) := by
  intro c E
  apply Prod.ext
  · apply c.injective
    change c (c.symm (naturalRepresentation (Fin 5) a.val v.1)) =
      c (alternatingCoreRepresentation (Fin 5) a (c.symm v.1))
    rw [c.apply_symm_apply]
    have hh : c (alternatingCoreRepresentation (Fin 5) a (c.symm v.1)) =
        naturalRepresentation (Fin 5) a.val (c (c.symm v.1)) :=
      coreEquivNatural_equivariant (Fin 5) (by decide) a.val (c.symm v.1)
    rw [c.apply_symm_apply] at hh
    exact hh.symm
  · apply c.injective
    change c (c.symm (naturalRepresentation (Fin 5) a.val v.2)) =
      c (alternatingCoreRepresentation (Fin 5) a (c.symm v.2))
    rw [c.apply_symm_apply]
    have hh : c (alternatingCoreRepresentation (Fin 5) a (c.symm v.2)) =
        naturalRepresentation (Fin 5) a.val (c (c.symm v.2)) :=
      coreEquivNatural_equivariant (Fin 5) (by decide) a.val (c.symm v.2)
    rw [c.apply_symm_apply] at hh
    exact hh.symm

theorem moduleA_fiveDouble_normalizer_le_one :
    moduleA (normalizerRepresentation fiveDoubleRepresentation) ≤ 1 := by
  let σ := fiveDoubleRepresentation
  let J := actionImage σ
  let K := J.subgroupOf (linearNormalizer σ)
  let τ := normalizerRepresentation σ
  let e₀ : alternatingGroup (Fin 5) ≃* J := MonoidHom.ofInjective five_double_faithful
  let e : K ≃* alternatingGroup (Fin 5) :=
    (subgroupOfEquivOfLe J.le_normalizer).trans e₀.symm
  let : K.Normal := J.normal_in_normalizer
  have hf : Function.Injective τ := by
    intro a b he
    exact Subtype.ext (Units.ext he)
  let c := coreEquivNatural (Fin 5) (by decide)
  let E := c.symm.prodCongr c.symm
  have he (k : K) (v : natural (Fin 5) × natural (Fin 5)) : E (τ k.val v) =
      (alternatingCoreRepresentation (Fin 5) (e k) (E v).1,
       alternatingCoreRepresentation (Fin 5) (e k) (E v).2) := by
    have hh := e₀.apply_symm_apply ((subgroupOfEquivOfLe J.le_normalizer) k)
    have ht : τ k.val v = σ (e k) v :=
      (congrArg (fun u : J => u.val.val v) hh).symm
    exact (congrArg E ht).trans (double_core_equivariant (e k) v)
  obtain ⟨j,t,hj,hjt,_⟩ := FiveTensorNormalizer.exists_tensor_embedding_of_double τ hf K e E he
  have hc : moduleA (coreRepresentation (Fin 5)) ≤ 1 := by
    rw [moduleA_eq_of_equivariant_equiv (coreRepresentation (Fin 5))
      (naturalRepresentation (Fin 5)) (MulEquiv.refl _) c
      (coreEquivNatural_equivariant (Fin 5) (by decide))]
    exact moduleA_fiveNatural_le_one
  let : Nontrivial (core (Fin 5)) := Module.nontrivial_of_finrank_pos
    (by rw [finrank_core]; decide : 0 < Module.finrank (ZMod 2) (core (Fin 5)))
  exact (moduleA_le_of_equivariant_injective τ _ j hj t hjt).trans
    (moduleA_threeTensor_le_one _ hc)
end CFSG.Quasithin.ChapterE

namespace CFSG.Quasithin.ChapterE
/-- The full local automizer of an actual doubled A₅ section has parameter at most one. -/
theorem moduleA_local_double_section_le_one
    {G : Type*} [Group G]
    (H W M : Subgroup G) [IsElementaryAbelian 2 W]
    (q : H →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (c : Representation.BinaryConjugationSection H W ⊥
      (fiveDoubleRepresentation.comp q))
    (hHM : H ≤ M)
    (hNH : M ⊓ normalizer (W : Set G) ≤ normalizer (H : Set G)) :
    moduleA ((automizerRepresentation W).comp (inducedAutomizer W M).subtype) ≤ 1 := by
  let N := M ⊓ normalizer (W : Set G)
  have hNB : N ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [normalizer_eq_top]
    exact le_top
  have hk : commutatorPreimage N W ⊥ ≤ centralizer (W : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (bot_unique (commutator_commutatorPreimage_le N W ⊥ hNB))
  obtain ⟨τ,f,hf,hfτ,hact⟩ := exists_local_section_normalizer H W ⊥ M
    fiveDoubleRepresentation
    q hq c hHM hNH hNB hk
  have hci : Function.Injective c.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [c.kernel_eq,bot_subgroupOf]
  let E : Additive W ≃ₗ[ZMod 2] (natural (Fin 5) × natural (Fin 5)) :=
    LinearEquiv.ofBijective (c.coordinates.toAdditiveLeft.toZModLinearMap 2) ⟨hci,c.onto⟩
  apply (moduleA_le_of_equivariant_injective
    ((automizerRepresentation W).comp (inducedAutomizer W M).subtype)
    _ f hf E ?_).trans moduleA_fiveDouble_normalizer_le_one
  intro a w
  obtain ⟨n,rfl⟩ := localNormalizerAction_surjective W M a
  rw [hfτ]
  exact (hact n w.toMul).symm
end CFSG.Quasithin.ChapterE
