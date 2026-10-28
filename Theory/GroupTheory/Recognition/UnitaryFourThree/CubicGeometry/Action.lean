module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.OriginalKernel
public import Theory.GroupTheory.NormalizerAction
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Faithful action on the original elementary kernel

Since C_G(X)=V⟨z⟩ and z moves V, the abelian kernel V is self-centralizing.
The literal normalizer action has kernel V. Its elementary ternary vector
space gives an actual matrix homomorphism with that same kernel and the
GL4(3) order divisor for the normalizer quotient.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed pp246–247.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_kernel_centralizer (P:Sylow 3 (centralizer z)) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    Subgroup.centralizer (V:Set G)=V := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let V:=CubicNormalizer.oddKernel X
  let C:=Subgroup.centralizer (V:Set G)
  let L:=Subgroup.centralizer (X:Set G)
  have hX:=h.cubic_sylow_image_card P
  have hXH:X≤centralizer z:=map_subtype_le _
  have hXV:X≤V:=CubicNormalizer.le_oddKernel X hX (h.toCentralizerHypothesis.cubic_centralizer X hX hXH)
  obtain ⟨hV,hVc⟩:=h.original_cubic_kernel_eighty_one P
  change Nat.card V=81 at hVc
  let : IsMulCommutative V:=hV.toIsMulCommutative
  have hVC:V≤C:=V.le_centralizer
  have hCL:C≤L:=centralizer_le hXV
  have hzL:z∈L:=fun x hx=>mem_centralizer_singleton_iff.mp (hXH hx)
  have hZV:zpowers z≤normalizer (V:Set G):=zpowers_le.mpr
    (CubicNormalizer.normalizer_normalizes_oddKernel X (centralizer_le_normalizer _ hzL))
  have hLc:Nat.card L=162:=by
    rw [show L=V⊔zpowers z from h.toCentralizerHypothesis.cubic_centralizer_split X hX hXH,
      card_sup_eq_mul_of_normalizes_of_disjoint V (zpowers z) hZV
      (disjoint_of_coprime_natCard (by rw [hVc,Nat.card_zpowers,h.involution];decide)),hVc,
      Nat.card_zpowers,h.involution]
  have hidx:V.relIndex L=2:=by
    have hh:=relIndex_mul_relIndex (⊥:Subgroup G) V L bot_le (hVC.trans hCL)
    simp only [relIndex_bot_left,hVc,hLc] at hh
    omega
  have hh:=relIndex_mul_relIndex V C L hVC hCL
  rw [hidx] at hh
  have hc:C=V ∨ C=L:=by
    have hd:V.relIndex C∣2:=⟨C.relIndex L,hh.symm⟩
    have hcases:V.relIndex C=1 ∨ C.relIndex L=1:=by
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi|hi
      · exact Or.inl hi
      · rw [hi] at hh
        exact Or.inr (by omega)
    rcases hcases with hc|hc
    · exact Or.inl (le_antisymm (relIndex_eq_one.mp hc) hVC)
    · exact Or.inr (le_antisymm hCL (relIndex_eq_one.mp hc))
  rcases hc with hc|hc
  · exact hc
  have hzC:z∈C:=hc ▸ hzL
  have hVX:V≤X:=by
    apply (le_inf le_rfl ?_).trans (h.toCentralizerHypothesis.cubic_oddKernel_fixed X hX hXH).le
    intro v hv
    exact mem_centralizer_singleton_iff.mpr (hzC v hv)
  have hn:=card_le_of_le hVX
  rw [hVc,hX] at hn
  omega
include h in
theorem cubic_kernel_automorphism_kernel (P:Sylow 3 (centralizer z)) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    V.normalizerMonoidHom.ker=V.subgroupOf (normalizer (V:Set G)) := by
  dsimp only
  rw [normalizerMonoidHom_ker,h.cubic_kernel_centralizer P]

include h in
theorem cubic_kernel_faithful_linear_action (P:Sylow 3 (centralizer z)) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    ∃ρ:normalizer (V:Set G)→*Matrix.GeneralLinearGroup (Fin 4) (ZMod 3),
      ρ.ker=V.subgroupOf (normalizer (V:Set G)) := by
  let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
  obtain ⟨hV,hc⟩:=h.original_cubic_kernel_eighty_one P
  let :IsElementaryAbelian 3 V:=hV
  obtain ⟨f,hf⟩:=IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p:=3) (n:=4) V hc.le
  refine ⟨f.comp V.normalizerMonoidHom,?_⟩
  rw [MonoidHom.ker_comp_of_injective V.normalizerMonoidHom f hf]
  exact h.cubic_kernel_automorphism_kernel P

include h in
theorem cubic_kernel_normalizer_index_dvd (P:Sylow 3 (centralizer z)) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    V.relIndex (normalizer (V:Set G)) ∣ 24261120 := by
  obtain ⟨ρ,hρ⟩:=h.cubic_kernel_faithful_linear_action P
  have hc:Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 3))=24261120:=by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ,ZMod.card]
  have hh:=ρ.range.card_subgroup_dvd_card
  rwa [←index_ker,hρ,hc] at hh
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
