module
public import Theory.Representation.FirstCohomologyAutomorphism.Subkernel
public import Theory.Representation.FirstCohomologyProjective
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction.FixedKernel

/-!
# C.1.13(c): the alternating-five module-centralizer split

For a two-subgroup P normalized by the A₅ block K, the assumed core
commutators imply mutual normalization. The short-group fixed-point lemma
makes P fix U(K), and the central two-kernel lifting theorem puts each
actor's displacement in U(K). Its displacement on O₂(K) is then central
in K and belongs to U(K), hence is trivial by the proved fixed-kernel
vanishing. The cocycle descends to the actual A₅ quotient. Projectivity of
the natural A₅ module makes it principal, yielding P=U(K) C_P(K).

The possible central factor in O₂(K)/U(K) is retained throughout; neither
a moving conjugator nor O₂(K)=U(K) is assumed. The last theorem discharges
the P hypotheses for the actual two-core of a normalizing overgroup.
Source: Aschbacher–Smith C.1.13(c), printed pp.124–125, applied in C.5.4(3),
printed p.155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L]

theorem IsAlternatingBlock.automorphism_inner_of_core_displacement
    (h : IsAlternatingBlock L 5) (α : MulAut L)
    (hd : ∀ x, α x * x⁻¹ ∈ pCore 2 L)
    (hfix : ∀ u ∈ blockU L, α u = u) :
    ∃ u : blockU L, ∀ x, α x = (u : L)⁻¹ * x * u := by
  let := h.2.1.elementary
  have hdU (x : L) : α x * x⁻¹ ∈ blockU L := by
    have he := DFunLike.congr_fun (h.2.1.quotient_blockU_aut_eq_one α hd)
      (QuotientGroup.mk' (blockU L) x)
    rw [quotientAut_apply_mk] at he
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp he
  have hz : blockU L ⊓ center L = ⊥ := by
    rw [←blockFixed_map,h.blockFixed_eq_bot,Subgroup.map_bot]
  have hcore := Representation.OneCohomology.automorphism_fixes_centralizing_layer
    (blockU L) (pCore 2 L) h.2.1.core_centralizes_blockU le_rfl hz α hdU hfix
  obtain ⟨r,⟨m⟩,hr⟩ := h.2.2
  let f := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,QuotientGroup.ker_mk']
  have hq : Function.Bijective (QuotientGroup.mk' (blockFixed L)) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',h.blockFixed_eq_bot]),
      QuotientGroup.mk'_surjective _⟩
  let e := (MulEquiv.ofBijective (QuotientGroup.mk' (blockFixed L)) hq).trans m.moduleIso
  let ρ := BinaryPermutation.alternatingNaturalRepresentation (Fin 5)
  have he0 (g : L) (u : blockU L) : e (blockConjugate L g u) =
      Multiplicative.ofAdd (ρ (f g) (e u).toAdd) := by
    apply Multiplicative.toAdd.injective
    change (m.moduleIso (QuotientGroup.mk' _ (blockConjugate L g u))).toAdd = _
    rw [m.intertwining]
    exact hr (f g) (e u)
  have he (g : L) (v : BinaryPermutation.natural (Fin 5)) :
      (e.symm (Multiplicative.ofAdd (ρ (f g) v)) : L) =
        g * (e.symm (Multiplicative.ofAdd v) : L) * g⁻¹ := by
    have he' : e.symm (Multiplicative.ofAdd (ρ (f g) v)) =
        blockConjugate L g (e.symm (Multiplicative.ofAdd v)) := by
      apply e.injective
      rw [e.apply_symm_apply,he0,e.apply_symm_apply]
      rfl
    exact congrArg Subtype.val he'
  let : Module.Projective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5))) ρ.asModule :=
    BinaryPermutation.alternatingFive_natural_projective
  let : Subsingleton (Representation.OneCohomology.H1 ρ) :=
    Representation.OneCohomology.subsingleton_H1_of_projective ρ
  exact Representation.OneCohomology.automorphism_inner_of_H1_zero_of_subkernel
    (blockU L) f hf e ρ he α hdU (by simpa only [hk] using hcore)

variable {G : Type*} [Group G] [Finite G]

theorem IsAlternatingBlock.two_subgroup_eq_module_sup_centralizer
    {K P : Subgroup G} (hK : IsAlternatingBlock K 5)
    (hP : IsPGroup 2 P) (hKP : K ≤ normalizer (P : Set G))
    (hUP : (blockU K).map K.subtype ≤ P)
    (hc : ⁅K,P⁆ ≤ K.pCoreIn 2) :
    P = (blockU K).map K.subtype ⊔ (P ⊓ centralizer (K : Set G)) := by
  have hPK : P ≤ normalizer (K : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr
      ((commutator_comm P K).le.trans (hc.trans (pCoreIn_le 2 K)))
  have hPU := hK.2.1.normalizing_twoGroup_centralizes_blockU hP hKP hPK
  apply le_antisymm
  · intro p hp
    let α := K.normalizerMonoidHom ⟨p,hPK hp⟩
    have hd (x : K) : α x * x⁻¹ ∈ pCore 2 K := by
      have hx := hc ((commutator_comm P K).le (commutator_mem_commutator hp x.property))
      obtain ⟨z,hz,he⟩ := hx
      exact (Subtype.ext he : z = α x * x⁻¹) ▸ hz
    have hf (u : K) (hu : u ∈ blockU K) : α u = u := by
      apply Subtype.ext
      change p * (u : G) * p⁻¹ = (u : G)
      rw [←hPU hp u (mem_map_of_mem K.subtype hu),mul_inv_cancel_right]
    obtain ⟨u,hu⟩ := hK.automorphism_inner_of_core_displacement α hd hf
    have huG : ((u : K) : G) ∈ (blockU K).map K.subtype := mem_map_of_mem K.subtype u.property
    have hcG : ((u : K) : G) * p ∈ centralizer (K : Set G) := by
      intro k hk
      have he := congrArg (fun z : K => (z : G)) (hu ⟨k,hk⟩)
      change p*k*p⁻¹ = ((u : K) : G)⁻¹*k*u at he
      calc
        k * (((u : K) : G)*p) = u * (((u : K) : G)⁻¹*k*u) * p := by group
        _ = u * (p*k*p⁻¹) * p := by rw [←he]
        _ = (((u : K) : G)*p)*k := by group
    have hm := mul_mem_sup ((blockU K).map K.subtype |>.inv_mem huG)
      (show ((u : K) : G)*p ∈ P ⊓ centralizer (K : Set G) from
        ⟨P.mul_mem (hUP huG) hp,hcG⟩)
    simpa only [inv_mul_cancel_left] using hm
  · exact sup_le hUP inf_le_left

end CFSG.Quasithin.ChapterC

namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

theorem IsAlternatingBlock.normalizer_twoCore_eq_module_sup_centralizer
    {K H : Subgroup G} (hK : IsAlternatingBlock K 5)
    (hKH : K ≤ H) (hH : H ≤ normalizer (K : Set G)) :
    H.pCoreIn 2 = (blockU K).map K.subtype ⊔
      (H.pCoreIn 2 ⊓ centralizer (K : Set G)) := by
  let Q := H.pCoreIn 2
  have hQN : Q ≤ normalizer (K : Set G) := (pCoreIn_le 2 H).trans hH
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hKQ := hKH.trans hHQ
  have hU : (blockU K).map K.subtype ≤ Q := by
    apply le_pCoreIn_of_normalizes
      ((pCore_isPGroup.to_le blockU_le_core).map K.subtype)
      ((map_subtype_le _).trans hKH)
    exact hH.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hc : ⁅K,Q⁆ ≤ K.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 H).to_le
        (le_normalizer_iff_commutator_le_right.mp hKQ))
      (le_normalizer_iff_commutator_le_left.mp hQN)
      (normalizer_commutator_ge_left K Q)
  exact hK.two_subgroup_eq_module_sup_centralizer (isPGroup_pCoreIn 2 H) hKQ hU hc

end CFSG.Quasithin.ChapterC
