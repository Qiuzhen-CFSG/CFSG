module
public import Theory.GroupTheory.PCoreCoverEquiv
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicCentralizer
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The A5 quotient of the original core supplement

If Y = K O₂(Y) and K/O₂(K) is A₅, inclusion identifies the two core
quotients. Every two-subgroup of Y therefore has commutator in O₂(Y).
A subgroup of order three embeds in the quotient and has centralizer of
order three there. Hence a two-subgroup commuting with that cubic modulo
the core lies entirely in the core.

The final theorem retains the original ambient subgroups and core map.
It supplies the finite quotient step for the original tensor pair, where
S = (T ∩ K)O₂(HA). No elementary or normality premise on V is needed.
Source: Aschbacher–Smith 9.3.2–3, printed p.733, combined manuscript of
1 March 2004; the elementary A₅ cubic-centralizer calculation is imported.
-/

public section
open Subgroup
open scoped IsMulCommutative Pointwise commutatorElement

namespace CFSG.Quasithin.Chapter10.SourceA5TensorExclusion

private theorem a5_two_subgroup_abelian
    (U : Subgroup (alternatingGroup (Fin 5))) (hU : IsPGroup 2 U) :
    IsMulCommutative U := by
  obtain ⟨P,hUP⟩ := hU.exists_le_sylow
  have hc : Nat.card P = 2^2 := by
    rw [P.card_eq_multiplicity,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    decide +kernel
  let : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq hc
  apply isMulCommutative_iff.mpr
  intro x y
  exact Subtype.ext (congrArg (fun z : P => (z : alternatingGroup (Fin 5))) (mul_comm
    (⟨x,hUP x.property⟩ : P) (⟨y,hUP y.property⟩ : P)))

private theorem a5_map_two_subgroup
    {E : Type*} [Group E] [Finite E]
    (f : E →* alternatingGroup (Fin 5)) (hf : IsPGroup 2 f.ker)
    (S B : Subgroup E) (hS : IsPGroup 2 S) (hB : Nat.card B = 3) :
    ⁅S,S⁆ ≤ f.ker ∧ ∀ V : Subgroup E, V ≤ S → ⁅B,V⁆ ≤ f.ker → V ≤ f.ker := by
  have hBP : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by simpa using hB)
  have hd := hBP.disjoint_of_coprime hf (by decide : Nat.Coprime 3 2)
  let g := f.comp B.subtype
  have hg : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff g).mp
    apply bot_unique
    intro x hx
    exact Subtype.ext (Subgroup.disjoint_def.mp hd x.property
      (show (x : E) ∈ f.ker from hx))
  have hm : Function.Injective (f.subgroupMap B) := by
    intro x y he
    exact hg (congrArg Subtype.val he)
  have hBmap : Nat.card (B.map f) = 3 := by
    rw [←Nat.card_congr (MulEquiv.ofBijective (f.subgroupMap B)
      ⟨hm,MonoidHom.subgroupMap_surjective f B⟩).toEquiv]
    exact hB
  constructor
  · apply (map_eq_bot_iff ⁅S,S⁆).mp
    rw [map_commutator]
    exact commutator_self_eq_bot_iff.mpr (a5_two_subgroup_abelian (S.map f) (hS.map f))
  · intro V hVS hBV
    have he : ⁅B.map f,V.map f⁆ = ⊥ := by
      rw [←map_commutator]
      exact (map_eq_bot_iff ⁅B,V⁆).mpr hBV
    have hc : V.map f ≤ centralizer (B.map f : Set (alternatingGroup (Fin 5))) := by
      rw [commutator_comm] at he
      exact commutator_eq_bot_iff_le_centralizer.mp he
    have hCcard := alternatingGroup.FiveLocalGeometry.cubic_centralizer_card
      (MulEquiv.refl (alternatingGroup (Fin 5))) (B.map f) hBmap
    have hC : IsPGroup 3 (centralizer (B.map f : Set (alternatingGroup (Fin 5)))) :=
      IsPGroup.of_card (n := 1) (by simpa using hCcard)
    have hdis := ((hS.to_le hVS).map f).disjoint_of_coprime hC
      (by decide : Nat.Coprime 2 3)
    apply (map_eq_bot_iff V).mp
    apply bot_unique
    intro v hv
    exact Subgroup.disjoint_def.mp hdis hv (hc hv)

variable {G : Type*} [Group G] [Finite G]

/-- The literal A₅ core quotient controls two-subgroup commutators and cubic fixed images. -/
theorem a5_core_quotient_two_subgroup
    (K Y S B : Subgroup G)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hcover : Y = K ⊔ Y.pCoreIn 2)
    (hS : IsPGroup 2 S) (hSY : S ≤ Y) (hBK : B ≤ K) (hB3 : Nat.card B = 3) :
    ⁅S,S⁆ ≤ Y.pCoreIn 2 ∧
      ∀ V : Subgroup G, V ≤ S → ⁅B,V⁆ ≤ Y.pCoreIn 2 → V ≤ Y.pCoreIn 2 := by
  have hKY : K ≤ Y := hcover ▸ le_sup_left
  have hBY : B ≤ Y := hBK.trans hKY
  have hn : Y ≤ normalizer (Y.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 Y).le_normalizer_map Y.subtype
  have hp : (Y : Set G) ⊆ (K : Set G) * (Y.pCoreIn 2 : Set G) := by
    intro y hy
    rw [←coe_mul_of_left_le_normalizer_right K (Y.pCoreIn 2) (hKY.trans hn)]
    exact hcover ▸ hy
  obtain ⟨ee,_hee⟩ := exists_pCoreQuotientEquiv_of_cover hKY hp
  let eY := ee.symm.trans eK
  let f := eY.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Y))
  have hf : f.ker = pCore 2 Y := by
    ext y
    change eY (QuotientGroup.mk' (pCore 2 Y) y) = 1 ↔ y ∈ pCore 2 Y
    rw [map_eq_one_iff eY eY.injective]
    exact QuotientGroup.eq_one_iff y
  have hBcard : Nat.card (B.subgroupOf Y) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv,hB3]
  obtain ⟨hc,hv⟩ := a5_map_two_subgroup f (hf ▸ pCore_isPGroup)
    (S.subgroupOf Y) (B.subgroupOf Y) hS.comap_subtype hBcard
  rw [hf] at hc hv
  constructor
  · have hh := map_mono (f := Y.subtype) hc
    rwa [map_commutator,map_subgroupOf_eq_of_le hSY] at hh
  · intro V hVS hBV
    have hVY : V ≤ Y := hVS.trans hSY
    have hBV' : ⁅B.subgroupOf Y,V.subgroupOf Y⁆ ≤ pCore 2 Y := by
      apply commutator_le.mpr
      intro b hb v hv
      apply (mem_map_iff_mem (f := Y.subtype) Y.subtype_injective).mp
      exact hBV (commutator_mem_commutator hb hv)
    have hh := map_mono (f := Y.subtype) (hv (V.subgroupOf Y) (comap_mono hVS) hBV')
    rwa [map_subgroupOf_eq_of_le hVY] at hh

end CFSG.Quasithin.Chapter10.SourceA5TensorExclusion
