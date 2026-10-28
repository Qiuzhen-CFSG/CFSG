module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.SmallAutomizer
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The E.2.17 small automizer in the original ambient group

For a genuine marked two-conjugate subgroup I and an elementary chosen V,
the small automizer calculation uses the actual quotient U/C_U(V). Its
four-group actor exhausts the quotient. Thus U=O₂(I)C_U(V), with the two-core
mapped through the literal inclusion I→G; this core has order thirty-two
and its centralizer of V is exactly its intersection with V.

The application retains the explicit source pair and its order-two quotient
premise. It supplies the product and centralizer calculations used after
E.2.17 in 15.1.11. It does not assert that I is the global conjugate span or
that its two-core is normalized by U; that is the remaining extension step.

Source: Aschbacher–Smith, E.2.17 and 15.1.11, printed pp.229 and 1085.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.DihedralCubic
open TwoConjugate
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
variable {I U V : Subgroup G} {S : Sylow 2 I} {N : Subgroup I} {g : I}

/-- Small automizers are exhausted by the genuine source actor. -/
theorem ambient_small_automizer [IsElementaryAbelian 2 V]
    (hVI : V ≤ I) (hn : U ≤ normalizer (V : Set G))
    (h : Hypotheses S (V.subgroupOf I) N g)
    (hSU : (S : Subgroup I).map I.subtype ≤ U)
    (hproper : V.subgroupOf I ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting I = pCore 2 I)
    (hcard : Nat.card ((V.subgroupOf I).map (QuotientGroup.mk' (J N))) = 2)
    (hV : Nat.card V = 16)
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (V : Set G)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (representation U V hn q hq hk)) :
    Nat.card D = 4 ∧ IsElementaryAbelian 2 D ∧
      Nat.card (I.pCoreIn 2) = 32 ∧
      I.pCoreIn 2 ⊓ centralizer (V : Set G) = I.pCoreIn 2 ⊓ V ∧
      U = I.pCoreIn 2 ⊔ (U ⊓ centralizer (V : Set G)) := by
  let e := subgroupOfEquivOfLe hVI
  let ρ := representation U V hn q hq hk
  let f := actorMap h hSU q
  have hρ := representation_injective U V hn q hq hk
  have ha (a : A (V.subgroupOf I) N g) (v : V.subgroupOf I) :
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : I) =
        (a : I) * v * (a : I)⁻¹ := by
    apply Subtype.ext
    change ((ρ (q (actorIn h hSU a)) (Additive.ofMul (e v))).toMul : G) =
      ((a : I) : G) * ((v : I) : G) * ((a : I) : G)⁻¹
    rw [representation_apply]
    rfl
  have hr := h.actor_rank_two_of_small_automizer hproper hfit hcard e ρ hρ f ha hD hratio
  have htop : f.range = ⊤ := eq_top_of_le_card _ (by rw [hr.2.1]; exact hD)
  have hf : Function.Surjective f := by
    intro d
    exact (show d ∈ f.range by rw [htop]; trivial)
  have hDp : IsElementaryAbelian 2 D := by
    let := h.A_elementary
    exact IsElementaryAbelian.of_surjective f hf
  have hDc : Nat.card D = 4 := by
    simpa only [htop, card_top] using hr.2.1
  have hVi : Nat.card (V.subgroupOf I) = 16 := (Nat.card_congr e.toEquiv).trans hV
  have hc := h.small_automizer_core_orders hproper hfit hcard hVi e ρ hρ f ha hD hratio
  have hP : P (V.subgroupOf I) N g = pCore 2 I := (h.odd_dihedral hcard).1
  have hPc : Nat.card (I.pCoreIn 2) = 32 := by
    change Nat.card ((pCore 2 I).map I.subtype) = 32
    rw [card_map_of_injective I.subtype_injective, ← hP]
    exact hc.2.2.2.1
  have hPU : I.pCoreIn 2 ≤ U :=
    (map_mono (pCore_isPGroup.le_sylow_of_normal S)).trans hSU
  have hPC : I.pCoreIn 2 ⊓ centralizer (V : Set G) = I.pCoreIn 2 ⊓ V := by
    apply le_antisymm
    · rintro x ⟨hxP, hxC⟩
      obtain ⟨x, hx, rfl⟩ := mem_map.mp hxP
      have hxi : x ∈ P (V.subgroupOf I) N g ⊓
          centralizer (V.subgroupOf I : Set I) := by
        refine ⟨hP.symm ▸ hx, ?_⟩
        intro v hv
        apply Subtype.ext
        exact hxC v hv
      rw [hc.2.2.2.2] at hxi
      exact ⟨mem_map_of_mem I.subtype hx, hxi.2⟩
    · exact inf_le_inf_left _ V.le_centralizer
  refine ⟨hDc, hDp, hPc, hPC, le_antisymm ?_ (sup_le hPU inf_le_left)⟩
  intro u hu
  obtain ⟨a, ha⟩ := hf (q ⟨u,hu⟩)
  let b := actorIn h hSU a
  have hbP : (b : G) ∈ I.pCoreIn 2 := by
    exact mem_map_of_mem I.subtype (h.P_le_twoCore (mem_sup_right a.property))
  have hrK : b⁻¹ * ⟨u,hu⟩ ∈ q.ker := by
    change q (b⁻¹ * ⟨u,hu⟩) = 1
    rw [map_mul, map_inv]
    change (f a)⁻¹ * q ⟨u,hu⟩ = 1
    rw [ha, inv_mul_cancel]
  rw [hk] at hrK
  have hrU : (b : G)⁻¹ * u ∈ U ⊓ centralizer (V : Set G) :=
    ⟨U.mul_mem (U.inv_mem b.property) hu, hrK⟩
  have hmem := (I.pCoreIn 2 ⊔ (U ⊓ centralizer (V : Set G))).mul_mem
    (mem_sup_left hbP) (mem_sup_right hrU)
  simpa only [mul_inv_cancel_left] using hmem

end CFSG.Quasithin.ChapterE.DihedralCubic
