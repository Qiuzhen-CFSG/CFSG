module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.Basic
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.FourNormalizerCores
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore

/-!
# Identification of the genuine local core

Transport E through the given A₆ isomorphism. Compatibility of the action
identifies N_H(E) with the preimage of its full automorphism normalizer,
and detects centralization of E. The action kernel is the actual two-group
S_C. Prime-core lifting therefore transfers the checked model identity
O₂(N_Aut(A₆)(E)) = C_S̄(E) to O₂(N_H(E)) = C_S(E).

Source: Aschbacher–Smith, proof of 2.5.24, printed p.568. No rank,
elementary-core, largest-local-pair or orbit premise enters this formula.
-/

public section

open Subgroup AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable (d : EarlierSetup κ G)

private noncomputable def modelFour (E : Subgroup G) : Subgroup A6 :=
  (E.subgroupOf d.K).map d.modelK.toMonoidHom

private theorem mem_modelFour (E : Subgroup G) (a : A6) :
    a ∈ modelFour d E ↔ (d.modelK.symm a : G) ∈ E := by
  change a ∈ (E.subgroupOf d.K).map d.modelK.toMonoidHom ↔ _
  rw [mem_map_equiv]
  rfl

private theorem modelFour_four (E : Subgroup G) (hE : E ≤ d.K) [IsKleinFour E] :
    IsKleinFour (modelFour d E) := by
  let e := (subgroupOfEquivOfLe hE).symm.trans (d.modelK.subgroupMap (E.subgroupOf d.K))
  exact ⟨(Nat.card_congr e.toEquiv).symm.trans IsKleinFour.card_four,
    (Monoid.exponent_eq_of_mulEquiv e).symm.trans IsKleinFour.exponent_two⟩

private theorem modelFour_inner_le (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) :
    (modelFour d E).map (MulAut.conj : A6 →* AutA6) ≤ d.imageSylow := by
  rintro _ ⟨a, ha, rfl⟩
  have haE := (mem_modelFour d E a).mp ha
  rw [d.imageSylow_eq_range]
  refine ⟨⟨d.modelK.symm a, (hE haE).1⟩, ?_⟩
  change d.action ⟨d.modelK.symm a, _⟩ = _
  rw [d.action_on_K, d.modelK.apply_symm_apply]

private theorem action_stabilizes_iff (E : Subgroup G) (hE : E ≤ d.K) (h : d.H) :
    (modelFour d E).map (d.action h).toMonoidHom = modelFour d E ↔
      (h : G) ∈ normalizer (E : Set G) := by
  constructor
  · intro he
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      have haF : d.modelK ⟨a, hE ha⟩ ∈ modelFour d E := ⟨⟨a, hE ha⟩, ha, rfl⟩
      have hi := mem_map_of_mem (d.action h).toMonoidHom haF
      rw [he, mem_modelFour] at hi
      simp only [MulEquiv.coe_toMonoidHom] at hi
      rw [d.action_compatible h ⟨a, hE ha⟩] at hi
      exact hi
    · intro a ha
      have haF : d.modelK ⟨a, hE ha⟩ ∈ modelFour d E := ⟨⟨a, hE ha⟩, ha, rfl⟩
      rw [← he, mem_map_equiv] at haF
      have hbE := (mem_modelFour d E _).mp haF
      refine ⟨d.modelK.symm ((d.action h).symm (d.modelK ⟨a, hE ha⟩)), hbE, ?_⟩
      change (h : G) * _ * (h : G)⁻¹ = a
      rw [← d.action_compatible]
      simp only [d.modelK.apply_symm_apply, MulEquiv.apply_symm_apply,
        d.modelK.symm_apply_apply]
  · intro hn
    ext a
    rw [mem_map_equiv, mem_modelFour, mem_modelFour]
    have hh := mem_normalizer_iff.mp hn (d.modelK.symm ((d.action h).symm a) : G)
    rw [← d.action_compatible h _] at hh
    simpa only [d.modelK.apply_symm_apply, MulEquiv.apply_symm_apply] using hh

private theorem action_normalizes_iff (E : Subgroup G) (hE : E ≤ d.K) (h : d.H) :
    d.action h ∈ normalizer ((modelFour d E).map (MulAut.conj : A6 →* AutA6) : Set AutA6) ↔
      (h : G) ∈ normalizer (E : Set G) := by
  rw [FourNormalizers.mem_inner_normalizer_iff]
  exact action_stabilizes_iff d E hE h

private theorem action_centralizes_iff (E : Subgroup G) (hE : E ≤ d.K) (h : d.H) :
    d.action h ∈ centralizer ((modelFour d E).map (MulAut.conj : A6 →* AutA6) : Set AutA6) ↔
      (h : G) ∈ centralizer (E : Set G) := by
  have hcomm (k : d.K) : Commute (d.action h) (MulAut.conj (d.modelK k)) ↔
      Commute (h : G) (k : G) := by
    change d.action h * MulAut.conj (d.modelK k) = _ ↔ _
    rw [← mul_inv_eq_iff_eq_mul, aut_conj_inner, inner_injective.eq_iff]
    constructor
    · intro he
      have hv := d.action_compatible h k
      rw [he, d.modelK.symm_apply_apply] at hv
      exact mul_inv_eq_iff_eq_mul.mp hv.symm
    · intro hc
      apply d.modelK.symm.injective
      apply Subtype.ext
      rw [d.action_compatible, d.modelK.symm_apply_apply]
      exact mul_inv_eq_iff_eq_mul.mpr hc.eq
  constructor
  · intro hc a ha
    have haF : d.modelK ⟨a, hE ha⟩ ∈ modelFour d E := ⟨⟨a, hE ha⟩, ha, rfl⟩
    have hh := hc _ (mem_map_of_mem (MulAut.conj : A6 →* AutA6) haF)
    exact ((hcomm ⟨a, hE ha⟩).mp hh.symm).eq.symm
  · intro hc a ha
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨k, hk, rfl⟩ := hb
    exact ((hcomm k).mpr (hc k hk).symm).eq.symm

/-- The exact remaining finite-model identity, without any chapter hypotheses. -/
private def ModelCoreFormula : Prop :=
  ∀ (P : Sylow 2 AutA6) (F : Subgroup A6), IsKleinFour F →
    F.map (MulAut.conj : A6 →* AutA6) ≤ P →
    (normalizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6)).pCoreIn 2 =
      (P : Subgroup AutA6) ⊓ centralizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6)

private theorem localCore_eq_of_model (hmodel : ModelCoreFormula)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) [IsKleinFour E] :
    localCore d E = d.S ⊓ centralizer (E : Set G) := by
  let F := modelFour d E
  let L : Subgroup d.H := (normalizer (E : Set G)).subgroupOf d.H
  let C : Subgroup d.H := (d.S ⊓ centralizer (E : Set G)).subgroupOf d.H
  have hSC : d.SC ≤ centralizer (E : Set G) :=
    (d.centralizer_K ▸ inf_le_right).trans (centralizer_le (hE.trans inf_le_right))
  have hker : IsPGroup 2 d.action.ker := by
    rw [d.action_kernel]
    have hp : IsPGroup 2 d.SC := by rw [d.core]; exact isPGroup_pCoreIn 2 d.H
    exact hp.comap_subtype
  have hkerL : d.action.ker ≤ L := by
    intro h hh
    rw [d.action_kernel] at hh
    exact centralizer_le_normalizer (E : Set G) (hSC hh)
  have hkerCore : d.action.ker ≤ L.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes hker hkerL
    rw [normalizer_eq_top_iff.mpr (inferInstance : d.action.ker.Normal)]
    exact le_top
  have hkerC : d.action.ker ≤ C := by
    intro h hh
    rw [d.action_kernel] at hh
    exact ⟨d.sc_le_s hh, hSC hh⟩
  have hL : L.map d.action = normalizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6) := by
    ext a
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact (action_normalizes_iff d E (hE.trans inf_le_right) h).mpr hh
    · intro ha
      obtain ⟨h, rfl⟩ := d.action_surjective a
      exact ⟨h, (action_normalizes_iff d E (hE.trans inf_le_right) h).mp ha, rfl⟩
  have hS : (d.S.subgroupOf d.H).map d.action = d.imageSylow := by
    rw [d.imageSylow_eq_range]
    ext a
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s, d.s_le_h s.property⟩, s.property, rfl⟩
  have hpreS : (d.imageSylow : Subgroup AutA6).comap d.action = d.S.subgroupOf d.H := by
    rw [← hS, comap_map_eq]
    apply sup_eq_left.mpr
    rw [d.action_kernel]
    exact fun _ h => d.sc_le_s h
  have hpreC : ((d.imageSylow : Subgroup AutA6) ⊓
      centralizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6)).comap d.action = C := by
    rw [comap_inf, hpreS]
    ext h
    exact and_congr_right (fun _ => action_centralizes_iff d E (hE.trans inf_le_right) h)
  have hC : C.map d.action = (d.imageSylow : Subgroup AutA6) ⊓
      centralizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6) := by
    rw [← hpreC, map_comap_eq_self]
    rw [MonoidHom.range_eq_top.mpr d.action_surjective]
    exact le_top
  have he : L.pCoreIn 2 = C := by
    apply map_injective_of_ker_le d.action hkerCore hkerC
    rw [map_pCoreIn_of_ker_isPGroup d.action hker, hL, hC]
    exact hmodel d.imageSylow F (modelFour_four d E (hE.trans inf_le_right))
      (modelFour_inner_le d E hE)
  have hm := congrArg (Subgroup.map d.H.subtype) he
  rw [map_pCoreIn_of_injective 2 L d.H.subtype d.H.subtype_injective] at hm
  have hLm : L.map d.H.subtype = d.H ⊓ normalizer (E : Set G) := by
    change ((normalizer (E : Set G)).comap d.H.subtype).map d.H.subtype = _
    rw [map_comap_eq, d.H.range_subtype, inf_comm]
  have hCm : C.map d.H.subtype = d.S ⊓ centralizer (E : Set G) :=
    map_subgroupOf_eq_of_le (inf_le_left.trans d.s_le_h)
  rw [hLm, hCm] at hm
  exact hm

/-- The actual local core, with no elementary-core or rank assumptions. -/
theorem localCore_eq (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) [IsKleinFour E] :
    localCore d E = d.S ⊓ centralizer (E : Set G) := by
  apply localCore_eq_of_model d ?_ E hE
  intro P F hF hFP
  let := hF
  exact FourNormalizerCores.core_eq_sylow_centralizer P F hFP

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.RankTwo
