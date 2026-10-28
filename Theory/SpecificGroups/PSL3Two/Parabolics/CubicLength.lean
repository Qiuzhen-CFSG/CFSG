module
public import Theory.SpecificGroups.PSL3Two.Parabolics.OddIndex
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Displacement
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients
public import Theory.GroupTheory.PCoreImage

/-!
# Cubic movement on a covered binary parabolic core

A proper index-seven Sylow overgroup in SL₃(2) is an actual S₄ parabolic.
A cubic cannot centralize its four-core, since that core is self-centralizing.
Coprime fixed-point lifting therefore gives a positive cubic contribution on
O₂(P) modulo the full two-group kernel of any cover. The actor lies in P;
no assertion is made for arbitrary cubics of the covering group.

Source application: Aschbacher–Smith 13.4.7(4), printed p.903, the contribution
on the second parabolic core above the original join's core.
-/

public noncomputable section
open Subgroup
namespace NoncentralChiefRefinement.CubicComparison
variable {G : Type*} [Group G] [Finite G]

/-- A cubic moves the core above the actual kernel of a symmetric-four quotient. -/
theorem symmetricFour_core_section_pos
    (f : G →* Equiv.Perm (Fin 4)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (E : Subgroup G) (hE : Nat.card E = 3) :
    1 ≤ sectionCubicLength E f.ker (pCore 2 G) := by
  have hkQ : f.ker ≤ pCore 2 G := le_sSup ⟨inferInstance,hk⟩
  have hmap : (pCore 2 G).map f = pCore 2 (Equiv.Perm (Fin 4)) := by
    rw [← f.comap_pCore_of_ker_isPGroup hf hk,map_comap_eq_self]
    rw [MonoidHom.range_eq_top_of_surjective _ hf]
    exact le_top
  by_contra hn
  have hz : conjugationCubicLength E f.ker = conjugationCubicLength E (pCore 2 G) := by
    have hm := conjugationCubicLength_mono E hkQ
    unfold sectionCubicLength at hn
    omega
  have hc := commutator_le_of_length_eq E (pCore 2 G) f.ker
    (IsPGroup.of_card (n := 1) (by simpa using hE)) pCore_isPGroup hkQ
    le_normalizer_of_normal le_normalizer_of_normal hz
  have hm := map_mono (f := f) hc
  have hmk : f.ker.map f = ⊥ := (map_eq_bot_iff f.ker).mpr le_rfl
  rw [map_commutator,hmap,hmk] at hm
  have he := commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hm)
  have hle : E.map f ≤ pCore 2 (Equiv.Perm (Fin 4)) :=
    (le_centralizer_iff.mp he).trans
      (Matrix.PSL3Two.ParabolicCoreModel.core_selfCentralizing (MulEquiv.refl _))
  obtain ⟨n,hn⟩ := (pCore_isPGroup.to_le hle).exists_card_eq
  rw [GLS3.Chapter5.cubic_image_card_of_two_kernel f hk E hE] at hn
  have hd : 3 ∣ 2 ^ n := by rw [←hn]
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

end NoncentralChiefRefinement.CubicComparison

namespace Matrix.PSL3Two
open NoncentralChiefRefinement.CubicComparison
variable {G : Type*} [Group G] [Finite G]

/-- The actual parabolic core contributes above the full kernel of a linear cover. -/
theorem index_seven_core_section_pos
    (f : G →* SL) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 G) (P : Subgroup G) (hSP : (S : Subgroup G) ≤ P)
    (hi : P.index = 7) (E : Subgroup G) (hE : Nat.card E = 3) (hEP : E ≤ P) :
    1 ≤ sectionCubicLength E f.ker (P.pCoreIn 2) := by
  have hkP : f.ker ≤ P := (hk.le_sylow_of_normal S).trans hSP
  let B := P.map f
  have hBi : B.index = 7 := (P.index_map_eq hf hkP).trans hi
  have hBcard : Nat.card B = 24 := by
    have hh := B.index_mul_card
    rw [hBi,card_SL] at hh
    omega
  have hBne : B ≠ ⊤ := by intro he; simp only [he,index_top] at hBi; omega
  have hBtwo : ¬ IsPGroup 2 B := by
    intro hp
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hBcard] at hn
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow
      (hn ▸ (by decide : 3 ∣ 24)))
  obtain ⟨e,_,he⟩ := exists_sylow_line_marking equiv (S.mapSurjective hf) B
    (map_mono hSP) hBne hBtwo
  let eB : B ≃* Equiv.Perm (Fin 4) :=
    ((e.subgroupMap B).trans (MulEquiv.subgroupCongr he)).trans
      MarkedAutomorphisms.lineEquivSymmetric
  let g := eB.toMonoidHom.comp (f.subgroupMap P)
  have hg : Function.Surjective g := eB.surjective.comp (f.subgroupMap_surjective P)
  have hgker : g.ker = f.ker.subgroupOf P := by
    rw [MonoidHom.ker_comp_of_injective _ _ eB.injective,ker_subgroupMap]
  have hg2 : IsPGroup 2 g.ker := hgker ▸ hk.comap_subtype
  have hE' : Nat.card (E.subgroupOf P) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv).trans hE
  have hh := symmetricFour_core_section_pos g hg hg2 (E.subgroupOf P) hE'
  have hcore : (P.pCoreIn 2).subgroupOf P = pCore 2 P :=
    comap_map_eq_self_of_injective P.subtype_injective _
  rw [hgker,←hcore] at hh
  simpa only [sectionCubicLength,
    length_subgroupOf E (P.pCoreIn 2) P hEP (P.pCoreIn_le 2),
    length_subgroupOf E f.ker P hEP hkP] using hh
end Matrix.PSL3Two
