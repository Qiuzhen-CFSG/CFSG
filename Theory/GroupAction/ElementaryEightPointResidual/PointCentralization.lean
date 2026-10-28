module
public import Theory.GroupAction.ElementaryEightPointResidual.Sylow
public import Mathlib.Data.Fintype.Perm
public import Theory.GroupTheory.SubgroupTransport

/-!
# Point images centralizing a cubic quotient

An actor on an elementary eight-group which normalizes an A₄ point image
and centralizes its quotient modulo a two-group belongs to that A₄.
The proof restricts to the S₄ point stabilizer and detects odd permutations
by their commutators with A₄. The final theorem uses the literal conjugation
images and the intrinsic two-core of the original point residual.

This calculation is shared by Sylow promotion and full action-kernel
containment in Aschbacher–Smith 14.7.6, printed pp.1044–1045.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupAction.ElementaryEightPointResidual

private theorem symmetric_four_core_detector :
    ∀ x : Equiv.Perm (Fin 4),
      (∀ y : Equiv.Perm (Fin 4), y.sign = 1 → ⁅x,y⁆ ^ 4 = 1) → x.sign = 1 := by
  decide +kernel

/-- Centralizing the alternating quotient modulo a two-group forces an
actor in S₄ to be even. -/
private theorem symmetric_four_two_subgroup_bound
    {X : Type*} [Group X] [Finite X]
    (e : X ≃* Equiv.Perm (Fin 4)) (B A Q : Subgroup X)
    (hB : Nat.card B = 12) (hQ : IsPGroup 2 Q) (hQB : Q ≤ B)
    (hcomm : ⁅A,B⁆ ≤ Q) : A ≤ B := by
  have hX : Nat.card X = 24 := by
    rw [Nat.card_congr e.toEquiv]
    simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  have hBi : B.index = 2 := by
    have hh := B.card_mul_index
    rw [hB,hX] at hh
    omega
  have hBm : B.map e.toMonoidHom = alternatingGroup (Fin 4) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two ((B.index_map_equiv e).trans hBi)
  have hQd : Nat.card Q ∣ 4 := by
    have hd := hB ▸ card_dvd_of_le hQB
    obtain ⟨n,hn⟩ := hQ.exists_card_eq
    have hc : Nat.Coprime (Nat.card Q) 3 := by
      rw [hn]
      exact (by decide : Nat.Coprime 2 3).pow_left n
    exact hc.dvd_of_dvd_mul_right hd
  have hAB : A ≤ B := by
    intro a ha
    have hm : e a ∈ alternatingGroup (Fin 4) := by
      apply symmetric_four_core_detector
      intro y hy
      have hyB : e.symm y ∈ B := by
        have hy' : y ∈ B.map e.toMonoidHom := hBm.symm ▸ hy
        simpa only [MulEquiv.symm_apply_apply] using mem_map_equiv.mp hy'
      have hc : ⁅a,e.symm y⁆ ∈ Q := hcomm (commutator_mem_commutator ha hyB)
      have hp : ⁅a,e.symm y⁆ ^ 4 = 1 := by
        have hh : (⟨⁅a,e.symm y⁆,hc⟩ : Q) ^ 4 = 1 :=
          orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard (⟨⁅a,e.symm y⁆,hc⟩ : Q)).trans hQd)
        exact congrArg Subtype.val hh
      simpa only [map_pow,map_one,map_commutatorElement,MulEquiv.apply_symm_apply] using congrArg e hp
    have ha' : e a ∈ B.map e.toMonoidHom := hBm.symm ▸ hm
    simpa only [MulEquiv.symm_apply_apply] using mem_map_equiv.mp ha'
  exact hAB

private theorem point_normalizer_fixes
    {E : Type*} [Group E] (B : Subgroup (MulAut E)) (z : E) (hz : z ≠ 1)
    (hfix : ∀ b : B, (b : MulAut E) z = z)
    (hunique : ∀ x : E, (∀ b : B, (b : MulAut E) x = x) → x = 1 ∨ x = z) :
    normalizer (B : Set (MulAut E)) ≤ MulAction.stabilizer (MulAut E) z := by
  intro a ha
  have hb (b : B) : (b : MulAut E) (a z) = a z := by
    have hc : a⁻¹ * b * a ∈ B :=
      (mem_normalizer_iff.mp ((normalizer (B : Set (MulAut E))).inv_mem ha) b).mp b.property
    have hh := congrArg (fun f : E => a f) (hfix ⟨a⁻¹ * b * a,hc⟩)
    simpa using hh
  rcases hunique (a z) hb with he | he
  · exact (hz (a.injective (he.trans a.map_one.symm))).elim
  · exact he

private theorem point_image_two_actor_le
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (B A Q : Subgroup (MulAut E))
    (hB : Nat.card B = 12) (hQ : IsPGroup 2 Q) (hQB : Q ≤ B)
    (hAB : A ≤ normalizer (B : Set (MulAut E)))
    (hcomm : ⁅A,B⁆ ≤ Q) (z : E) (hz : z ≠ 1)
    (hfix : ∀ b : B, (b : MulAut E) z = z)
    (hunique : ∀ x : E, (∀ b : B, (b : MulAut E) x = x) → x = 1 ∨ x = z) :
    A ≤ B := by
  let J := MulAction.stabilizer (MulAut E) z
  have hBJ : B ≤ J := fun b hb => hfix ⟨b,hb⟩
  have hAJ : A ≤ J := hAB.trans (point_normalizer_fixes B z hz hfix hunique)
  obtain ⟨e⟩ := (full_point_stabilizer hE z hz).2
  have hle := symmetric_four_two_subgroup_bound e (B.subgroupOf J) (A.subgroupOf J)
    (Q.subgroupOf J)
    ((Nat.card_congr (subgroupOfEquivOfLe hBJ).toEquiv).trans hB)
    hQ.comap_subtype (subgroupOf_mono J hQB) (by
      rw [←Theory.GroupTheory.SubgroupTransport.subgroupOf_commutator A B hAJ hBJ]
      exact subgroupOf_mono J hcomm)
  intro a ha
  exact hle (show (⟨a,hAJ ha⟩ : J) ∈ A.subgroupOf J from ha)


/-- Centralization modulo the original point residual's two-core forces
containment in its actual A₄ image on the common eight-group. -/
theorem conjugationImage_le_point_image
    {G : Type*} [Group G] [Finite G]
    (A B C Z : Subgroup G) [IsElementaryAbelian 2 C]
    (hAC : A ≤ normalizer (C : Set G))
    (hBC : B ≤ normalizer (C : Set G))
    (hAB : A ≤ normalizer (B : Set G))
    (hc : Nat.card C = 8) (hz : Nat.card Z = 2)
    (hfixed : C ⊓ centralizer (B : Set G) = Z)
    (hB : Nat.card (conjugationImage B C) = 12)
    (hcomm : ⁅A,B⁆ ≤ B.pCoreIn 2) :
    conjugationImage A C ≤ conjugationImage B C := by
  let N := normalizer (C : Set G)
  have hQC : B.pCoreIn 2 ≤ N := (pCoreIn_le 2 B).trans hBC
  have hQ : IsPGroup 2 (conjugationImage (B.pCoreIn 2) C) := by
    rw [conjugationImage_eq_map_of_le _ _ hQC]
    exact (isPGroup_pCoreIn 2 B).comap_subtype.map _
  have hcommImage : ⁅conjugationImage A C,conjugationImage B C⁆ ≤
      conjugationImage (B.pCoreIn 2) C := by
    rw [conjugationImage_eq_map_of_le _ _ hAC,conjugationImage_eq_map_of_le _ _ hBC,
      conjugationImage_eq_map_of_le _ _ hQC,←map_commutator,
      ←Theory.GroupTheory.SubgroupTransport.subgroupOf_commutator A B hAC hBC]
    exact map_mono (subgroupOf_mono N hcomm)
  obtain ⟨z,hz1,hzu⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hz
  have hZC : Z ≤ C := hfixed ▸ inf_le_left
  let zC : C := ⟨z,hZC z.property⟩
  have hzC : zC ≠ 1 := fun he => hz1 (Subtype.ext (congrArg (fun c : C => (c : G)) he))
  have hfix : ∀ b : conjugationImage B C, (b : MulAut C) zC = zC :=
    (fixed_by_conjugationImage_iff B C hBC zC).mpr
      (show (z : G) ∈ C ⊓ centralizer (B : Set G) from hfixed.symm ▸ z.property).2
  have huniq (x : C) (hx : ∀ b : conjugationImage B C, (b : MulAut C) x = x) :
      x = 1 ∨ x = zC := by
    have hxZ : (x : G) ∈ Z := hfixed ▸
      (show (x : G) ∈ C ⊓ centralizer (B : Set G) from
        ⟨x.property,(fixed_by_conjugationImage_iff B C hBC x).mp hx⟩)
    by_cases h1 : x = 1
    · exact Or.inl h1
    · right
      apply Subtype.ext
      exact congrArg (fun v : Z => (v : G)) (hzu ⟨x,hxZ⟩
        (fun he => h1 (Subtype.ext (congrArg (fun v : Z => (v : G)) he))))
  have himage : conjugationImage A C ≤ conjugationImage B C := point_image_two_actor_le hc
    _ _ _ hB hQ (conjugationImage_mono (pCoreIn_le 2 B))
    (conjugationImage_normalizes A B C hAC hBC hAB) hcommImage zC hzC hfix huniq
  exact himage

end Theory.GroupAction.ElementaryEightPointResidual
