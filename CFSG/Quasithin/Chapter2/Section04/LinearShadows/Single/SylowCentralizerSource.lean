module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DistinguishedSource
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.SylowLocalCore

/-!
# Sylow subgroups of the distinguished involution centralizers

The normal elementary subgroup Z of the original two-group S contains a
nonidentity point fixed by S. The original regular torus carries that point
to any prescribed element of Z#. Thus its centralizer contains a conjugate
of the full Sylow subgroup S of N(Z). The TI property puts that centralizer
inside N(Z), and Sylow conjugacy gives every centralizer Sylow. Since S<T,
no ambient conjugate of an element of Z# centralizes T.

Source: Aschbacher–Smith, 2.4.20(5) and its noncentrality consequence,
printed p.535.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
private lemma sylow_image_conj (N : Subgroup G) (P : Sylow 2 N) (a : N) :
    (((a • P : Sylow 2 N) : Subgroup N).map N.subtype) =
      ((P : Subgroup N).map N.subtype).map (MulAut.conj (a : G)).toMonoidHom := by
  change ((P : Subgroup N).map (MulAut.conj a).toMonoidHom).map N.subtype = _
  rw [map_map,map_map]
  rfl

/-- Every Sylow two-subgroup of the actual centralizer is conjugate to the original S. -/
theorem source_distinguished_centralizer_sylow
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (z : G) (hzZ : z ∈ distinguishedZ d) (hz1 : z ≠ 1)
    (P : Sylow 2 (centralizer ({z} : Set G))) :
    ∃ g : G, (P : Subgroup (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype =
      ((d.S : Subgroup d.H).map d.H.subtype).map (MulAut.conj g).toMonoidHom := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let Z := distinguishedZ d
  let N := normalizer (Z : Set G)
  let C := centralizer ({z} : Set G)
  have hb := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  have hTI := source_distinguished_TI_of_center_ne_bot d hG T hST hsingle hL hM hTM hunique hz
  have hZn : Z ≠ ⊥ := fun he => hz1 (mem_bot.mp (he ▸ hzZ))
  have hZS : Z ≤ S := hb.2.2.1.trans inf_le_left |>.trans (sSup_le fun _ h => h.1)
  have hn := inf_centerIn_ne_bot (d.S.isPGroup'.map d.H.subtype) hZn hZS hb.2.2.2
  obtain ⟨w,hw,hw1⟩ := (Z ⊓ centerIn S).bot_or_exists_ne_one.resolve_left hn
  have hCN : C ≤ N := by
    intro c hc
    apply hTI.1.mem_normalizer_of_conj_mem hzZ hz1
    have he : c*z*c⁻¹=z := by
      rw [(mem_centralizer_singleton_iff.mp hc),mul_inv_cancel_right]
    rwa [he]
  have hMe : M ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)
  have hbase := lemma_2_4_3_1 hG.evenCharacteristic hMe d.mem_gammaEvenZero d.full_pair d.S le_rfl
  have hNS : ∃ P₀ : Sylow 2 N, (P₀ : Subgroup N).map N.subtype = S := by
    change ∃ P₀ : Sylow 2 (normalizer (distinguishedZ d : Set G)),
      (P₀ : Subgroup (normalizer (distinguishedZ d : Set G))).map
        (normalizer (distinguishedZ d : Set G)).subtype = S
    rw [hTI.2]
    exact hbase.2.2
  obtain ⟨P₀,hP₀⟩ := hNS
  obtain ⟨_,D,_,_,_,x,_,_,_,hcent⟩ :=
    source_center_torus_and_splitting d hG T hST hsingle hL hM hTM hunique
  obtain ⟨_,hEN,hreg⟩ := hcent.resolve_left hz
  let L := d.block.map d.H.subtype
  have hZeq : Z = (center L).map L.subtype := distinguishedZ_of_center_ne_bot d hz
  obtain ⟨a,ha,_⟩ := hreg ⟨w,hZeq ▸ hw.1⟩
    (fun he => hw1 (congrArg Subtype.val he)) ⟨z,hZeq ▸ hzZ⟩
    (fun he => hz1 (congrArg Subtype.val he))
  have haN : (a : G) ∈ N := by
    change (a : G) ∈ normalizer (Z : Set G)
    rw [hZeq]
    exact hEN a.property
  let aN : N := ⟨a,haN⟩
  let Q : Sylow 2 N := aN • P₀
  have hQimage : (Q : Subgroup N).map N.subtype = S.map (MulAut.conj (a : G)).toMonoidHom := by
    rw [sylow_image_conj,hP₀]
  have hQC : (Q : Subgroup N).map N.subtype ≤ C := by
    rw [hQimage]
    rintro b ⟨s,hs,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hc : Commute s w := hw.2.2 s hs
    have hm := hc.map (MulAut.conj (a : G)).toMonoidHom
    change (MulAut.conj (a : G)) s * (MulAut.conj (a : G)) w =
      (MulAut.conj (a : G)) w * (MulAut.conj (a : G)) s at hm
    rwa [show (MulAut.conj (a : G)) w = z from ha] at hm
  obtain ⟨P₁,hP₁⟩ := Q.exists_map_subtype_eq_of_le hCN hQC
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq C P₁ P
  refine ⟨(c : G)*(a : G),?_⟩
  rw [←hc,sylow_image_conj,hP₁,hQimage,map_map]
  congr 1
  ext s
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_inv_rev]
  group

alias lemma_2_4_20_5 := source_distinguished_centralizer_sylow

/-- No ambient conjugate of an element of Z# centralizes the original T. -/
theorem source_distinguished_not_two_central
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (z : G) (hzZ : z ∈ distinguishedZ d) (hz1 : z ≠ 1) (g : G) :
    ¬ (T : Subgroup G) ≤ centralizer ({g*z*g⁻¹} : Set G) := by
  intro hT
  let C := centralizer ({z} : Set G)
  let e := MulAut.conj g⁻¹
  let U := (T : Subgroup G).map e.toMonoidHom
  have hUC : U ≤ C := by
    rintro u ⟨t,ht,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hc : Commute t (g*z*g⁻¹) := mem_centralizer_singleton_iff.mp (hT ht)
    have he := hc.map e.toMonoidHom
    simpa only [e,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,mul_assoc,
      inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_one] using he.eq
  have hpU : IsPGroup 2 U := T.isPGroup'.map e.toMonoidHom
  obtain ⟨P,hUP⟩ := (hpU.comap_subtype (K := C)).exists_le_sylow
  have hUP' : U ≤ (P : Subgroup C).map C.subtype := by
    rw [←map_subgroupOf_eq_of_le hUC]
    exact map_mono hUP
  obtain ⟨a,ha⟩ := source_distinguished_centralizer_sylow d hG T hST hsingle hL hM hTM hunique
    hz z hzZ hz1 P
  have hc := Nat.card_le_card_of_injective (inclusion hUP') (inclusion_injective hUP')
  have hcU : Nat.card U = Nat.card (T : Subgroup G) := card_map_of_injective e.injective
  have hcP : Nat.card ((P : Subgroup C).map C.subtype) =
      Nat.card ((d.S : Subgroup d.H).map d.H.subtype) := by
    rw [ha]
    exact card_map_of_injective (MulAut.conj a).injective
  rw [hcU,hcP] at hc
  exact hST.ne (eq_of_le_of_card_ge hST.le hc)

end CFSG.Quasithin.Chapter2.LinearShadows.Single
