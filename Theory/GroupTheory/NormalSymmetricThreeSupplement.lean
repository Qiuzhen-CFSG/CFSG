module

public import Theory.GroupTheory.NormalSymmetricThree
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.SymmetricThreeNormalSupplementIndex
public import Mathlib.Data.Fintype.Perm

/-!
# Symmetric-three quotients of normal supplements

A normal S₃ splits off its centralizer. If an index-three supplement has
S₃ quotient modulo its two-core, its projection to that centralizer has
kernel of order two. This identifies the whole core-free group with
S₃ × S₃. Passing through the literal two-core quotient gives the same
criterion for an arbitrary finite group.

A normal subgroup with S₃ quotient also retains that quotient after
adjoining a normalizing two-subgroup: the complementary centralizer is
a normal two-group and disappears modulo the two-core. The Chapter13
consumer applies these facts to C_L(z) in L₁T and then to the original
Thompson span in C_G(z).

Source: Aschbacher–Smith, 13.4.8(3), printed p.905.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.NormalSymmetricThree
variable {G : Type*} [Group G] [Finite G]
local notation "S3" => Equiv.Perm (Fin 3)

theorem pair_of_index_three_supplement
    (hcore : pCore 2 G = ⊥)
    (I M : Subgroup G) [I.Normal] (eI : I ≃* S3)
    (hgen : I ⊔ M = ⊤) (hi : M.index = 3)
    (eM : (M ⧸ pCore 2 M) ≃* S3) : Nonempty (G ≃* (S3 × S3)) := by
  let C := centralizer (I : Set G)
  obtain ⟨d,hd⟩ := exists_product_equiv I eI
  let f : G →* C := (MonoidHom.snd I C).comp d.symm.toMonoidHom
  have hfI (i : I) : f i = 1 := by
    have hh : d (i,1) = i := by simpa using hd i 1
    change (d.symm i).2 = 1
    rw [← hh,d.symm_apply_apply]
  have hfC (c : C) : f c = c := by
    have hh : d (1,c) = c := by simpa using hd 1 c
    change (d.symm c).2 = c
    rw [← hh,d.symm_apply_apply]
  have hk : f.ker = I := by
    apply le_antisymm
    · intro g hg
      have hh : (d.symm g).2 = 1 := hg
      have he : g = ((d.symm g).1 : G) := by
        calc
          g = d (d.symm g) := (d.apply_symm_apply g).symm
          _ = ((d.symm g).1 : G) * ((d.symm g).2 : G) := hd _ _
          _ = _ := by rw [hh,coe_one,mul_one]
      rw [he]
      exact (d.symm g).1.property
    · exact fun g hg => hfI ⟨g,hg⟩
  let r : M →* C := f.comp M.subtype
  have hr : Function.Surjective r := by
    intro c
    have hc : (c : G) ∈ (I : Set G) * (M : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left I M le_normalizer_of_normal,hgen]
      trivial
    obtain ⟨i,hi,m,hm,he⟩ := hc
    refine ⟨⟨m,hm⟩,?_⟩
    have hh := congrArg f he
    rw [map_mul,hfI ⟨i,hi⟩,one_mul,hfC c] at hh
    exact hh
  have hcardI : Nat.card I = 6 := by
    rw [Nat.card_congr eI.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  have hcardIM : Nat.card (I ⊓ M : Subgroup G) = 2 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes I M le_normalizer_of_normal
    rw [hgen,card_top,← M.card_mul_index,hi,hcardI] at hh
    have hm := Nat.card_pos (α := M)
    nlinarith
  have hrk : r.ker = I.subgroupOf M := by
    change f.ker.comap M.subtype = I.subgroupOf M
    rw [hk]
    rfl
  have hpk : IsPGroup 2 r.ker := by
    rw [hrk]
    have he : Nat.card (I.subgroupOf M) = Nat.card (I ⊓ M : Subgroup G) := by
      rw [← card_map_of_injective M.subtype_injective,subgroupOf_map_subtype]
    exact IsPGroup.of_card (n := 1) (by rw [he,hcardIM];rfl)
  have hcCore : pCore 2 C = ⊥ := by
    have hle : (pCore 2 C).map C.subtype ≤ pCore 2 G :=
      le_sSup ⟨by dsimp [C]; infer_instance,pCore_isPGroup.map C.subtype⟩
    apply ((pCore 2 C).map_eq_bot_iff_of_injective C.subtype_injective).mp
    exact bot_unique (hle.trans hcore.le)
  let eC : C ≃* S3 :=
    ((QuotientGroup.quotientMulEquivOfEq hcCore).trans QuotientGroup.quotientBot).symm.trans
      ((r.pCoreQuotientEquiv hr hpk).symm.trans eM)
  exact ⟨d.symm.trans (eI.prodCongr eC)⟩

omit [Finite G] in
theorem symmetricThree_of_twoGroup_supplement
    (hcore : pCore 2 G = ⊥)
    (I P : Subgroup G) [I.Normal] (eI : I ≃* S3)
    (hP : IsPGroup 2 P) (hgen : I ⊔ P = ⊤) : Nonempty (G ≃* S3) := by
  let C := centralizer (I : Set G)
  obtain ⟨d,hd⟩ := exists_product_equiv I eI
  let f : G →* C := (MonoidHom.snd I C).comp d.symm.toMonoidHom
  have hfI (i : I) : f i = 1 := by
    have hh : d (i,1) = i := by simpa using hd i 1
    change (d.symm i).2 = 1
    rw [← hh,d.symm_apply_apply]
  have hfC (c : C) : f c = c := by
    have hh : d (1,c) = c := by simpa using hd 1 c
    change (d.symm c).2 = c
    rw [← hh,d.symm_apply_apply]
  have hr : Function.Surjective (f.comp P.subtype) := by
    intro c
    have hc : (c : G) ∈ (I : Set G) * (P : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left I P le_normalizer_of_normal,hgen]
      trivial
    obtain ⟨i,hi,p,hp,he⟩ := hc
    refine ⟨⟨p,hp⟩,?_⟩
    have hh := congrArg f he
    rw [map_mul,hfI ⟨i,hi⟩,one_mul,hfC c] at hh
    exact hh
  have hC : IsPGroup 2 C := hP.of_surjective _ hr
  have hCbot : C = ⊥ :=
    bot_unique ((show C ≤ pCore 2 G from le_sSup ⟨by dsimp [C];infer_instance,hC⟩).trans hcore.le)
  have hI : I = ⊤ := by
    have hh := sup_centralizer_eq_top I eI
    change I ⊔ C = ⊤ at hh
    rwa [hCbot,sup_bot_eq] at hh
  exact ⟨((MulEquiv.subgroupCongr hI).trans topEquiv).symm.trans eI⟩


theorem quotient_pair_of_normal_supplement
    (I M : Subgroup G) [I.Normal]
    (eI : (I ⧸ pCore 2 I) ≃* S3)
    (eM : (M ⧸ pCore 2 M) ≃* S3)
    (P : Sylow 2 G) (hPM : (P : Subgroup G) ≤ M)
    (hM : M ≠ ⊤) (hgen : I ⊔ M = ⊤) :
    Nonempty ((G ⧸ pCore 2 G) ≃* (S3 × S3)) := by
  let Q := G ⧸ pCore 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  have hq := QuotientGroup.mk'_surjective (pCore 2 G)
  have hqker : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hQcore : pCore 2 Q = ⊥ := by
    apply comap_injective hq
    rw [q.comap_pCore_of_ker_isPGroup hq hqker,MonoidHom.comap_bot,QuotientGroup.ker_mk']
  let B := I.map q
  let A := M.map q
  let : B.Normal := Normal.map inferInstance q hq
  have hBcore : pCore 2 B = ⊥ := by
    have hle : (pCore 2 B).map B.subtype ≤ pCore 2 Q :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map B.subtype⟩
    apply ((pCore 2 B).map_eq_bot_iff_of_injective B.subtype_injective).mp
    exact bot_unique (hle.trans hQcore.le)
  have hkI : IsPGroup 2 (q.subgroupMap I).ker := by
    rw [ker_subgroupMap]
    exact hqker.comap_subtype
  let eb : B ≃* S3 :=
    ((QuotientGroup.quotientMulEquivOfEq hBcore).trans QuotientGroup.quotientBot).symm.trans
      (((q.subgroupMap I).pCoreQuotientEquiv (q.subgroupMap_surjective I) hkI).symm.trans eI)
  have hkM : IsPGroup 2 (q.subgroupMap M).ker := by
    rw [ker_subgroupMap]
    exact hqker.comap_subtype
  let ea : (A ⧸ pCore 2 A) ≃* S3 :=
    ((q.subgroupMap M).pCoreQuotientEquiv (q.subgroupMap_surjective M) hkM).symm.trans eM
  have hMA : A.comap q = M := by
    rw [comap_map_eq,sup_eq_left.mpr]
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal P).trans hPM
  have hAi : A.index = 3 := by
    rw [← A.index_comap_of_surjective hq,hMA]
    exact index_three_of_symmetricThree_normal_supplement I M eI P hPM hM hgen
  have hgen' : B ⊔ A = ⊤ := by
    rw [← Subgroup.map_sup,hgen,← MonoidHom.range_eq_map,q.range_eq_top_of_surjective hq]
  exact pair_of_index_three_supplement hQcore B A eb hgen' hAi ea

theorem quotient_symmetricThree_of_normal_twoGroup_supplement
    (I P : Subgroup G) [I.Normal]
    (eI : (I ⧸ pCore 2 I) ≃* S3)
    (hP : IsPGroup 2 P) (hgen : I ⊔ P = ⊤) :
    Nonempty ((G ⧸ pCore 2 G) ≃* S3) := by
  let Q := G ⧸ pCore 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  have hq := QuotientGroup.mk'_surjective (pCore 2 G)
  have hqker : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hQcore : pCore 2 Q = ⊥ := by
    apply comap_injective hq
    rw [q.comap_pCore_of_ker_isPGroup hq hqker,MonoidHom.comap_bot,QuotientGroup.ker_mk']
  let B := I.map q
  let A := P.map q
  let : B.Normal := Normal.map inferInstance q hq
  have hBcore : pCore 2 B = ⊥ := by
    have hle : (pCore 2 B).map B.subtype ≤ pCore 2 Q :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map B.subtype⟩
    apply ((pCore 2 B).map_eq_bot_iff_of_injective B.subtype_injective).mp
    exact bot_unique (hle.trans hQcore.le)
  have hkI : IsPGroup 2 (q.subgroupMap I).ker := by
    rw [ker_subgroupMap]
    exact hqker.comap_subtype
  let eb : B ≃* S3 :=
    ((QuotientGroup.quotientMulEquivOfEq hBcore).trans QuotientGroup.quotientBot).symm.trans
      (((q.subgroupMap I).pCoreQuotientEquiv (q.subgroupMap_surjective I) hkI).symm.trans eI)
  have hgen' : B ⊔ A = ⊤ := by
    rw [← Subgroup.map_sup,hgen,← MonoidHom.range_eq_map,q.range_eq_top_of_surjective hq]
  exact symmetricThree_of_twoGroup_supplement hQcore B A eb (hP.map q) hgen'

end Theory.GroupTheory.NormalSymmetricThree
