module
public import Theory.SpecificGroups.SymmetricEight.NineBlockCertificate
public import Mathlib.GroupTheory.SpecificGroups.Alternating
/-!
# Even nine-quotient subgroups of S₈ preserve four-blocks

For an even subgroup I with |I/O₂(I)| = 9, its Sylow three-subgroup is
already Sylow in S₈. Conjugate it to two disjoint cubics. The commutator
certificate places every element of O₂(I) in one of two Klein-four products;
the subgroup-in-a-union lemma makes the placement uniform. The Sylow
supplement then places all of I in the same unordered four-block stabilizer.

This is the concrete containment used in Aschbacher--Smith 12.6.19, printed
p.828 of the combined 1 March 2004 manuscript. It preserves the literal
subgroup I and returns an actual permutation conjugator. Its source consumer
is `Chapter12.Section06.CentralLine.FourBlockRecognition`.
-/

@[expose] public section
open Subgroup Equiv.Perm
namespace Theory.SpecificGroups.SymmetricEight.NineBlockContainment
open NineBlockCertificate FourBlockCoreAction

private theorem twoElement_eighth (N : Subgroup S8) (hn : IsPGroup 2 N)
    (x : S8) (hx : x ∈ N) : x^8 = 1 := by
  obtain ⟨n,hn⟩ := hn ⟨x,hx⟩
  have hxpow : x^(2^n) = 1 := congrArg Subtype.val hn
  rw [←orderOf_dvd_iff_pow_eq_one,←Equiv.Perm.lcm_cycleType,Multiset.lcm_dvd]
  intro c hc
  have hcle : c ≤ 8 := (Multiset.le_sum_of_mem hc).trans (x.sum_cycleType_le.trans (by simp))
  have hd : c ∣ 2^n := (Equiv.Perm.dvd_of_mem_cycleType hc).trans (orderOf_dvd_of_pow_eq_one hxpow)
  obtain ⟨k,_,rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hk : k ≤ 3 := by
    by_contra h
    have hh : 16 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ k)
    omega
  exact pow_dvd_pow 2 hk

private abbrev C3 := Multiplicative (ZMod 3)
private def cubicMap : C3 × C3 →* S8 where
  toFun x := leftCubic^x.1.toAdd.val * rightCubic^x.2.toAdd.val
  map_one' := by decide
  map_mul' := by decide
private theorem cubicMap_injective : Function.Injective cubicMap := by decide
private theorem cubicMap_card : Nat.card cubicMap.range = 9 := by
  rw [←Nat.card_congr (MonoidHom.ofInjective cubicMap_injective).toEquiv,Nat.card_prod]
  simp only [Nat.card_eq_fintype_card]
  decide
private noncomputable def cubicSylow : Sylow 3 S8 := Sylow.ofCard cubicMap.range (by
  rw [cubicMap_card,Nat.card_perm,Nat.card_fin]
  decide +kernel)
private theorem left_mem : leftCubic ∈ (cubicSylow : Subgroup S8) :=
  ⟨(Multiplicative.ofAdd (1:ZMod 3),1),by decide⟩
private theorem right_mem : rightCubic ∈ (cubicSylow : Subgroup S8) :=
  ⟨(1,Multiplicative.ofAdd (1:ZMod 3)),by decide⟩
private theorem cubic_le_blocks : (cubicSylow : Subgroup S8) ≤ A6ShadowTwoLocals.fourStabilizer := by
  rintro _ ⟨x,rfl⟩
  revert x
  decide
private theorem switch_cubic_le_blocks :
    (cubicSylow : Subgroup S8).map (MulAut.conj switch).toMonoidHom ≤ A6ShadowTwoLocals.fourStabilizer := by
  rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
  revert x
  decide


private theorem normalized_core_le (N : Subgroup S8)
    (hn : IsPGroup 2 N) (he : N ≤ alternatingGroup (Fin 8))
    (hc : (cubicSylow : Subgroup S8) ≤ normalizer (N : Set S8)) :
    N ≤ kleinGroup ∨ N ≤ kleinGroup.map (MulAut.conj switch).toMonoidHom := by
  apply SubgroupClass.subset_union.mp
  intro x hx
  have hcomm (x : S8) (hx : x ∈ N) (y : S8)
      (hy : y ∈ (cubicSylow : Subgroup S8)) : comm x y ∈ N := by
    change x*y*x⁻¹*y⁻¹ ∈ N
    simpa only [mul_assoc] using N.mul_mem hx ((hc hy _).mp (N.inv_mem hx))
  have hh := element_certificate x (he hx) (twoElement_eighth N hn x hx)
    (twoElement_eighth N hn _ (hcomm x hx leftCubic left_mem))
    (twoElement_eighth N hn _ (hcomm _ (hcomm x hx leftCubic left_mem) rightCubic right_mem))
    (twoElement_eighth N hn _ (hcomm x hx rightCubic right_mem))
    (twoElement_eighth N hn _ (hcomm _ (hcomm x hx rightCubic right_mem) leftCubic left_mem))
    (twoElement_eighth N hn _ (hcomm x hx (leftCubic*rightCubic)
      ((cubicSylow : Subgroup S8).mul_mem left_mem right_mem)))
  rcases hh with ⟨a,b,rfl⟩ | ⟨a,b,rfl⟩
  · exact Or.inl ⟨a,b,rfl⟩
  · exact Or.inr (mem_map_of_mem (MulAut.conj switch).toMonoidHom ⟨a,b,rfl⟩)

/-- An even subgroup of S₈ with two-core quotient of order nine lies in a
conjugate of the unordered four-block stabilizer. -/
theorem exists_conjugate_le_fourStabilizer (I : Subgroup S8)
    (heven : I ≤ alternatingGroup (Fin 8)) (hcard : Nat.card (I ⧸ pCore 2 I) = 9) :
    ∃ s : S8, I.map (MulAut.conj s).toMonoidHom ≤ A6ShadowTwoLocals.fourStabilizer := by
  classical
  let P : Sylow 3 I := Classical.choice inferInstance
  let q := QuotientGroup.mk' (pCore 2 I)
  have hthree : IsPGroup 3 (I ⧸ pCore 2 I) := IsPGroup.of_card (n := 2) hcard
  have htop : (P : Subgroup I).map q = ⊤ := by
    have hh := (hthree.to_subgroup ⊤).le_sylow_of_normal
      (P.mapSurjective (QuotientGroup.mk'_surjective _))
    exact top_le_iff.mp hh
  have hgen : (P : Subgroup I) ⊔ pCore 2 I = ⊤ := by
    have hh := congrArg (Subgroup.comap q) htop
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk',comap_top] using hh
  have hsurj : Function.Surjective (q.comp (P : Subgroup I).subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,range_subtype]
    exact htop
  have hnine : 9 ≤ Nat.card P := by
    rw [←hcard]
    exact Nat.card_le_card_of_surjective _ hsurj
  obtain ⟨U,hPU⟩ := (P.isPGroup'.map I.subtype).exists_le_sylow
  have hUcard : Nat.card U = 9 := by
    rw [U.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    decide +kernel
  have hPUeq : (P : Subgroup I).map I.subtype = (U : Subgroup S8) :=
    eq_of_le_of_card_ge hPU (by
      rw [hUcard,card_map_of_injective I.subtype_injective]
      exact hnine)
  obtain ⟨s,hs⟩ := MulAction.exists_smul_eq S8 U cubicSylow
  let f := (MulAut.conj s).toMonoidHom
  have hPf : ((P : Subgroup I).map I.subtype).map f = (cubicSylow : Subgroup S8) := by
    rw [hPUeq]
    change ((s • U : Sylow 3 S8) : Subgroup S8) = _
    rw [hs]
  let N := (pCore 2 I).map I.subtype
  have hIN : I ≤ normalizer (N : Set S8) := by
    have hh := (pCore 2 I).le_normalizer_map I.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hN : IsPGroup 2 (N.map f) := (pCore_isPGroup.map I.subtype).map f
  have hNeven : N.map f ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨x,hx,rfl⟩
    have hx' := heven (map_subtype_le (pCore 2 I) hx)
    change sign (s*x*s⁻¹) = 1
    simp only [map_mul,map_inv,show sign x = 1 from hx',mul_one,mul_inv_cancel]
  have hnormal : (cubicSylow : Subgroup S8) ≤ normalizer (N.map f : Set S8) := by
    rw [←hPf]
    exact (map_mono ((map_subtype_le (P : Subgroup I)).trans hIN)).trans (N.le_normalizer_map f)
  have hIf : I.map f = (cubicSylow : Subgroup S8) ⊔ N.map f := by
    have hh := congrArg (fun J : Subgroup I => (J.map I.subtype).map f) hgen
    simpa only [Subgroup.map_sup,hPf,←MonoidHom.range_eq_map,range_subtype] using hh.symm
  have hK : kleinGroup ≤ A6ShadowTwoLocals.fourStabilizer := by
    rw [←fourStabilizer_pCoreIn]
    exact pCoreIn_le _ _
  rcases normalized_core_le (N.map f) hN hNeven hnormal with hle | hle
  · refine ⟨s,?_⟩
    rw [hIf]
    exact sup_le cubic_le_blocks (hle.trans hK)
  · let t := (MulAut.conj switch).toMonoidHom
    have htt : t.comp t = MonoidHom.id S8 := by
      apply MonoidHom.ext
      intro x
      change switch * (switch*x*switch⁻¹) * switch⁻¹ = x
      have ht : switch * switch = 1 := by decide
      have hti : switch⁻¹ = switch := inv_eq_of_mul_eq_one_left ht
      rw [hti]
      calc
        _ = (switch*switch)*x*(switch*switch) := by group
        _ = x := by rw [ht,one_mul,mul_one]
    have hKtt : (kleinGroup.map t).map t = kleinGroup := by rw [map_map,htt,map_id]
    have hboth : (I.map f).map t ≤ A6ShadowTwoLocals.fourStabilizer := by
      rw [hIf,Subgroup.map_sup]
      exact sup_le switch_cubic_le_blocks
        (((map_mono hle).trans_eq hKtt).trans hK)
    refine ⟨switch*s,?_⟩
    have hf : (MulAut.conj (switch*s)).toMonoidHom = t.comp f := by
      ext x
      simp [t,f,MulAut.conj_apply,mul_assoc]
    rw [hf,←map_map]
    exact hboth

end Theory.SpecificGroups.SymmetricEight.NineBlockContainment
