module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreAction
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.GeometryCertificate
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.SecondNormalizer.Characteristic


/-!
# The center and centralizer of the actual second Tits core

Let E be the already constructed four-element second center of the marked
Sylow subgroup. Its centralizer in the second parabolic is normal and lies in
the Sylow subgroup by the checked point test. The first 1024 normal forms lie
in this centralizer, so its order and the known core order identify it with
the actual two-core. Commuting with s3 and s7 restricts the core center to E.

This proves the center order and its exact relative centralizer, and provides
a bijective normal-form parametrization of the literal core. The conjugation
kernel, model-image order and inner-image order follow without a splitting.
These facts feed the action-image reconstruction, not an assumed endpoint
isomorphism.

Source: Parrott (1972), §5, p.683, and Aschbacher--Smith F.1.12 and14.2.21,
printed pp.263 and988--989, in the existing Atlas1600 generator conventions.
-/

@[expose] public section

open Subgroup
namespace Tits.ExceptionalParabolics.SecondCoreAction
open AmalgamRigidity.SecondExtension RelativeSecondBlockLayers RelativeParabolicNormalizers
noncomputable section
private def x : second := gen 1 * gen 5 ^ 2
private def y : second := gen 1 * gen 2 * gen 3 ^ 2
private theorem x_val : x.val = atlas1600R5 := by
  rw [atlas1600R5_eq]
  rfl
private theorem y_val : y.val = secondCenterMate := rfl
private theorem x_mem : atlas1600R5 ∈ secondCenter := mem_sup_left (mem_zpowers _)
private theorem y_mem : secondCenterMate ∈ secondCenter := mem_sup_right (mem_zpowers _)
private abbrev E := secondCenter.subgroupOf second
private abbrev C := centralizer (E : Set second)
private theorem E_le : secondCenter ≤ second := secondCenter_le_sylow.trans sylow_le_second
private instance E_normal : E.Normal :=
  (normal_subgroupOf_iff_le_normalizer E_le).mpr second_le_normalizer_secondCenter
private theorem E_cases (z : second) : z ∈ E ↔ z = 1 ∨ z = y ∨ z = x ∨ z = x * y := by
  change z.val ∈ secondCenter ↔ _
  rw [mem_secondCenter_iff, ← x_val, ← y_val]
  change z.val = (1 : second).val ∨ z.val = y.val ∨ z.val = x.val ∨ z.val = (x*y).val ↔ _
  simp only [Subtype.val_inj]
private theorem mem_C (z : second) : z ∈ C ↔ x * z = z * x ∧ y * z = z * y := by
  rw [mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨h x ((E_cases x).mpr (Or.inr (Or.inr (Or.inl rfl)))),
      h y ((E_cases y).mpr (Or.inr (Or.inl rfl)))⟩
  · rintro ⟨hx,hy⟩ w hw
    rcases (E_cases w).mp hw with rfl | rfl | rfl | rfl
    · simp
    · exact hy
    · exact hx
    · calc
        (x*y)*z = x*(y*z) := mul_assoc _ _ _
        _ = x*(z*y) := congrArg (x * ·) hy
        _ = (z*x)*y := by rw [← mul_assoc,hx]
        _ = z*(x*y) := mul_assoc _ _ _
private theorem perm_x : perm x = SecondCenterCertificate.x := by
  simp only [x,map_mul,map_pow,perm_gen,packedGen,
    OuterOddSubgroups.OverlapCentralizers.Packed.perm_eq,
    OuterOddSubgroups.OverlapCentralizers.Packed.generator,SecondCenterCertificate.x]
  rfl
private theorem perm_y : perm y = SecondCenterCertificate.y := by
  simp only [y,map_mul,map_pow,perm_gen,packedGen,
    OuterOddSubgroups.OverlapCentralizers.Packed.perm_eq,
    OuterOddSubgroups.OverlapCentralizers.Packed.generator,SecondCenterCertificate.y]
  rfl
private theorem gen_centralizes (i : Fin 7) : gen ⟨i.val+1,by omega⟩ ∈ C := by
  apply (mem_C _).mpr
  constructor
  · apply perm_injective
    simp only [map_mul,perm_x,perm_gen]
    have h := Atlas1600SylowTwoCenterCertificate.central_word_commutes
      (⟨i.val,by omega⟩ : Fin 8)
    change SecondCenterCertificate.x * _ = _ * SecondCenterCertificate.x at h
    convert h using 1 <;>
      fin_cases i <;> simp [packedGen,
        OuterOddSubgroups.OverlapCentralizers.Packed.perm_eq,
        OuterOddSubgroups.OverlapCentralizers.Packed.generator,
        Atlas1600SylowTwoCenterCertificate.generator]
  · apply perm_injective
    simp only [map_mul,perm_y,perm_gen]
    have h := SecondCenterCertificate.sylow_y (⟨i.val,by omega⟩ : Fin 8)
    have hi : (⟨i.val,by omega⟩ : Fin 8) ≠ 7 := by
      fin_cases i <;> decide
    rw [if_neg hi] at h
    have he := (mul_inv_eq_iff_eq_mul.mp h).symm
    convert he using 1 <;>
      fin_cases i <;> simp [packedGen,
        OuterOddSubgroups.OverlapCentralizers.Packed.perm_eq,
        OuterOddSubgroups.OverlapCentralizers.Packed.generator,
        Atlas1600SylowTwoCenterCertificate.generator]
private theorem word_mem_C (n : Fin 2048) (hn : n.val < 1024) : word gen n ∈ C := by
  have hz : n.val / 1024 % 2 = 0 := by omega
  simp only [word,hz,pow_zero,mul_one]
  exact C.mul_mem (C.mul_mem (C.mul_mem (C.mul_mem (C.mul_mem (C.mul_mem
    (C.pow_mem (gen_centralizes 0) _) (C.pow_mem (gen_centralizes 1) _))
    (C.pow_mem (gen_centralizes 2) _)) (C.pow_mem (gen_centralizes 3) _))
    (C.pow_mem (gen_centralizes 4) _)) (C.pow_mem (gen_centralizes 5) _))
    (C.pow_mem (gen_centralizes 6) _)
private theorem word_injective : Function.Injective (word gen) := by
  intro a b hab
  have hv := congrArg Subtype.val hab
  simp only [word_gen_val] at hv
  exact atlas1600SylowTwoNormalForm_injective hv
private theorem C_card_lower : 1024 ≤ Nat.card C := by
  let f : Fin 1024 → C := fun n => ⟨word gen ⟨n.val,by omega⟩,word_mem_C _ n.isLt⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h := word_injective (congrArg Subtype.val hab)
    exact Fin.ext (congrArg (fun n : Fin 2048 => n.val) h)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

private theorem perm_normalForm (n : Fin 2048) (i : Fin 3) :
    perm (secondNormalForm (n,i)) = word packedGen n * rep packedGen i := by
  rw [← normalForm_gen,map_mul,map_word,map_rep]
  have hg : perm ∘ gen = packedGen := funext perm_gen
  rw [hg]
private theorem C_le_sylow : C ≤ S.subgroupOf second := by
  intro z hz
  obtain ⟨⟨n,i⟩,rfl⟩ := secondNormalForm_surjective z
  obtain ⟨hx,hy⟩ := (mem_C _).mp hz
  have hx' := congrArg (fun a : second => perm a 0) hx
  have hy' := congrArg (fun a : second => perm a 0) hy
  simp only [map_mul,Equiv.Perm.mul_apply,perm_normalForm,perm_x,perm_y] at hx' hy'
  obtain ⟨_,hi⟩ := GeometryCertificate.centralizer_candidates n i
    (beq_iff_eq.mpr hx'.symm) (beq_iff_eq.mpr hy'.symm)
  subst i
  change (secondNormalForm (n,0)).val ∈ S
  simpa only [secondNormalForm_val,SecondOrder.rep,Fin.val_zero,pow_zero,mul_one]
    using atlas1600SylowTwoNormalForm_mem n
private theorem C_eq_core : C = pCore 2 second := by
  have hp : IsPGroup 2 C := secondSylowTwo.isPGroup'.to_le
    (by simpa only [secondSylowTwo_coe] using C_le_sylow)
  have hc : C ≤ pCore 2 second := le_sSup ⟨inferInstance,hp⟩
  apply eq_of_le_of_card_ge hc
  rw [second_core_card]
  exact C_card_lower
private theorem E_le_core : E ≤ pCore 2 second :=
  le_sSup ⟨inferInstance,secondCenter_isPGroup.of_equiv (subgroupOfEquivOfLe E_le).symm⟩
private theorem word_zero : word gen 0 = 1 := by norm_num [word]
private theorem word_eleven : word gen 11 = y := by norm_num [word,y]
private theorem word_sixty_five : word gen 65 = x := by norm_num [word,x]
private theorem word_seventy_four : word gen 74 = x*y := by
  apply perm_injective
  rw [map_mul,perm_x,perm_y]
  change (word gen 74).val.val = _
  rw [word_gen_val,atlas1600SylowTwoNormalForm_val]
  exact SecondNormalizerCertificate.form_74
/-- The embedded core center is precisely the previously identified second
center of the marked Sylow subgroup. -/
theorem center_map_eq_secondCenter : (center Core).map (pCore 2 second).subtype =
    secondCenter.subgroupOf second := by
  apply le_antisymm
  · rintro z ⟨q,hq,rfl⟩
    change q.val ∈ E
    obtain ⟨n,hn⟩ := atlas1600SylowTwoNormalForm_surjective
      (C_le_sylow (C_eq_core.ge q.property))
    have hn' : word gen n = q.val := Subtype.ext ((word_gen_val n).trans hn)
    have comm (i : Fin 7) :
        GeometryCertificate.commutesZero (word packedGen n) (packedGen ⟨i.val+1,by omega⟩) = true := by
      have hg : gen ⟨i.val+1,by omega⟩ ∈ pCore 2 second := C_eq_core.le (gen_centralizes i)
      have he := congrArg (fun q : Core => perm q.val 0)
        (mem_center_iff.mp hq ⟨_,hg⟩)
      change perm (_ * q.val) 0 = perm (q.val * _) 0 at he
      rw [← hn'] at he
      simp only [map_mul,Equiv.Perm.mul_apply,map_word,perm_gen] at he
      have hf : perm ∘ gen = packedGen := funext perm_gen
      rw [hf] at he
      exact beq_iff_eq.mpr he.symm
    rcases GeometryCertificate.center_candidates n (comm 2) (comm 6) with rfl | rfl | rfl | rfl
    · rw [← hn',word_zero,E_cases]; exact Or.inl rfl
    · rw [← hn',word_eleven,E_cases]; exact Or.inr (Or.inl rfl)
    · rw [← hn',word_sixty_five,E_cases]; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [← hn',word_seventy_four,E_cases]; exact Or.inr (Or.inr (Or.inr rfl))
  · intro z hz
    refine ⟨⟨z,E_le_core hz⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro q
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (C_eq_core.ge q.property) z hz).symm
private def planeIndex : Fin 4 → Fin 2048 := ![0,11,65,74]
private theorem planeIndex_injective : Function.Injective planeIndex := by decide
private def planeWord : Fin 4 → second := ![1,y,x,x*y]
private theorem planeWord_eq (i : Fin 4) : planeWord i = word gen (planeIndex i) := by
  fin_cases i
  · exact word_zero.symm
  · exact word_eleven.symm
  · exact word_sixty_five.symm
  · exact word_seventy_four.symm
private theorem E_card : Nat.card E = 4 := by
  let f : Fin 4 → E := fun i => ⟨planeWord i,by
    rw [E_cases]; fin_cases i <;> simp [planeWord]⟩
  have hi : Function.Injective f := by
    intro a b h
    have he := congrArg Subtype.val h
    change planeWord a = planeWord b at he
    simp only [planeWord_eq] at he
    exact planeIndex_injective (word_injective he)
  have hs : Function.Surjective f := by
    intro z
    rcases (E_cases z.val).mp z.property with h | h | h | h
    · exact ⟨0,Subtype.ext h.symm⟩
    · exact ⟨1,Subtype.ext h.symm⟩
    · exact ⟨2,Subtype.ext h.symm⟩
    · exact ⟨3,Subtype.ext h.symm⟩
  simpa only [Nat.card_fin] using (Nat.card_eq_of_bijective f ⟨hi,hs⟩).symm

/-- The first 1024 checked Sylow words enumerate the literal second two-core. -/
def coreNormalForm (n : Fin 1024) : Core :=
  ⟨word gen ⟨n.val,by omega⟩,by exact C_eq_core.le (word_mem_C _ n.isLt)⟩

theorem coreNormalForm_val (n : Fin 1024) :
    (coreNormalForm n : second) = word gen ⟨n.val,by omega⟩ := rfl

theorem coreNormalForm_bijective : Function.Bijective coreNormalForm := by
  have hi : Function.Injective coreNormalForm := by
    intro a b h
    have he := word_injective (congrArg Subtype.val h)
    exact Fin.ext (congrArg (fun n : Fin 2048 => n.val) he)
  apply hi.bijective_of_nat_card_le
  change Nat.card (pCore 2 second) ≤ Nat.card (Fin 1024)
  rw [second_core_card,Nat.card_fin]

/-- The center of the literal second two-core has order four. -/
theorem center_card : Nat.card (center Core) = 4 := by
  have hc := card_map_of_injective (K := center Core) (pCore 2 second).subtype_injective
  rw [center_map_eq_secondCenter,E_card] at hc
  exact hc.symm

/-- The four-element core center has exactly the core as its centralizer in
 the second parabolic. -/
theorem centralizer_center :
    centralizer ((center Core).map (pCore 2 second).subtype : Set second) = pCore 2 second := by
  rw [center_map_eq_secondCenter]
  exact C_eq_core

/-- The literal core is self-centralizing inside its parabolic. -/
theorem core_selfCentralizing : centralizer (pCore 2 second : Set second) ≤ pCore 2 second :=
  (centralizer_le (map_subtype_le (center Core))).trans centralizer_center.le

/-- The action kernel is the embedded center of the actual core. -/
theorem model_ker : model.ker = (center Core).map (pCore 2 second).subtype := by
  rw [model,MulAut.conjNormal_ker_eq_centralizer,
    map_center_subtype_eq_inf_centralizer,inf_eq_right.mpr core_selfCentralizing]

/-- The model image has order 1536, with the central kernel retained. -/
theorem model_range_card : Nat.card model.range = 1536 := by
  have h := model.ker.card_mul_index
  rw [index_ker,model_ker,card_map_of_injective (pCore 2 second).subtype_injective,
    center_card,second_card] at h
  omega

/-- Every inner automorphism already occurs in the specified Sylow action. -/
theorem inner_le_sylow_range : MulAut.innerSubgroup Core ≤ sylow.range := by
  rintro a ⟨q,rfl⟩
  refine ⟨(sylowCoreEquiv.symm q).val,?_⟩
  change model (inclusion sylow_le_second (sylowCoreEquiv.symm q).val) = MulAut.conj q
  rw [sylowCoreEquiv_symm_val]
  exact MulAut.conjNormal_val

/-- The actual inner automorphism subgroup has order 256. -/
theorem inner_card : Nat.card (MulAut.innerSubgroup Core) = 256 := by
  have hk : (MulAut.conj : Core →* MulAut Core).ker = center Core := by
    ext q
    change MulAut.conj q = 1 ↔ q ∈ center Core
    rw [mem_center_iff]
    constructor
    · intro h g
      have he := congrArg (fun a : MulAut Core => a g) h
      change q*g*q⁻¹ = g at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro h
      apply MulEquiv.ext
      intro g
      change q*g*q⁻¹ = g
      rw [← h g,mul_inv_cancel_right]
  have hc := (MulAut.conj : Core →* MulAut Core).ker.card_mul_index
  rw [index_ker,hk,center_card] at hc
  change 4 * Nat.card (MulAut.innerSubgroup Core) = Nat.card (pCore 2 second) at hc
  rw [second_core_card] at hc
  omega

/-- Inclusion of the marked Sylow also includes its whole action image. -/
theorem sylow_range_le_model_range : sylow.range ≤ model.range := by
  rintro _ ⟨s,rfl⟩
  exact ⟨inclusion sylow_le_second s,rfl⟩

end
end Tits.ExceptionalParabolics.SecondCoreAction
