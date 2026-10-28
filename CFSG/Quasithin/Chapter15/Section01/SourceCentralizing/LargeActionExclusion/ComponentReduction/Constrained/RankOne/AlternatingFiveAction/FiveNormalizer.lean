module
public import Theory.SpecificGroups.SymmetricFive.OuterFourGeometry
import all Theory.SpecificGroups.SymmetricFive.OuterFourGeometry
/-!
# The odd-involution Thompson image in five-point coordinates

A two-subgroup normalized by an inner Sylow four-group and containing an
odd involution contains the two disjoint transpositions of a positioned
Sylow subgroup. Any element normalizing it preserves those transpositions,
so its normalizer is a two-group. The small checked certificates range over
individual permutations and the eight Sylow words. Conjugation transports
the conclusion to the literal image used by the A₅-block actor.

Source: the automorphism step of Aschbacher--Smith 15.1.21(ii), p.1098.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section01.ConstrainedFiveAction
open Theory.SpecificGroups.SymmetricFive.OuterFourGeometry

private theorem normalizer_between_four_eight (J : Subgroup D)
    (hF : four ≤ J) (hJ : J ≤ eight) : normalizer (J : Set D) ≤ eight := by
  have ht : ∀ g : D, (∃ i, word i = g*a*g⁻¹) →
      (∃ i, word i = g*b*g⁻¹) → ∃ i, word i = g := by decide +kernel
  intro g hg
  exact ht g
    (hJ ((mem_normalizer_iff.mp hg a).mp (hF ⟨1,rfl⟩)))
    (hJ ((mem_normalizer_iff.mp hg b).mp (hF ⟨2,rfl⟩)))

private theorem positioned_normalizer (J : Subgroup D) (hJ : J ≤ eight)
    (hn : eight ⊓ alternatingGroup (Fin 5) ≤ normalizer (J : Set D))
    (ho : ∃ t ∈ J, t ^ 2 = 1 ∧ t ∉ alternatingGroup (Fin 5)) :
    normalizer (J : Set D) ≤ eight := by
  obtain ⟨t,ht,ht2,hto⟩ := ho
  obtain ⟨i,hi⟩ := hJ ht
  have hchoices : ∀ i, (word i)^2=1 → (word i).sign ≠ 1 → word i=a ∨ word i=b := by
    decide +kernel
  have hc : c ∈ normalizer (J : Set D) := hn ⟨⟨4,rfl⟩,Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩
  have hab : a ∈ J ∧ b ∈ J := by
    have hsign : (word i).sign ≠ 1 := fun he => hto
      (Equiv.Perm.mem_alternatingGroup.mpr (hi ▸ he))
    rcases hchoices i (hi ▸ ht2) hsign with ha | hb
    · have haJ : a ∈ J := ha ▸ (hi ▸ ht)
      refine ⟨haJ,?_⟩
      have hh := (mem_normalizer_iff.mp hc a).mp haJ
      have he : c*a*c⁻¹=b := by decide +kernel
      rwa [he] at hh
    · have hbJ : b ∈ J := hb ▸ (hi ▸ ht)
      refine ⟨?_,hbJ⟩
      have hh := (mem_normalizer_iff.mp hc b).mp hbJ
      have he : c*b*c⁻¹=a := by decide +kernel
      rwa [he] at hh
  apply normalizer_between_four_eight J ?_ hJ
  rintro x ⟨j,rfl⟩
  fin_cases j
  · exact J.one_mem
  · exact hab.1
  · exact hab.2
  · exact J.mul_mem hab.1 hab.2

private theorem sylow_positioned_normalizer (P : Sylow 2 D) (J : Subgroup D)
    (hJ : J ≤ P)
    (hn : (P : Subgroup D) ⊓ alternatingGroup (Fin 5) ≤ normalizer (J : Set D))
    (ho : ∃ t ∈ J, t ^ 2 = 1 ∧ t ∉ alternatingGroup (Fin 5)) :
    IsPGroup 2 (normalizer (J : Set D)) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D P standardSylow
  let e := MulAut.conj g
  have hP : (P : Subgroup D).map e.toMonoidHom = eight := congrArg Sylow.toSubgroup hg
  have hA : (alternatingGroup (Fin 5)).map e.toMonoidHom = alternatingGroup (Fin 5) :=
    characteristic_iff_map_eq.mp inferInstance e
  have hn' : eight ⊓ alternatingGroup (Fin 5) ≤ normalizer (J.map e.toMonoidHom : Set D) := by
    have hh := map_mono (f := e.toMonoidHom) hn
    rwa [map_inf _ _ _ e.injective,hP,hA,map_equiv_normalizer_eq] at hh
  have ho' : ∃ t ∈ J.map e.toMonoidHom, t ^ 2 = 1 ∧ t ∉ alternatingGroup (Fin 5) := by
    obtain ⟨t,ht,ht2,hto⟩ := ho
    refine ⟨e t,mem_map_of_mem _ ht,by rw [←map_pow,ht2,map_one],?_⟩
    intro he
    rw [←hA] at he
    exact hto (by simpa only [e.symm_apply_apply] using (mem_map_equiv).mp he)
  have hN := positioned_normalizer (J.map e.toMonoidHom) (hP ▸ map_mono hJ) hn' ho'
  rw [←map_equiv_normalizer_eq] at hN
  exact (standardSylow.isPGroup'.to_le hN).of_equiv
    ((normalizer (J : Set D)).equivMapOfInjective e.toMonoidHom e.injective).symm

/-- The normalizer of the actual odd Thompson image is a two-group. -/
theorem normalizer_isTwoGroup (R : Sylow 2 (alternatingGroup (Fin 5))) (J : Subgroup D)
    (hJ : IsPGroup 2 J)
    (hn : (R : Subgroup (alternatingGroup (Fin 5))).map (alternatingGroup (Fin 5)).subtype ≤
      normalizer (J : Set D))
    (ho : ∃ t ∈ J, t ^ 2 = 1 ∧ t ∉ alternatingGroup (Fin 5)) :
    IsPGroup 2 (normalizer (J : Set D)) := by
  let F := (R : Subgroup (alternatingGroup (Fin 5))).map (alternatingGroup (Fin 5)).subtype
  obtain ⟨P,hP⟩ := ((R.isPGroup'.map (alternatingGroup (Fin 5)).subtype).to_sup_of_normal_right'
    hJ hn).exists_le_sylow
  have hFP : F ≤ P := le_sup_left.trans hP
  have he : (P : Subgroup D).subgroupOf (alternatingGroup (Fin 5)) = R :=
    R.is_maximal' P.isPGroup'.comap_subtype (map_le_iff_le_comap.mp hFP)
  have he' := congrArg (map (alternatingGroup (Fin 5)).subtype) he
  rw [subgroupOf_map_subtype] at he'
  exact sylow_positioned_normalizer P J (le_sup_right.trans hP) (he' ▸ hn) ho

end CFSG.Quasithin.Chapter15.Section01.ConstrainedFiveAction
