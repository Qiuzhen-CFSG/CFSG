module
public import Theory.SpecificGroups.AlternatingFiveBorelProjection
public import Theory.SpecificGroups.AlternatingFiveSolvableSylow
public import Theory.GroupTheory.PCoreImage
/-!
# The two-core of a proper Sylow-normalized subgroup above A₅

Map the actual Sylow subgroup to the standard Klein four in A₅. A proper
overgroup lies in its A₄ normalizer, so a nontrivial two-perfect invariant
subgroup is the whole A₄. The Klein four is therefore in its two-core.
Lifting the core through the actual map restores the original two-kernel.

Source: Aschbacher–Smith, the Sylow placement in 15.3.18–19, pp.1126–1127.
The application to the selected component uses O₂(L)O₂(Y_L)≤R from15.3.12.
-/
public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups
variable {L : Type*} [Group L] [Finite L]

/-- A nontrivial two-perfect subgroup normalized by a Sylow subgroup has
that Sylow subgroup in its two-core, modulo the ambient two-core, when their
join is proper and the ambient two-core quotient is A₅. -/
theorem alternatingFive_sylow_le_core_join
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (P : Sylow 2 L)
    (A : Subgroup L) (hne : A ≠ ⊥) (hp : IsPPerfect 2 A)
    (hn : (P : Subgroup L) ≤ normalizer (A : Set L))
    (hproper : A ⊔ (P : Subgroup L) ≠ ⊤) :
    (P : Subgroup L) ≤ pCore 2 L ⊔ A.pCoreIn 2 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective (f := q) hq
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) Q AlternatingFiveProjection.sylow
  let f := (MulAut.conj g).toMonoidHom.comp q
  have hk : f.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective,
      MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hP : (P : Subgroup L).map f = AlternatingFiveProjection.P := by
    change (P : Subgroup L).map ((MulAut.conj g).toMonoidHom.comp q) = _
    rw [←map_map]
    change (g • Q).toSubgroup = AlternatingFiveProjection.P
    rw [hg]
    rfl
  let D := A.map f
  let J := (A ⊔ (P : Subgroup L)).map f
  have hJ : J ≠ ⊤ := by
    intro ht
    have hh := comap_map_eq_self
      (show f.ker ≤ A ⊔ (P : Subgroup L) from hk ▸
        (pCore_isPGroup.le_sylow_of_normal P).trans le_sup_right)
    change J.comap f = _ at hh
    rw [ht,comap_top] at hh
    exact hproper hh.symm
  have hPJ : AlternatingFiveProjection.P ≤ J := hP ▸ map_mono le_sup_right
  have hJB : J ≤ BinaryPermutation.AlternatingFiveBorel.B := by
    have hh := alternatingGroup.proper_sylow_overgroup_le_normalizer
      AlternatingFiveProjection.sylow J hJ hPJ
    exact hh.trans_eq AlternatingFiveProjection.normalizer_P
  have hDB : D ≤ BinaryPermutation.AlternatingFiveBorel.B := (map_mono le_sup_left).trans hJB
  have hD : D ≠ ⊥ := by
    intro hD
    have hAk : A ≤ f.ker := (Subgroup.map_eq_bot_iff A).mp hD
    have hA2 : IsPGroup 2 A := (hk ▸ pCore_isPGroup).to_le hAk
    have hid := hp.hom_eq_one_of_isPGroup hA2 (MonoidHom.id A)
    apply hne
    apply eq_bot_iff.mpr
    intro a ha
    exact congrArg Subtype.val (DFunLike.congr_fun hid ⟨a,ha⟩)
  have hD5 : ∀ d ∈ D, d^5=1 → d=1 := by
    have hc : Nat.card BinaryPermutation.AlternatingFiveBorel.B = 12 :=
      (Nat.card_congr BinaryPermutation.AlternatingFiveBorel.marking.toEquiv.symm).trans
        (alternatingGroup.card_of_card_eq_four (by simp))
    have hd : Nat.card D ∣ 12 := hc ▸ card_dvd_of_le hDB
    have hcop : Nat.Coprime (Nat.card D) 5 := Nat.Coprime.of_dvd_left hd (by decide)
    intro d hd he
    have ht : (⟨d,hd⟩ : D) = 1 := (powCoprime hcop).injective (by
      change (⟨d,hd⟩ : D)^5=1^5
      simpa only [one_pow] using (Subtype.ext he : (⟨d,hd⟩ : D)^5=1))
    exact congrArg Subtype.val ht
  have hPD : AlternatingFiveProjection.P ≤ normalizer (D : Set _) := by
    rw [←hP]
    apply le_normalizer_iff.mpr
    rintro p ⟨p,hp,rfl⟩ a ⟨a,ha,rfl⟩
    exact ⟨p*a*p⁻¹,(hn hp a).mp ha,by simp only [map_mul,map_inv]⟩
  have hDB' : D = BinaryPermutation.AlternatingFiveBorel.B :=
    AlternatingFiveProjection.eq_borel D hD
      (hp.of_surjective (f.subgroupMap A) (f.subgroupMap_surjective A)) hD5 hPD
  have hPC : AlternatingFiveProjection.P ≤ D.pCoreIn 2 := by
    rw [hDB']
    apply le_pCoreIn_of_normalizes AlternatingFiveProjection.sylow.isPGroup'
    · rw [←AlternatingFiveProjection.normalizer_P]
      exact AlternatingFiveProjection.P.le_normalizer
    · exact AlternatingFiveProjection.normalizer_P.ge
  have hm : (P : Subgroup L).map f ≤ (A.pCoreIn 2).map f := by
    rw [hP,map_pCoreIn_of_ker_isPGroup f (hk ▸ pCore_isPGroup)]
    exact hPC
  have hh := map_le_iff_le_comap.mp hm
  rw [comap_map_eq,hk,sup_comm] at hh
  exact hh
end Theory.SpecificGroups
