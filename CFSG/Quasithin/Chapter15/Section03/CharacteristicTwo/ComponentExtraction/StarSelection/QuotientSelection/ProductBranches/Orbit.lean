module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.QuotientSelection.ProductBranches.Factors

public import Theory.GroupTheory.CComponent.QuotientLifting

public import Theory.GroupTheory.SpecificGroups.PermThreeProduct

/-!
# Normal S₃ subgroups in the two-factor alternatives

Projection kills a normal solvable subgroup in every nonsolvable source
factor. Thus a normal S₃ in a mixed product must be its S₃ coordinate;
for S₃ × S₃ use the checked normal-subgroup classification. Ambient
conjugation preserves normality inside the normal product N, so all
conjugates belong to the same coordinate pair. Orbit–stabilizer gives
index at most two for the actual ambient normalizer.

Source: Aschbacher–Smith B.5.6(3),(5), printed p.105, and the factor
selection in 15.3.15(2)/26(2), pp.1125 and 1130 (1 March 2004 manuscript).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection.ProductBranches
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {D E : Type*} [Group D] [Group E]

/-- The first coordinate subgroup with its literal projection. -/
noncomputable def firstEquiv : (⊤ : Subgroup D).prod (⊥ : Subgroup E) ≃* D where
  toFun x := x.1.1
  invFun x := ⟨(x, 1), ⟨mem_top _, rfl⟩⟩
  left_inv x := by apply Subtype.ext; exact Prod.ext rfl x.property.2.symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem s3_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]

variable [Finite D] [Finite E]
omit [Finite D] [Finite E] in
private theorem normal_solvable_projection (K : Subgroup (D × E)) [K.Normal]
    [Group.IsSolvable K]
    (hE : ∀ H : Subgroup E, H.Normal → Group.IsSolvable H → H = ⊥) :
    K.map (MonoidHom.snd D E) = ⊥ := by
  let : (K.map (MonoidHom.snd D E)).Normal :=
    (inferInstance : K.Normal).map _ Prod.snd_surjective
  let : Group.IsSolvable (K.map (MonoidHom.snd D E)) :=
    Group.isSolvable_of_surjective ((MonoidHom.snd D E).subgroupMap_surjective K)
  exact hE _ inferInstance inferInstance

private theorem normal_s3_eq_first (K : Subgroup (D × E)) [K.Normal]
    (eK : K ≃* Equiv.Perm (Fin 3)) (eD : D ≃* Equiv.Perm (Fin 3))
    (hE : ∀ H : Subgroup E, H.Normal → Group.IsSolvable H → H = ⊥) :
    K = (⊤ : Subgroup D).prod (⊥ : Subgroup E) := by
  let := s3_solvable
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (f := eK.toMonoidHom) eK.injective
  apply eq_of_le_of_card_ge
    (le_prod_iff.mpr ⟨le_top, (normal_solvable_projection K hE).le⟩)
  exact (Nat.card_congr ((firstEquiv (D := D) (E := E)).trans eD).toEquiv).trans
    (Nat.card_congr eK.toEquiv).symm |>.le

/-- Normal S₃ subgroups in a product of source factors are coordinate factors,
including when one or both factors are nonsolvable. -/
theorem normal_s3_eq_coordinate (hD : FactorModel D) (hE : FactorModel E)
    (K : Subgroup (D × E)) [K.Normal] (eK : K ≃* Equiv.Perm (Fin 3)) :
    K = (⊤ : Subgroup D).prod (⊥ : Subgroup E) ∨
      K = (⊥ : Subgroup D).prod (⊤ : Subgroup E) := by
  rcases factor_structure hD with hd | ⟨_, _, hd⟩
  · obtain ⟨eD⟩ := hd
    rcases factor_structure hE with he | ⟨_, _, he⟩
    · obtain ⟨eE⟩ := he
      let e := eD.prodCongr eE
      let K' := K.map e.toMonoidHom
      let : K'.Normal := (inferInstance : K.Normal).map _ e.surjective
      let eK' := (K.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eK
      have hl : ((⊤ : Subgroup D).prod (⊥ : Subgroup E)).map e.toMonoidHom =
          (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥ := by
        ext x
        rw [mem_map_equiv]
        change (True ∧ eE.symm x.2 = 1) ↔ (True ∧ x.2 = 1)
        simp
      have hr : ((⊥ : Subgroup D).prod (⊤ : Subgroup E)).map e.toMonoidHom =
          (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod ⊤ := by
        ext x
        rw [mem_map_equiv]
        change (eD.symm x.1 = 1 ∧ True) ↔ (x.1 = 1 ∧ True)
        simp
      exact (PermThreeProduct.normal_subgroup_eq_factor K' eK').imp
        (fun h => map_injective e.injective (h.trans hl.symm))
        (fun h => map_injective e.injective (h.trans hr.symm))
    · exact Or.inl (normal_s3_eq_first K eK eD he)
  · rcases factor_structure hE with he | ⟨_, _, he⟩
    · obtain ⟨eE⟩ := he
      let s : D × E ≃* E × D := MulEquiv.prodComm
      let : (K.map s.toMonoidHom).Normal := (inferInstance : K.Normal).map _ s.surjective
      have h := normal_s3_eq_first (K.map s.toMonoidHom)
        ((K.equivMapOfInjective s.toMonoidHom s.injective).symm.trans eK) eE hd
      right
      ext x
      have hx := SetLike.ext_iff.mp h (s x)
      simpa [mem_map_equiv, s, mem_prod, and_comm] using hx
    · let := s3_solvable
      let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
        (f := eK.toMonoidHom) eK.injective
      have hfst : K.map (MonoidHom.fst D E) = ⊥ := by
        let : (K.map (MonoidHom.fst D E)).Normal :=
          (inferInstance : K.Normal).map _ Prod.fst_surjective
        let : Group.IsSolvable (K.map (MonoidHom.fst D E)) :=
          Group.isSolvable_of_surjective ((MonoidHom.fst D E).subgroupMap_surjective K)
        exact hd _ inferInstance inferInstance
      have hb : K = ⊥ := by
        apply le_bot_iff.mp
        simpa only [bot_prod_bot] using
          (le_prod_iff.mpr ⟨hfst.le, (normal_solvable_projection K he).le⟩)
      have hc := Nat.card_congr eK.toEquiv
      norm_num [hb, Nat.card_eq_fintype_card, Fintype.card_perm] at hc

variable {A : Type*} [Group A] [Finite A]

/-- Normality of N transports every ambient conjugate back to a normal S₃
inside the same product. Hence the ambient normalizer has index at most two. -/
theorem normal_s3_normalizer_index (N : Subgroup A) [N.Normal]
    (e : N ≃* D × E) (hD : FactorModel D) (hE : FactorModel E)
    (K : Subgroup N) [K.Normal] (eK : K ≃* Equiv.Perm (Fin 3)) :
    (normalizer (K.map N.subtype : Set A)).index ≤ 2 := by
  let L := ((⊤ : Subgroup D).prod (⊥ : Subgroup E)).map e.symm.toMonoidHom
  let R := ((⊥ : Subgroup D).prod (⊤ : Subgroup E)).map e.symm.toMonoidHom
  have hall (B : Subgroup N) [B.Normal] (eB : B ≃* Equiv.Perm (Fin 3)) :
      B = L ∨ B = R := by
    let : (B.map e.toMonoidHom).Normal := (inferInstance : B.Normal).map _ e.surjective
    have h := normal_s3_eq_coordinate hD hE (B.map e.toMonoidHom)
      ((B.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eB)
    exact h.imp
      (fun h => by simpa [map_map, L] using congrArg (map e.symm.toMonoidHom) h)
      (fun h => by simpa [map_map, R] using congrArg (map e.symm.toMonoidHom) h)
  rw [← ncard_conjugates_eq_index_normalizer]
  have hs : (Set.range fun a : A => (K.map N.subtype).map (MulAut.conj a).toMonoidHom) ⊆
      {L.map N.subtype, R.map N.subtype} := by
    rintro _ ⟨a, rfl⟩
    let α : MulAut N := MulAut.conjNormal a
    let : (K.map α.toMonoidHom).Normal := (inferInstance : K.Normal).map _ α.surjective
    have hm := hall (K.map α.toMonoidHom)
      ((K.equivMapOfInjective α.toMonoidHom α.injective).symm.trans eK)
    have he : (K.map N.subtype).map (MulAut.conj a).toMonoidHom =
        (K.map α.toMonoidHom).map N.subtype := by rw [map_map, map_map]; rfl
    change (K.map N.subtype).map (MulAut.conj a).toMonoidHom ∈
      ({L.map N.subtype, R.map N.subtype} : Set (Subgroup A))
    rw [he]
    exact hm.imp (congrArg (map N.subtype)) (congrArg (map N.subtype))
  calc
    _ ≤ ({L.map N.subtype, R.map N.subtype} : Set (Subgroup A)).ncard := Set.ncard_le_ncard hs
    _ ≤ 2 := by simpa only [Set.ncard_singleton] using
      Set.ncard_insert_le (L.map N.subtype) {R.map N.subtype}

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection.ProductBranches
