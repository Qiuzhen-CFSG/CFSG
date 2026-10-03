module
public import ABG.ChapterII.Section1.WreathedCentralProductModel
public import ABG.ChapterII.Section1.WreathedQuaternionConjugacy

/-!
# Conjugacy of copies of the canonical quaternion central product

Every actual subgroup `X` isomorphic to the chosen central product `V` is
conjugate to `V` in the wreathed group. This is the central-product case of
ABG Chapter II §1 Lemma 3(iii), article p.10. No centricity or automorphism
hypothesis on `X` is required; the chosen presentation retains its exact
height and group-order assumptions.

An isomorphism transports the quaternion core into `X`. The center of `X`
has the same order as the ambient center: `V_center` identifies the model
center, and Lemma 2(xii) embeds the center of the nonabelian `X` in the ambient
center. Equal orders identify these centers. Quaternion subgroup conjugacy
then identifies the join of the transported core and the ambient center with
a conjugate of `V`. This join lies in `X` and has the same order as `X`, hence
is `X`. The second theorem retains the actual quaternion subgroup and join
for the later fusion-frame construction.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem center_of_V_iso (X : Subgroup S) (e : X ≃* P.V) :
    (Subgroup.center X).map X.subtype = Subgroup.center S := by
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  have hn : ¬ IsMulCommutative X := by
    intro h
    apply P.V_noncommutative
    apply IsMulCommutative.of_comm
    intro a b
    simpa only [map_mul, MulEquiv.apply_symm_apply] using
      congrArg e (h.is_comm.comm (e.symm a) (e.symm b))
  apply Subgroup.eq_of_le_of_card_ge (P.nonabelian_center_le X hn)
  rw [Subgroup.card_map_of_injective X.subtype_injective,
    Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  rw [← P.V_center, Subgroup.card_map_of_injective P.V.subtype_injective]

public theorem V_isomorphic_conjugate (X : Subgroup S)
    (hX : Nonempty (X ≃* P.V)) :
    ∃ g : S, P.V.map (MulAut.conj g).toMonoidHom = X := by
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  obtain ⟨e⟩ := hX
  have hC : Subgroup.center S ≤ X := by
    rw [← P.center_of_V_iso X e]
    rintro a ⟨b, hb, rfl⟩
    exact b.property
  let i : P.quaternionCore →* P.V := Subgroup.inclusion (show P.quaternionCore ≤ P.V from le_sup_left)
  let f : P.quaternionCore →* S := X.subtype.comp (e.symm.toMonoidHom.comp i)
  have hf : Function.Injective f := X.subtype_injective.comp
    (e.symm.injective.comp (Subgroup.inclusion_injective le_sup_left))
  let Q : Subgroup S := f.range
  let eQ : P.quaternionCore ≃* Q := MonoidHom.ofInjective hf
  have hQ : ABG.IsQuaternionGroup Q := by
    obtain ⟨ec⟩ := P.quaternion_core_model.1
    exact ⟨eQ.symm.trans ec⟩
  obtain ⟨g, hg⟩ := P.quaternion_subgroup_conjugacy Q hQ
  refine ⟨g, ?_⟩
  have hmap : P.V.map (MulAut.conj g).toMonoidHom = Q ⊔ Subgroup.center S := by
    rw [V, Subgroup.map_sup, hg,
      Subgroup.characteristic_iff_map_eq.mp (inferInstance : (Subgroup.center S).Characteristic)]
  apply Subgroup.eq_of_le_of_card_ge
  · rw [hmap]
    refine sup_le ?_ hC
    rintro q ⟨a, rfl⟩
    exact (e.symm (i a)).property
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact (Nat.card_congr e.toEquiv).le

public theorem V_isomorphic_quaternion_join (X : Subgroup S)
    (hX : Nonempty (X ≃* P.V)) :
    ∃ Q : Subgroup S, ABG.IsQuaternionGroup Q ∧ X = Q ⊔ Subgroup.center S := by
  obtain ⟨g, hg⟩ := P.V_isomorphic_conjugate X hX
  refine ⟨P.quaternionCore.map (MulAut.conj g).toMonoidHom, ?_, ?_⟩
  · obtain ⟨e⟩ := P.quaternion_core_model.1
    exact ⟨((MulAut.conj g).subgroupMap P.quaternionCore).symm.trans e⟩
  · rw [← hg, V, Subgroup.map_sup,
      Subgroup.characteristic_iff_map_eq.mp (inferInstance : (Subgroup.center S).Characteristic)]

end ABG.Wreathed.Presentation
