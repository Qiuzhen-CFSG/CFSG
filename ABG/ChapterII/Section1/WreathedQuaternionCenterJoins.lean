module
public import ABG.ChapterII.Section1.WreathedQuaternionCore
public import ABG.ChapterII.Section1.WreathedQuaternionConjugacy
public import Stellmacher.LaterDefs

/-!
# Central-product models from arbitrary quaternion subgroups

For any actual quaternion subgroup Q of order eight in a chosen wreathed
presentation, Q and the ambient center generate a central product with shared
intersection of order two. This gives the existing central-product vocabulary
for the quaternion-join case of ABG Chapter II §1 Lemma 3(i), article p.10.
Both model factors are the original subgroup types, in the same universe.

Every quaternion subgroup is conjugate to the chosen quaternion core.
Conjugation preserves the ambient center, so it transports their intersection
and its cardinality. The join then has the two factors as reflexive model
witnesses: they commute because one is central, and their shared intersection
lies in the center of the join through its actual subtype map.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

include P in
public theorem quaternion_inf_center_card (Q : Subgroup S) (hQ : ABG.IsQuaternionGroup Q) :
    Nat.card (Q ⊓ Subgroup.center S : Subgroup S) = 2 := by
  obtain ⟨g, hg⟩ := P.quaternion_subgroup_conjugacy Q hQ
  let f := (MulAut.conj g).toMonoidHom
  have hZ : (Subgroup.center S).map f = Subgroup.center S :=
    Subgroup.Normal.map_conj_eq (Subgroup.center S) g
  calc
    Nat.card (Q ⊓ Subgroup.center S : Subgroup S) =
        Nat.card ((P.quaternionCore ⊓ Subgroup.center S).map f) := by
      rw [Subgroup.map_inf _ _ f (MulAut.conj g).injective, hZ]
      exact congrArg (fun H : Subgroup S => Nat.card (H ⊓ Subgroup.center S : Subgroup S)) hg.symm
    _ = Nat.card (P.quaternionCore ⊓ Subgroup.center S : Subgroup S) :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    _ = 2 := P.quaternion_core_structure.2.2

include P in
public theorem quaternion_center_join_model (Q : Subgroup S) (hQ : ABG.IsQuaternionGroup Q) :
    Stellmacher.Later.IsCentralProductModel (Q ⊔ Subgroup.center S) Q (Subgroup.center S) := by
  refine ⟨Q, Subgroup.center S, ⟨MulEquiv.refl _⟩, ⟨MulEquiv.refl _⟩,
    rfl, P.quaternion_inf_center_card Q hQ, ?_, ?_⟩
  · intro b hb c hc
    exact Subgroup.mem_center_iff.mp hc b
  · intro a ha
    have haJ : a ∈ Q ⊔ Subgroup.center S := (show Q ≤ Q ⊔ Subgroup.center S from le_sup_left) ha.1
    refine ⟨⟨a, haJ⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro b
    exact Subtype.ext (Subgroup.mem_center_iff.mp ha.2 (b : S))

end ABG.Wreathed.Presentation
