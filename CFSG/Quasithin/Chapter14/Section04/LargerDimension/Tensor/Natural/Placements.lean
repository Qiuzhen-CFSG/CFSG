module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Placements.Transport
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Placements.LocalProducts
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Placements.PointStabilizers
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Placements.ModelMarks

/-!
# Applying the marked Borel placement to the natural tensor branch

The actual image Sylow and the image of O²(B) generate C₂ × A₄ in the
alternating actor. Adding the first three-core gives S₃ × S₄ in the
symmetric actor. Both identifications begin with the original actor
isomorphism and the image of the literal Borel, and the whole overlap
quotient keeps the quotient-map formula of `overlapQuotientEquiv_mk`.

Source: Aschbacher–Smith, Lemma 14.4.10(5), printed pp.1010–1011.
The placements require only the actual Sylow subgroup and a genuine actor
equivalence. The marked image identities are available for the independent
natural-coordinate construction. The local S₃ quotient from 14.4.8 remains
explicit until the natural-module owner proves X₂ ∈ Y.
-/

public section
open Subgroup Theory.SpecificGroups.TensorThreeFive
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Placements
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)
variable {G : Type*} [Group G] [Finite G] {H T : Subgroup G}

/-- A genuine A₄ image makes O²(B) and B have exactly the same star image. -/
theorem star_second_eq_borel (eB : star H (borel H T) ≃* A4) :
    star H (second H T) = star H (borel H T) := by
  rw [second, star_twoResidual (show borel H T ≤ H from
    inf_le_left.trans (map_subtype_le _))]
  exact twoResidual_eq_of_equiv_a4 _ eB

/-- The residual image at the marked point of the alternating actor. -/
theorem alternating_second_image (e : coreQuotient H ≃* S3 × A5) (i : Fin 5)
    (hB : (star H (borel H T)).map e.toMonoidHom =
      (⊥ : Subgroup S3).prod (MulAction.stabilizer A5 i)) :
    (star H (second H T)).map e.toMonoidHom =
      (⊥ : Subgroup S3).prod (MulAction.stabilizer A5 i) := by
  rw [actor_second, hB]
  exact twoResidual_eq_of_equiv_a4 _
    ((botProdEquiv _).trans (alternatingPointEquiv i))

/-- The residual image at the marked point of the symmetric actor. -/
theorem symmetric_second_image (e : coreQuotient H ≃* S3 × S5) (i : Fin 5)
    (hB : (star H (borel H T)).map e.toMonoidHom =
      (⊥ : Subgroup S3).prod (A5 ⊓ MulAction.stabilizer S5 i)) :
    (star H (second H T)).map e.toMonoidHom =
      (⊥ : Subgroup S3).prod (A5 ⊓ MulAction.stabilizer S5 i) := by
  rw [actor_second, hB]
  exact twoResidual_eq_of_equiv_a4 _ ((botProdEquiv _).trans (evenPointEquiv i))

/-- The alternating placement retains the given actor coordinates and Borel point. -/
noncomputable def alternatingPlacement_of_borel_image
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e : coreQuotient H ≃* S3 × A5) (i : Fin 5)
    (hB : (star H (borel H T)).map e.toMonoidHom =
      (⊥ : Subgroup S3).prod (MulAction.stabilizer A5 i)) :
    star H (second H T ⊔ T) ≃* C2 × A4 := by
  have hT : T ≤ H := hS ▸ map_subtype_le _
  let hex := (actor_sylow_marks S hS e).1
  let P := hex.choose
  have hP := hex.choose_spec
  let B := MulAction.stabilizer A5 i
  have hp : twoResidual ((⊥ : Subgroup S3).prod B) = (⊥ : Subgroup S3).prod B :=
    twoResidual_eq_of_equiv_a4 _ ((botProdEquiv B).trans (alternatingPointEquiv i))
  have hn : (P : Subgroup (S3 × A5)) ≤ normalizer ((⊥ : Subgroup S3).prod B : Set _) := by
    rw [hP]
    simpa only [hB] using actor_borel_normalized hT e
  have he : (star H (second H T ⊔ T)).map e.toMonoidHom =
      (⊥ : Subgroup S3).prod B ⊔ (P : Subgroup (S3 × A5)) := by
    rw [actor_second_join hT, hB, hp, hP]
  exact (e.subgroupMap _).trans ((MulEquiv.subgroupCongr he).trans
    (alternatingJoinEquiv P B
      (Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.even_stabilizer_self_normalizing i)
      (alternatingPointEquiv i) hn))

/-- The symmetric placement identifies the whole literal overlap. -/
noncomputable def symmetricPlacement_of_borel_image
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e : coreQuotient H ≃* S3 × S5) (i : Fin 5)
    (hB : (star H (borel H T)).map e.toMonoidHom =
      (⊥ : Subgroup S3).prod (A5 ⊓ MulAction.stabilizer S5 i)) :
    star H (overlap H T) ≃* S3 × S4 := by
  have hT : T ≤ H := hS ▸ map_subtype_le _
  let hex := (actor_sylow_marks S hS e).1
  let P := hex.choose
  have hP := hex.choose_spec
  let B := A5 ⊓ MulAction.stabilizer S5 i
  have hp : twoResidual ((⊥ : Subgroup S3).prod B) = (⊥ : Subgroup S3).prod B :=
    twoResidual_eq_of_equiv_a4 _ ((botProdEquiv B).trans (evenPointEquiv i))
  have hn : (P : Subgroup (S3 × S5)) ≤ normalizer ((⊥ : Subgroup S3).prod B : Set _) := by
    rw [hP]
    simpa only [hB] using actor_borel_normalized hT e
  have he : (star H (overlap H T)).map e.toMonoidHom =
      pCore 3 (S3 × S5) ⊔ (⊥ : Subgroup S3).prod B ⊔ (P : Subgroup (S3 × S5)) := by
    rw [actor_overlap hT, hB, hp, hP]
  exact (e.subgroupMap _).trans ((MulEquiv.subgroupCongr he).trans
    (symmetricJoinEquiv P B (evenPointEquiv i) (evenPointNormalizerEquiv i) hn))

/-- Apply the alternating placement to the genuine local S₃ quotient from 14.4.8. -/
theorem symmetric_five_of_borel_images
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hmodel : Nonempty (coreQuotient H ≃* S3 × S5) ∨
      Nonempty (coreQuotient H ≃* S3 × A5))
    (hB : ∀ e : coreQuotient H ≃* S3 × A5, ∃ i : Fin 5,
      (star H (borel H T)).map e.toMonoidHom =
        (⊥ : Subgroup S3).prod (MulAction.stabilizer A5 i))
    (hlocal : Nonempty (coreQuotient (second H T ⊔ T) ≃* S3)) :
    Nonempty (coreQuotient H ≃* S3 × S5) := by
  apply symmetric_five_of_local_image (hS ▸ map_subtype_le _) hmodel _ hlocal
  rintro ⟨e⟩
  obtain ⟨i, hi⟩ := hB e
  exact ⟨alternatingPlacement_of_borel_image S hS e i hi⟩

/-- Feed the marked symmetric placement to the whole overlap quotient. -/
noncomputable def overlapQuotient_of_borel_image
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e : coreQuotient H ≃* S3 × S5) (i : Fin 5)
    (hB : (star H (borel H T)).map e.toMonoidHom =
      (⊥ : Subgroup S3).prod (A5 ⊓ MulAction.stabilizer S5 i)) :
    coreQuotient (overlap H T) ≃* S3 × S3 :=
  overlapQuotientEquiv (hS ▸ map_subtype_le _)
    (symmetricPlacement_of_borel_image S hS e i hB)

/-- The final quotient evaluates through the original star homomorphism. -/
theorem overlapQuotient_of_borel_image_mk
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e : coreQuotient H ≃* S3 × S5) (i : Fin 5)
    (hB : (star H (borel H T)).map e.toMonoidHom =
      (⊥ : Subgroup S3).prod (A5 ⊓ MulAction.stabilizer S5 i)) (x : overlap H T) :
    overlapQuotient_of_borel_image S hS e i hB (QuotientGroup.mk' _ x) =
      overlapMap (symmetricPlacement_of_borel_image S hS e i hB
        (starHom (overlap_le (hS ▸ map_subtype_le _)) x)) :=
  overlapQuotientEquiv_mk _ _ x

/-- All alternating actor marks use one quotient map and one Borel point. -/
theorem alternating_marked_images
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e : coreQuotient H ≃* S3 × A5) :
    ∃ P : Sylow 2 (S3 × A5), ∃ i : Fin 5,
      (P : Subgroup (S3 × A5)) = (star H T).map e.toMonoidHom ∧
      (star H (component H)).map e.toMonoidHom = (⊥ : Subgroup S3).prod (⊤ : Subgroup A5) ∧
      (star H (T ⊓ component H)).map e.toMonoidHom =
        (P : Subgroup (S3 × A5)) ⊓ (⊥ : Subgroup S3).prod (⊤ : Subgroup A5) ∧
      (star H (borel H T)).map e.toMonoidHom =
        (⊥ : Subgroup S3).prod (MulAction.stabilizer A5 i) ∧
      (star H (second H T)).map e.toMonoidHom =
        (⊥ : Subgroup S3).prod (MulAction.stabilizer A5 i) := by
  obtain ⟨⟨P, hP⟩, hI, _⟩ := actor_sylow_marks S hS e
  obtain ⟨i, hi⟩ := alternating_borel_image S hS e
  refine ⟨P,i,hP,alternating_component_image e,?_,hi,alternating_second_image e i hi⟩
  rw [hI, alternating_residual, hP]

/-- All symmetric actor marks use one quotient map and one Borel point. -/
theorem symmetric_marked_images
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e : coreQuotient H ≃* S3 × S5) :
    ∃ P : Sylow 2 (S3 × S5), ∃ i : Fin 5,
      (P : Subgroup (S3 × S5)) = (star H T).map e.toMonoidHom ∧
      (star H (component H)).map e.toMonoidHom = (⊥ : Subgroup S3).prod A5 ∧
      (star H (T ⊓ component H)).map e.toMonoidHom =
        (P : Subgroup (S3 × S5)) ⊓ (⊥ : Subgroup S3).prod A5 ∧
      (star H (borel H T)).map e.toMonoidHom =
        (⊥ : Subgroup S3).prod (A5 ⊓ MulAction.stabilizer S5 i) ∧
      (star H (second H T)).map e.toMonoidHom =
        (⊥ : Subgroup S3).prod (A5 ⊓ MulAction.stabilizer S5 i) := by
  obtain ⟨⟨P, hP⟩, hI, _⟩ := actor_sylow_marks S hS e
  obtain ⟨i, hi⟩ := symmetric_borel_image S hS e
  refine ⟨P,i,hP,symmetric_component_image e,?_,hi,symmetric_second_image e i hi⟩
  rw [hI, symmetric_residual, hP]

/-- The alternating local placement from only the actual Sylow and actor equivalence. -/
noncomputable def alternatingPlacement
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e : coreQuotient H ≃* S3 × A5) : star H (second H T ⊔ T) ≃* C2 × A4 :=
  alternatingPlacement_of_borel_image S hS e (alternating_borel_image S hS e).choose
    (alternating_borel_image S hS e).choose_spec

/-- The symmetric whole-overlap placement from only the actual Sylow and actor equivalence. -/
noncomputable def symmetricPlacement
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e : coreQuotient H ≃* S3 × S5) : star H (overlap H T) ≃* S3 × S4 :=
  symmetricPlacement_of_borel_image S hS e (symmetric_borel_image S hS e).choose
    (symmetric_borel_image S hS e).choose_spec

/-- The actual 14.4.8 local quotient excludes the alternating actor.
The natural-module owner supplies this local quotient after proving X₂ ∈ Y. -/
theorem symmetric_five_of_sylow
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hmodel : Nonempty (coreQuotient H ≃* S3 × S5) ∨
      Nonempty (coreQuotient H ≃* S3 × A5))
    (hlocal : Nonempty (coreQuotient (second H T ⊔ T) ≃* S3)) :
    Nonempty (coreQuotient H ≃* S3 × S5) :=
  symmetric_five_of_borel_images S hS hmodel (alternating_borel_image S hS) hlocal

/-- The whole overlap quotient in the surviving actor, with no placement premise. -/
noncomputable def overlapQuotient
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e : coreQuotient H ≃* S3 × S5) : coreQuotient (overlap H T) ≃* S3 × S3 :=
  overlapQuotientEquiv (hS ▸ map_subtype_le _) (symmetricPlacement S hS e)

/-- The unconditional overlap equivalence retains the literal star quotient map. -/
theorem overlapQuotient_mk
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e : coreQuotient H ≃* S3 × S5) (x : overlap H T) :
    overlapQuotient S hS e (QuotientGroup.mk' _ x) =
      overlapMap (symmetricPlacement S hS e (starHom (overlap_le (hS ▸ map_subtype_le _)) x)) :=
  overlapQuotientEquiv_mk _ _ x

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Placements
