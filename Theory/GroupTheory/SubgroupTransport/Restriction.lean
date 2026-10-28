module
public import Theory.GroupTheory.SubgroupTransport
public import Theory.Frattini.Intersection

/-!
# Restricting an isomorphism of ambient subgroups

The literal image construction for an isomorphism S≃T has an explicit
restriction R≃image(R). It preserves joins of subgroups inside S, has an
inverse on such subgroups, transports normalization, and preserves the
embedded Frattini subgroup. No ambient automorphism extension is required.

These identities supply the recursive pair and the Frattini comparison in
Niles, *Pushing-up in finite groups* (1979), Proposition4.4, printedpp45–46.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SubgroupTransport
variable {G H : Type*} [Group G] [Group H] {S : Subgroup G} {T : Subgroup H}

/-- Restrict an overgroup isomorphism to an actual ambient subgroup. -/
@[expose] noncomputable def imageEquiv (φ : S ≃* T) (R : Subgroup G) (hRS : R ≤ S) :
    R ≃* image φ R :=
  (subgroupOfEquivOfLe hRS).symm.trans
    ((R.subgroupOf S).equivMapOfInjective (ambientHom φ) (ambientHom_injective φ))

theorem imageEquiv_apply (φ : S ≃* T) (R : Subgroup G) (hRS : R ≤ S) (x : R) :
    (imageEquiv φ R hRS x : H) = (φ ⟨x,hRS x.property⟩ : H) := rfl

theorem image_mono (φ : S ≃* T) {R Q : Subgroup G} (hRQ : R ≤ Q) :
    image φ R ≤ image φ Q := map_mono (comap_mono hRQ)

theorem image_symm (φ : S ≃* T) (R : Subgroup G) (hRS : R ≤ S) :
    image φ.symm (image φ R) = R := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact (mem_image_iff φ R (φ.symm y)).mp (by simpa only [φ.apply_symm_apply] using (show (y : H) ∈ image φ R from hy))
  · intro x hx
    let z : S := ⟨x,hRS hx⟩
    refine ⟨φ z,(mem_image_iff φ R z).mpr hx,?_⟩
    exact congrArg Subtype.val (φ.symm_apply_apply z)

theorem image_self (φ : S ≃* T) : image φ S = T := by
  apply le_antisymm (image_le φ S)
  intro x hx
  refine ⟨φ.symm ⟨x,hx⟩,(φ.symm ⟨x,hx⟩).property,?_⟩
  exact congrArg Subtype.val (φ.apply_symm_apply ⟨x,hx⟩)

theorem image_sup (φ : S ≃* T) (R Q : Subgroup G) (hRS : R ≤ S) (hQS : Q ≤ S) :
    image φ (R ⊔ Q) = image φ R ⊔ image φ Q := by
  rw [image,subgroupOf_sup hRS hQS,Subgroup.map_sup]
  rfl

theorem normalizes_image (φ : S ≃* T) (R : Subgroup G) (hRS : R ≤ S)
    (hn : S ≤ normalizer (R : Set G)) : T ≤ normalizer (image φ R : Set H) := by
  intro x hx
  have h := (normalizes_iff φ R hRS (φ.symm ⟨x,hx⟩)).mp
    (hn (φ.symm ⟨x,hx⟩).property)
  simpa only [φ.apply_symm_apply] using h

/-- Restriction transports the embedded Frattini subgroup through the
literal ambient homomorphism. -/
theorem image_frattini (φ : S ≃* T) (R : Subgroup G) (hRS : R ≤ S) :
    image φ ((frattini R).map R.subtype) =
      (frattini (image φ R)).map (image φ R).subtype := by
  have he : (R.subgroupOf S).map S.subtype = R := map_subgroupOf_eq_of_le hRS
  have hp := frattini_image_map (R.subgroupOf S) S.subtype S.subtype_injective
  rw [he] at hp
  have hc : ((frattini R).map R.subtype).subgroupOf S =
      (frattini (R.subgroupOf S)).map (R.subgroupOf S).subtype := by
    rw [hp]
    exact comap_map_eq_self_of_injective S.subtype_injective _
  rw [image,hc,←frattini_image_map _ _ (ambientHom_injective φ)]
  rfl
end Theory.GroupTheory.SubgroupTransport
