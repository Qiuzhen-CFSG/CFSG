module

public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Relative normal Sylows and quotient Borel displacements

If a Sylow subgroup S normalizes L, its intersection with L is Sylow
in L: apply the normal-subgroup intersection theorem inside LS.
Suppose S is normal in S N_L(S ∩ L). Conjugating an element of S by
an element of this local normalizer keeps it in S, so its displacement
on L lies in S ∩ L.

For any equivariant surjection from L, the image of S ∩ L is Sylow
and its normalizer is the image of N_L(S ∩ L). The same displacement
bound therefore holds in the quotient, with the original action.
No normality of L in the full ambient group is required.

Source application: Aschbacher--Smith F.1.12, printed p.264
(PDF p.275), the implication from S normal in SBⱼ.
-/

public section

open Subgroup
namespace Subgroup.NormalSylowQuotientAction
variable {G H : Type*} [Group G] [Group H] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- A normalized local subgroup inherits the ambient Sylow by intersection. -/
theorem intersection_sylow (S : Sylow p G) (L : Subgroup G)
    (hSL : (S : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ P : Sylow p L, (P : Subgroup L) = (S : Subgroup G).subgroupOf L := by
  let W := L ⊔ (S : Subgroup G)
  have hLW : L ≤ W := le_sup_left
  let _ : (L.subgroupOf W).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLW).mpr (sup_le L.le_normalizer hSL)
  obtain ⟨P, hP⟩ := (S.subtype (show (S : Subgroup G) ≤ W from le_sup_right)).exists_subgroupOf_eq_of_normal (L.subgroupOf W)
  let e := subgroupOfEquivOfLe hLW
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (P : Subgroup _).map e.toMonoidHom = _
  rw [hP]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x, hLW x.property⟩, x.property⟩, hx, rfl⟩

omit [Finite G] in
private theorem action_preserves_intersection (L A : Subgroup G)
    (s : normalizer (L : Set G)) (hs : (s : G) ∈ A) :
    (A.subgroupOf L).map (L.normalizerMonoidHom s).toMonoidHom = A.subgroupOf L := by
  have hf (u : normalizer (L : Set G)) (hu : (u : G) ∈ A) {x : L}
      (hx : x ∈ A.subgroupOf L) : L.normalizerMonoidHom u x ∈ A.subgroupOf L := by
    change (L.normalizerMonoidHom u x : G) ∈ A
    rw [normalizerMonoidHom_apply_apply_coe]
    exact A.mul_mem (A.mul_mem hu hx) (A.inv_mem hu)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hf s hs hy
  · intro hx
    refine ⟨L.normalizerMonoidHom s⁻¹ x, hf s⁻¹ (A.inv_mem hs) hx, ?_⟩
    rw [map_inv L.normalizerMonoidHom s]
    exact (L.normalizerMonoidHom s).apply_symm_apply x

omit [Finite G] in
private theorem displacement (S L : Subgroup G)
    (hSL : S ≤ normalizer (L : Set G))
    (hn : (S.subgroupOf (S ⊔ (normalizer (S.subgroupOf L : Set L)).map L.subtype)).Normal)
    (s : S) (x : L) (hx : x ∈ normalizer (S.subgroupOf L : Set L)) :
    x⁻¹ * L.normalizerMonoidHom ⟨s, hSL s.property⟩ x ∈ S.subgroupOf L := by
  let B := (normalizer (S.subgroupOf L : Set L)).map L.subtype
  have hBS : B ≤ normalizer (S : Set G) :=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer (show S ≤ S ⊔ B from le_sup_left)).mp hn)
  have hxB : (x : G) ∈ B := mem_map_of_mem L.subtype hx
  have hc : (x : G)⁻¹ * (s : G) * x ∈ S := by
    exact (mem_normalizer_iff''.mp (hBS hxB) s).mp s.property
  change (x⁻¹ * L.normalizerMonoidHom ⟨s, hSL s.property⟩ x : L).val ∈ S
  rw [Subgroup.coe_mul, Subgroup.coe_inv, normalizerMonoidHom_apply_apply_coe]
  simpa only [mul_assoc] using S.mul_mem hc (S.inv_mem s.property)

/-- Relative normality controls every displacement in the actual quotient normalizer. -/
theorem quotient_displacements (S : Sylow p G) (L : Subgroup G)
    (hSL : (S : Subgroup G) ≤ normalizer (L : Set G))
    (hn : ((S : Subgroup G).subgroupOf ((S : Subgroup G) ⊔
      (normalizer ((S : Subgroup G).subgroupOf L : Set L)).map L.subtype)).Normal)
    (f : L →* H) (hf : Function.Surjective f)
    (a : S → MulAut H)
    (ha : ∀ (s : S) (x : L), a s (f x) =
      f (L.normalizerMonoidHom ⟨s, hSL s.property⟩ x)) :
    ∃ P : Sylow p H,
      (P : Subgroup H) = ((S : Subgroup G).subgroupOf L).map f ∧
      ∀ s : S, (P : Subgroup H).map (a s).toMonoidHom = P ∧
        ∀ x ∈ normalizer (P : Set H), x⁻¹ * a s x ∈ (P : Subgroup H) := by
  obtain ⟨R, hR⟩ := intersection_sylow S L hSL
  refine ⟨R.mapSurjective hf, ?_, ?_⟩
  · change (R : Subgroup L).map f = _
    rw [hR]
  · intro s
    have he : (a s).toMonoidHom.comp f =
        f.comp (L.normalizerMonoidHom ⟨s, hSL s.property⟩).toMonoidHom := by
      ext x
      exact ha s x
    constructor
    · change ((R : Subgroup L).map f).map (a s).toMonoidHom = (R : Subgroup L).map f
      rw [hR, Subgroup.map_map, he, ← Subgroup.map_map,
        action_preserves_intersection L (S : Subgroup G) _ s.property]
    · intro x hx
      change x ∈ normalizer ((R : Subgroup L).map f : Set H) at hx
      rw [← R.normalizer_map_surjective f hf] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      change (f y)⁻¹ * a s (f y) ∈ (R : Subgroup L).map f
      rw [ha, ← map_inv, ← map_mul]
      apply mem_map_of_mem
      rw [hR]
      change y ∈ normalizer ((R : Subgroup L) : Set L) at hy
      rw [hR] at hy
      exact displacement (S : Subgroup G) L hSL hn s y hy
end Subgroup.NormalSylowQuotientAction
