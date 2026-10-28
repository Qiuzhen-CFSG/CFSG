module
public import Theory.GroupTheory.SylowPreimageNormalizer
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Sylow intersections lifted from a surjective image

Suppose a prescribed Sylow subgroup meets a subgroup of the image in a
Sylow subgroup of that image subgroup. Its original intersection with
the full preimage is then Sylow in that preimage. No restriction on the
kernel is needed: normality makes the original kernel intersection Sylow,
and relative-index multiplication combines it with the image index.

This transports the marked vector stabilizer in Aschbacher--Smith,
original 15.1.16--17, printed pp.1091--1092.
-/

public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D]

/-- The literal intersection of the prescribed Sylow with the full preimage
is Sylow whenever its image intersection is Sylow. -/
theorem exists_sylow_preimage_inf_of_image
    {p : ℕ} [Fact p.Prime] (T : Sylow p G)
    (f : G →* D) (hf : Function.Surjective f) (B : Subgroup D)
    (P : Sylow p B)
    (hP : (P : Subgroup B).map B.subtype = (T : Subgroup G).map f ⊓ B) :
    ∃ S : Sylow p (B.comap f),
      (S : Subgroup (B.comap f)).map (B.comap f).subtype =
        (T : Subgroup G) ⊓ B.comap f := by
  let : Finite D := Finite.of_surjective f hf
  let R := (T : Subgroup G) ⊓ B.comap f
  have hRm : R.map f = (T : Subgroup G).map f ⊓ B := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨mem_map_of_mem f hy.1,hy.2⟩
    · rintro ⟨⟨y,hy,rfl⟩,hb⟩
      exact ⟨y,⟨hy,hb⟩,rfl⟩
  have hRk : R ⊓ f.ker = (T : Subgroup G) ⊓ f.ker := by
    apply le_antisymm (inf_le_inf_right _ inf_le_left)
    intro x hx
    refine ⟨⟨hx.1,?_⟩,hx.2⟩
    change f x ∈ B
    rw [MonoidHom.mem_ker.mp hx.2]
    exact B.one_mem
  obtain ⟨Q,hQ⟩ := T.exists_sylow_map_eq_inf_of_normal f.ker
  obtain ⟨S,hS⟩ := exists_sylow_preimage_of_kernel_intersection R
    (T.isPGroup'.to_le inf_le_left) f Q (hQ.trans hRk.symm)
  have hidx₁ : ¬ p ∣ R.relIndex ((R.map f).comap f) := by
    change ¬ p ∣ (R.subgroupOf ((R.map f).comap f)).index
    rw [←hS]
    exact S.not_dvd_index
  have hidx₂ : ¬ p ∣ ((R.map f).comap f).relIndex (B.comap f) := by
    rw [relIndex_comap, map_comap_eq_self_of_surjective hf, ←hP.trans hRm.symm]
    have he := relIndex_map_map_of_injective (P : Subgroup B) ⊤ B.subtype_injective
    rw [←MonoidHom.range_eq_map, B.range_subtype, relIndex_top_right] at he
    rw [he]
    exact P.not_dvd_index
  have hidx : ¬ p ∣ R.relIndex (B.comap f) := by
    rw [←relIndex_mul_relIndex R ((R.map f).comap f) (B.comap f)
      (le_comap_map f R) (comap_mono (hRm ▸ inf_le_right))]
    exact fun h => (Fact.out : p.Prime).dvd_mul.mp h |>.elim hidx₁ hidx₂
  refine ⟨((T.isPGroup'.to_le inf_le_left).comap_subtype
    : IsPGroup p (R.subgroupOf (B.comap f))).toSylow hidx,?_⟩
  exact map_subgroupOf_eq_of_le inf_le_right

end Subgroup
