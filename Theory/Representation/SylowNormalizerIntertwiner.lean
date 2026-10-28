module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.RepresentationTheory.Basic

/-!
# Aligning Sylow normalizers and module coordinates

Given two finite groups, an actual group equivalence and an equivariant linear
identification, Sylow conjugacy aligns prescribed Sylow normalizers. Acting on
the target module by the same conjugating element preserves equivariance.
The groups and modules may have different concrete carriers. Products and
pullbacks supply the normalizer witnesses used in applications.

Source application: Aschbacher–Smith, E.2.2 (pp.215–216), F.9.18(5)
(pp.325–326), and the natural-module calculation on printed p.1152.
-/

@[expose] public section

namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
  {p : ℕ} [Fact p.Prime]

/-- Sylow conjugacy adjusts an equivalence between different groups to identify the
normalizers of two specified Sylow subgroups. -/
theorem exists_inner_map_sylow_normalizer (f : G ≃* H)
    (P : Sylow p G) (Q : Sylow p H) :
    ∃ g : H, (Subgroup.normalizer (P : Set G)).map
      (f.trans (MulAut.conj g)).toMonoidHom = Subgroup.normalizer (Q : Set H) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H (P.mapSurjective (f := f.toMonoidHom) f.surjective) Q
  have he : ((P : Subgroup G).map f.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      (Q : Subgroup H) := congrArg Sylow.toSubgroup hg
  refine ⟨g, ?_⟩
  change (Subgroup.normalizer ((P : Subgroup G) : Set G)).map
    ((MulAut.conj g).toMonoidHom.comp f.toMonoidHom) =
      Subgroup.normalizer ((Q : Subgroup H) : Set H)
  rw [← Subgroup.map_map, Subgroup.map_equiv_normalizer_eq (P : Subgroup G) f,
    Subgroup.map_equiv_normalizer_eq, he]

end Subgroup
namespace Representation
variable {k G H V W : Type*} [CommRing k] [Group G] [Group H]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Act on module coordinates by the same element used to conjugate the actor. -/
def innerIntertwiner (σ : Representation k H W) (g : H) : W ≃ₗ[k] W :=
  LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom g)

/-- The coordinate adjustment is the literal representation action. -/
@[simp] theorem innerIntertwiner_apply (σ : Representation k H W) (g : H) (w : W) :
    innerIntertwiner σ g w = σ g w := rfl

/-- Conjugating the group map and translating module coordinates preserve equivariance. -/
theorem innerIntertwiner_equivariant (ρ : Representation k G V)
    (σ : Representation k H W) (f : G →* H) (e : V ≃ₗ[k] W)
    (he : ∀ a v, e (ρ a v) = σ (f a) (e v)) (g : H) :
    ∀ a v, (e.trans (innerIntertwiner σ g)) (ρ a v) =
      σ ((MulAut.conj g) (f a)) ((e.trans (innerIntertwiner σ g)) v) := by
  intro a v
  change σ g (e (ρ a v)) = σ (g * f a * g⁻¹) (σ g (e v))
  rw [he]
  simp only [map_mul, Module.End.mul_apply]
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, mul_one]

end Representation
namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {p : ℕ} [Fact p.Prime]

omit [Finite G] in
/-- Pull a marked Sylow normalizer back through an actual group equivalence. -/
theorem exists_sylow_normalizer_of_equiv (f : G ≃* H) (B : Subgroup G)
    (C : Subgroup H) (hB : B.map f.toMonoidHom = C)
    (hC : ∃ Q : Sylow p H, normalizer (Q : Set H) = C) :
    ∃ P : Sylow p G, normalizer (P : Set G) = B := by
  obtain ⟨Q, hQ⟩ := hC
  refine ⟨Q.mapSurjective (f := f.symm.toMonoidHom) f.symm.surjective, ?_⟩
  change normalizer ((Q : Subgroup H).map f.symm.toMonoidHom : Set G) = B
  change normalizer ((Q : Subgroup H) : Set H) = C at hQ
  rw [← Subgroup.map_equiv_normalizer_eq, hQ]
  exact (Subgroup.map_symm_eq_iff_map_eq B).mpr hB

private def productSylow (P : Sylow p G) (Q : Sylow p H) : Sylow p (G × H) where
  toSubgroup := (P : Subgroup G).prod Q
  isPGroup' := by
    obtain ⟨a, ha⟩ := P.isPGroup'.exists_card_eq
    obtain ⟨b, hb⟩ := Q.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a + b)
    rw [Nat.card_congr (Subgroup.prodEquiv (P : Subgroup G) (Q : Subgroup H)).toEquiv,
      Nat.card_prod, ha, hb, pow_add]
  is_maximal' := by
    intro S hS hPQ
    apply le_antisymm _ hPQ
    apply Subgroup.le_prod_iff.mpr
    constructor
    · exact le_of_eq (P.is_maximal' (hS.map (MonoidHom.fst G H)) (by
        intro x hx
        exact ⟨(x, 1), hPQ ⟨hx, Q.one_mem⟩, rfl⟩))
    · exact le_of_eq (Q.is_maximal' (hS.map (MonoidHom.snd G H)) (by
        intro x hx
        exact ⟨(1, x), hPQ ⟨P.one_mem, hx⟩, rfl⟩))

omit [Finite G] [Finite H] in
private theorem normalizer_prod_eq (P : Subgroup G) (Q : Subgroup H) :
    normalizer (P.prod Q : Set (G × H)) =
      (normalizer (P : Set G)).prod (normalizer (Q : Set H)) := by
  ext g
  simp only [Subgroup.mem_prod, Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    constructor
    · intro x
      simpa using h (x, 1)
    · intro x
      simpa using h (1, x)
  · rintro ⟨hP, hQ⟩ ⟨x,y⟩
    exact (hP x).and (hQ y)

/-- Products of Sylow normalizers are Sylow normalizers in the product group. -/
theorem exists_sylow_normalizer_prod (B : Subgroup G) (C : Subgroup H)
    (hB : ∃ P : Sylow p G, normalizer (P : Set G) = B)
    (hC : ∃ Q : Sylow p H, normalizer (Q : Set H) = C) :
    ∃ R : Sylow p (G × H), normalizer (R : Set (G × H)) = B.prod C := by
  obtain ⟨P, hP⟩ := hB
  obtain ⟨Q, hQ⟩ := hC
  refine ⟨productSylow P Q, ?_⟩
  change normalizer (((P : Subgroup G).prod (Q : Subgroup H)) : Set (G × H)) = _
  change normalizer ((P : Subgroup G) : Set G) = B at hP
  change normalizer ((Q : Subgroup H) : Set H) = C at hQ
  rw [normalizer_prod_eq, hP, hQ]
end Subgroup

namespace Representation
variable {k G H V W : Type*} [CommRing k] [Group G] [Group H]
    [Finite G] [Finite H] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {p : ℕ} [Fact p.Prime]

/-- Simultaneously align the marked subgroups and an established module equivalence.
The conjugating element is constructed by Sylow conjugacy, without an assumption
on the image of the marked subgroup under the supplied module identification. -/
theorem exists_innerIntertwiner_sylowNormalizer
    (B : Subgroup G) (C : Subgroup H)
    (hB : ∃ P : Sylow p G, Subgroup.normalizer (P : Set G) = B)
    (hC : ∃ Q : Sylow p H, Subgroup.normalizer (Q : Set H) = C)
    (ρ : Representation k G V) (σ : Representation k H W)
    (f : G ≃* H) (e : V ≃ₗ[k] W)
    (he : ∀ a v, e (ρ a v) = σ (f a) (e v)) :
    ∃ g : H, B.map (f.trans (MulAut.conj g)).toMonoidHom = C ∧
      ∀ a v, (e.trans (innerIntertwiner σ g)) (ρ a v) =
        σ ((f.trans (MulAut.conj g)) a) ((e.trans (innerIntertwiner σ g)) v) := by
  obtain ⟨P, rfl⟩ := hB
  obtain ⟨Q, rfl⟩ := hC
  obtain ⟨g, hg⟩ := Subgroup.exists_inner_map_sylow_normalizer f P Q
  exact ⟨g, hg, innerIntertwiner_equivariant ρ σ f.toMonoidHom e he g⟩
end Representation
