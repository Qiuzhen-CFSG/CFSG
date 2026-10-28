module
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Abelian Sylow subgroups under sections and coprime extensions

Abelian Sylow subgroups pass to subgroups, quotients and direct products.
A homomorphism with kernel of order prime to p reflects this property,
since its restriction to each p-subgroup is injective. These statements
retain the supplied maps and require no classification.

Source application: the impossible triple-Mathieu section in
Aschbacher--Smith 15.2.15, printed p.1118, refs/quasithin.pdf.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory

/-- Every Sylow subgroup for the specified prime is abelian. -/
@[expose] def HasAbelianSylow (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ P : Sylow p G, IsMulCommutative P

namespace HasAbelianSylow
variable {p : ℕ}
variable {A B : Type*} [Group A] [Group B]

theorem subgroup (h : HasAbelianSylow p A) (Q : Subgroup A) (hQ : IsPGroup p Q) :
    IsMulCommutative Q := by
  obtain ⟨P,hP⟩ := hQ.exists_le_sylow
  let := h P
  exact .of_setLike_mul_comm fun a ha b hb => setLike_mul_comm (hP ha) (hP hb)

theorem of_injective (h : HasAbelianSylow p B) (f : A →* B)
    (hf : Function.Injective f) : HasAbelianSylow p A := by
  intro P
  let := h.subgroup ((P : Subgroup A).map f) (P.isPGroup'.map f)
  exact .of_comm fun a b => Subtype.ext (hf (by
    change f ((a : A) * b) = f ((b : A) * a)
    rw [map_mul,map_mul]
    exact setLike_mul_comm (mem_map_of_mem f a.property) (mem_map_of_mem f b.property)))

theorem of_surjective [Fact p.Prime] [Finite A] (h : HasAbelianSylow p A) (f : A →* B)
    (hf : Function.Surjective f) : HasAbelianSylow p B := by
  intro Q
  obtain ⟨P,rfl⟩ := Sylow.mapSurjective_surjective hf p Q
  let := h P
  exact (P : Subgroup A).map_isMulCommutative f

theorem of_coprime_kernel [Fact p.Prime] [Finite A] (h : HasAbelianSylow p B) (f : A →* B)
    (hk : Nat.Coprime p (Nat.card f.ker)) : HasAbelianSylow p A := by
  intro P
  let := h.subgroup ((P : Subgroup A).map f) (P.isPGroup'.map f)
  have hinj := injective_comp_subtype_of_coprime_ker f hk (P : Subgroup A) P.isPGroup'
  exact .of_comm fun a b => hinj (by
    change f ((a : A) * b) = f ((b : A) * a)
    rw [map_mul,map_mul]
    exact setLike_mul_comm (mem_map_of_mem f a.property) (mem_map_of_mem f b.property))

theorem prod (hA : HasAbelianSylow p A) (hB : HasAbelianSylow p B) :
    HasAbelianSylow p (A × B) := by
  intro P
  let := hA.subgroup ((P : Subgroup (A × B)).map (MonoidHom.fst A B))
    (P.isPGroup'.map (MonoidHom.fst A B))
  let := hB.subgroup ((P : Subgroup (A × B)).map (MonoidHom.snd A B))
    (P.isPGroup'.map (MonoidHom.snd A B))
  apply IsMulCommutative.of_comm
  intro a b
  apply Subtype.ext
  apply Prod.ext
  · exact setLike_mul_comm (mem_map_of_mem (MonoidHom.fst A B) a.property)
      (mem_map_of_mem (MonoidHom.fst A B) b.property)
  · exact setLike_mul_comm (mem_map_of_mem (MonoidHom.snd A B) a.property)
      (mem_map_of_mem (MonoidHom.snd A B) b.property)
end HasAbelianSylow
end Theory.GroupTheory
