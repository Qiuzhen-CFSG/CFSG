module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.KernelResidual
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.DihedralMarking
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Ambient markings of a normal dihedral source actor

The literal kernel is cyclic of prime order and is the actor’s two-residual.
Its image is normal in the ambient group and lies in the ambient two-residual.
Mapping the generation and inversion identities retains the exact actor
inclusion, marked involution and full moved module.

Source: Aschbacher–Smith D.2.17(1)–(2), used in original 15.1.2(1).
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u
variable {G V : Type u} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

theorem DihedralMarking.ambient_marks (K : Subgroup G) [K.Normal]
    {l : LocalGeneration (ρ.comp K.subtype)} {p m : ℕ}
    (hp : PrimeDimensionOptions p m) (h : DihedralMarking l p m) :
    let P := l.kernel.map K.subtype
    let t := (l.involution : G)
    Nat.card K = 2*p ∧ IsCyclic P ∧ Nat.card P = p ∧ P.Normal ∧
      l.kernel = pResidual 2 K ∧ P ≤ pResidual 2 G ∧
      K = P ⊔ zpowers t ∧ orderOf t = 2 ∧
      (∀ x : P, t * (x : G) * t⁻¹ = (x : G)⁻¹) ∧
      subspaceCommutator ρ ⊤ P = ⊤ := by
  let P := l.kernel.map K.subtype
  let t := (l.involution : G)
  have hpprime : Nat.Prime p := by
    rcases (primeDimensionOptions_iff p m).mp hp with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
  have hcK : Nat.card K = 2*p := by
    rw [←l.kernel.card_mul_index,l.kernel_index_two,h.card_kernel,mul_comm]
  let : Fact p.Prime := ⟨hpprime⟩
  let : IsCyclic l.kernel := isCyclic_of_prime_card h.card_kernel
  have hr := l.kernel_eq_twoResidual
  have hPnormal : P.Normal := by
    change (l.kernel.map K.subtype).Normal
    rw [hr]
    infer_instance
  have hgen := congrArg (fun A : Subgroup K => A.map K.subtype) l.generated
  rw [Subgroup.map_sup,MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hgen
  refine ⟨hcK,?_,(card_map_of_injective K.subtype_injective).trans h.card_kernel,
    hPnormal,hr,?_,hgen.symm,?_,?_,?_⟩
  · exact isCyclic_of_surjective (K.subtype.subgroupMap l.kernel)
      (MonoidHom.subgroupMap_surjective _ _)
  · rw [hr]
    exact map_pResidual_le 2 K.subtype
  · exact (orderOf_injective K.subtype K.subtype_injective l.involution).trans l.order_two
  · intro x
    obtain ⟨y,hy,he⟩ := x.property
    have hinv := congrArg K.subtype (h.inverts ⟨y,hy⟩)
    change (l.involution : G) * (y : G) * (l.involution : G)⁻¹ = (y : G)⁻¹ at hinv
    change (y : G) = (x : G) at he
    rw [he] at hinv
    exact hinv
  · rw [←subspaceCommutator_comp_map]
    exact l.moved
end CFSG.Quasithin.ChapterD.CyclicSource
