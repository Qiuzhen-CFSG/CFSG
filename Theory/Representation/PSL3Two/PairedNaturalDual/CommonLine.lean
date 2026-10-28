module
public import Theory.Representation.PSL3Two.PairedNaturalDual
public import Theory.Representation.BinaryOffender.CommonCenterKernel
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Quotient

/-!
# A common commutator line belongs to one component support

Consider two marked natural--dual component supports and a fixed supplement.
If a common displacement line lies in neither support, each component kernel
fixes the denominator: an actor trivial on one support has displacement only
in the other. Joint faithfulness makes these kernels disjoint, so their ranks
add. The common-line bound then forces the total fixed codimension to be at
most the sum of the two image ranks, contradicting the no-FF component bounds.

Thus a denominator of codimension at most the actor rank places its common
line in one support. This supplies the mixed-support step of Aschbacher--Smith
14.6.24(3), printed pp.1039--1040, by a kernel-rank argument. No order-nine
centralizer claim, support placement, or independent actor choice is assumed.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace BinaryLinearThree.NaturalDual.Paired
variable {H E : Type*} [_root_.Group H] [Finite H] [IsElementaryAbelian 2 H]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
private theorem elementary_card (A : Subgroup H) : Nat.card A = 2 ^ rank A := by
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective A.subtype A.subtype_injective
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  rw [rank,hn,Nat.log_pow (by decide : 1 < 2)]

private theorem rank_kernel_add_range {X : Type*} [_root_.Group X] (f : H →* X) :
    rank f.ker + rank f.range = Nat.log 2 (Nat.card H) := by
  let : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 f.range).exists_card_eq
  have he : Nat.card f.range = 2 ^ rank f.range := by
    rw [rank,hn,Nat.log_pow (by decide : 1 < 2)]
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker,elementary_card,he,←pow_add] at hc
  rw [←hc,Nat.log_pow (by decide : 1 < 2)]

omit [FiniteDimensional (ZMod 2) E] in
private theorem rank_join_kernels {ρ : Representation (ZMod 2) H E}
    (m : Marking ρ) (hf : Function.Injective ρ) :
    rank (m.left.ker ⊔ m.right.ker) = rank m.left.ker + rank m.right.ker := by
  have hd : Disjoint m.left.ker m.right.ker := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro a ha
    apply (injective_iff_map_eq_one _).mp (m.joint_injective hf)
    exact Prod.ext ha.1 ha.2
  have hn : m.right.ker ≤ normalizer (m.left.ker : Set H) := by
    intro a _
    exact Subgroup.mem_normalizer_iff.mpr (fun b => by
      simp only [mul_comm a b, mul_inv_cancel_right, iff_self])
  have hc := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hd
  rw [elementary_card,elementary_card,elementary_card,←pow_add] at hc
  exact Nat.pow_right_injective (by decide : 1 < 2) hc
end BinaryLinearThree.NaturalDual.Paired

namespace BinaryLinearThree.NaturalDual.Paired.Marking
variable {H E : Type*} [_root_.Group H] [Finite H] [IsElementaryAbelian 2 H]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  {ρ : Representation (ZMod 2) H E} (m : Marking ρ)

omit [Finite H] [IsElementaryAbelian 2 H] [FiniteDimensional (ZMod 2) E] in
private theorem displacement_mem_right_of_left_trivial
    (a : H) (ha : m.left a = 1) (v : E) : ρ a v - v ∈ m.rightEmbedding.range := by
  have hv : v ∈ m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace ρ ⊤ := by
    rw [m.span]; trivial
  obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨x,⟨x',rfl⟩,y,⟨y',rfl⟩,rfl⟩ := Submodule.mem_sup.mp hw
  have hfixed : ρ a z = z := hz ⟨a,mem_top a⟩
  refine ⟨autAction (m.right a) y' - y',?_⟩
  simp only [map_add,m.left_intertwines,m.right_intertwines,ha,map_one,
    Module.End.one_apply,hfixed,map_sub]
  abel

omit [Finite H] [IsElementaryAbelian 2 H] [FiniteDimensional (ZMod 2) E] in
private theorem displacement_mem_left_of_right_trivial
    (a : H) (ha : m.right a = 1) (v : E) : ρ a v - v ∈ m.leftEmbedding.range := by
  have hv : v ∈ m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace ρ ⊤ := by
    rw [m.span]; trivial
  obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨x,⟨x',rfl⟩,y,⟨y',rfl⟩,rfl⟩ := Submodule.mem_sup.mp hw
  have hfixed : ρ a z = z := hz ⟨a,mem_top a⟩
  refine ⟨autAction (m.left a) x' - x',?_⟩
  simp only [map_add,m.left_intertwines,m.right_intertwines,ha,map_one,
    Module.End.one_apply,hfixed,map_sub]
  abel

/-- A rank-compared common commutator line lies in a single component support. -/
theorem line_le_one_of_supports (hf : Function.Injective ρ)
    (hpos : 0 < Nat.log 2 (Nat.card H))
    (W : Subrepresentation ρ) (Z : Submodule (ZMod 2) E)
    (hZ : Module.finrank (ZMod 2) Z ≤ 1)
    (hd : ∀ a v, v ∈ W.toSubmodule → ρ a v - v ∈ Z)
    (hz : ∀ a z, z ∈ Z → ρ a z = z)
    (hcmp : Module.finrank (ZMod 2) (E ⧸ W.toSubmodule) ≤ Nat.log 2 (Nat.card H)) :
    Z ≤ m.leftEmbedding.range ∨ Z ≤ m.rightEmbedding.range := by
  by_contra! hn
  have hdim : Module.finrank (ZMod 2) Z = 1 := by
    have hne : Z ≠ ⊥ := fun he => hn.1 (he ▸ bot_le)
    have hp : 0 < Module.finrank (ZMod 2) Z := by
      by_contra hh
      exact hne (Submodule.finrank_eq_zero.mp (by omega))
    omega
  have hatom := Submodule.isAtom_iff_finrank_eq_one.mpr hdim
  have hleft := hatom.not_le_iff_disjoint.mp hn.1
  have hright := hatom.not_le_iff_disjoint.mp hn.2
  let B := m.left.ker ⊔ m.right.ker
  have hB : B ≤ subspaceKernel ρ W.toSubmodule ⊤ := by
    apply sup_le
    · intro a ha
      refine ⟨mem_top _,?_⟩
      intro v hv
      exact sub_eq_zero.mp (Submodule.disjoint_def.mp hright _ (hd a v hv)
        (m.displacement_mem_right_of_left_trivial a ha v))
    · intro a ha
      refine ⟨mem_top _,?_⟩
      intro v hv
      exact sub_eq_zero.mp (Submodule.disjoint_def.mp hleft _ (hd a v hv)
        (m.displacement_mem_left_of_right_trivial a ha v))
  have hbound := CommonCenter.fixedCodim_add_trivial_rank_le_codim ρ W Z hZ hd hz B
    (fun b hb v hv => (hB hb).2 v hv)
  have hjoin := Paired.rank_join_kernels m hf
  have hl := Paired.rank_kernel_add_range m.left
  have hr := Paired.rank_kernel_add_range m.right
  let : IsElementaryAbelian 2 (⊤ : Subgroup H) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup H).subtype (⊤ : Subgroup H).subtype_injective
  have hsum := m.sum_fixedCodim_le (⊤ : Subgroup H)
  have hrank := m.rank_le_sum hf (⊤ : Subgroup H)
  have hstrict := m.image_rank_lt_codim (⊤ : Subgroup H)
  have htop : rank (⊤ : Subgroup H) = Nat.log 2 (Nat.card H) := by
    exact congrArg (Nat.log 2) (Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).toEquiv)
  simp only [←MonoidHom.range_eq_map] at hsum hrank hstrict
  rw [htop] at hrank
  have hcodim : fixedCodim ρ ⊤ ≤ rank m.left.range + rank m.right.range := by
    change fixedCodim ρ ⊤ + rank (m.left.ker ⊔ m.right.ker) ≤ _ at hbound
    omega
  have hnon : m.left.range ≠ ⊥ ∨ m.right.range ≠ ⊥ := by
    by_contra! hh
    rw [hh.1,hh.2,Representation.BinaryOffender.rank_bot,zero_add] at hrank
    omega
  have hweak (f : H →* MulAut Group) : rank f.range ≤ fixedCodim autAction f.range := by
    let : IsElementaryAbelian 2 f.range :=
      IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    by_cases hn : f.range = ⊥
    · simp [hn]
    · exact (Nat.lt_of_not_ge (fun hh => not_isFFModule_autAction
        ⟨f.range,⟨hn,inferInstance⟩,hh⟩)).le
  have hwl := hweak m.left
  have hwr := hweak m.right
  rcases hnon with hn | hn
  · have := hstrict.1 hn; omega
  · have := hstrict.2 hn; omega
end BinaryLinearThree.NaturalDual.Paired.Marking

namespace BinaryLinearThree.NaturalDual.Paired.Marking
variable {H E J : Type*} [_root_.Group H] [_root_.Group J]
  [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) H E}
/-- Restrict both component actions along the same homomorphism. -/
@[expose] def comp (m : Marking ρ) (f : J →* H) : Marking (ρ.comp f) where
  left := m.left.comp f
  right := m.right.comp f
  leftEmbedding := m.leftEmbedding
  rightEmbedding := m.rightEmbedding
  left_injective := m.left_injective
  right_injective := m.right_injective
  disjoint := m.disjoint
  span := by
    apply top_unique
    rw [←m.span]
    exact sup_le_sup le_rfl (fun v hv a => hv ⟨f a,mem_top _⟩)
  left_intertwines := fun a v => m.left_intertwines (f a) v
  right_intertwines := fun a v => m.right_intertwines (f a) v
end BinaryLinearThree.NaturalDual.Paired.Marking
