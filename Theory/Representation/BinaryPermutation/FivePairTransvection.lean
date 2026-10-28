module
public import Theory.Representation.BinaryPermutation.FivePairFixedSpaces
public import Theory.Representation.BinaryPermutation.FivePairExtension
/-!
# Transvection displacement on the paired five-letter fixed planes

The normalizer of the two disjoint transpositions acts on their common fixed
plane with one possible nonzero displacement. The explicit center vector is
retained under any conjugate marking. Equivariant sections of a paired natural
quotient then lift displacement exactly, since its kernel is fixed pointwise.

Source: Aschbacher–Smith E.2.3(3) and 10.2.1, printed pp.216–217 and743.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation.FivePairFixedSpaces
local notation "r" => coreRepresentation (Fin 5)
local instance : DecidablePred (· ∈ core (Fin 5)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype Space := Subtype.fintype _
def centerVector : Space := ⟨![1,1,1,1,0], by decide +kernel⟩
def planeVector : Space := ⟨![1,1,0,0,0], by decide +kernel⟩
theorem centerVector_ne_zero : centerVector ≠ 0 := by decide +kernel
private theorem interchange_displacement : ∀ p : Perm,
    p*first*p⁻¹=second → p*second*p⁻¹=first →
    ∀ x : Space, r first x=x → r second x=x →
      r p x-x=0 ∨ r p x-x=centerVector := by decide +kernel
private theorem interchange_witness : ∀ p : Perm,
    p*first*p⁻¹=second → p*second*p⁻¹=first →
      r p planeVector-planeVector=centerVector := by decide +kernel
private theorem inside_fixed (p : Perm) (hp : p ∈ pairClosure)
    (x : Space) (h1 : r first x=x) (h2 : r second x=x) : r p x=x := by
  rcases (mem_pairClosure p).mp hp with rfl | rfl | rfl | rfl
  · simp
  · exact h1
  · exact h2
  · rw [map_mul,Module.End.mul_apply,h2,h1]
theorem normalizer_displacement (p : Perm)
    (hp : p ∈ normalizer (pairClosure : Set Perm))
    (x : Space) (h1 : r first x=x) (h2 : r second x=x) :
    r p x-x=0 ∨ r p x-x=centerVector := by
  by_cases hin : p ∈ pairClosure
  · exact Or.inl (by rw [inside_fixed p hin x h1 h2,sub_self])
  · obtain ⟨hp1,hp2⟩ := pairNormalizer_outside_exchanges p hp hin
    exact interchange_displacement p hp1 hp2 x h1 h2

theorem normalizer_outside_witness (p : Perm)
    (hp : p ∈ normalizer (pairClosure : Set Perm)) (hout : p ∉ pairClosure) :
    r first planeVector=planeVector ∧ r second planeVector=planeVector ∧
    r p planeVector-planeVector=centerVector := by
  obtain ⟨hp1,hp2⟩ := pairNormalizer_outside_exchanges p hp hout
  exact ⟨by decide +kernel,by decide +kernel,interchange_witness p hp1 hp2⟩

private theorem action_inv_cancel (a : Perm) (x : Space) : r a⁻¹ (r a x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
private theorem action_conj (a p : Perm) (x : Space) :
    r ((MulAut.conj a) p) (r a x) = r a (r p x) := by
  simp only [MulAut.conj_apply, map_mul, Module.End.mul_apply, action_inv_cancel]

theorem conjugate_normalizer_displacement (a p : Perm)
    (hp : p ∈ (normalizer (pairClosure : Set Perm)).map (MulAut.conj a).toMonoidHom)
    (x : Space)
    (h1 : r ((MulAut.conj a) first) x=x)
    (h2 : r ((MulAut.conj a) second) x=x) :
    r p x-x=0 ∨ r p x-x=r a centerVector := by
  obtain ⟨p,hp,rfl⟩ := hp
  let y := r a⁻¹ x
  have hx : r a y=x := by simpa only [inv_inv] using action_inv_cancel a⁻¹ x
  have h1' : r first y=y := by
    apply (Function.LeftInverse.injective (action_inv_cancel a))
    rw [←action_conj,hx,h1]
  have h2' : r second y=y := by
    apply (Function.LeftInverse.injective (action_inv_cancel a))
    rw [←action_conj,hx,h2]
  rcases normalizer_displacement p hp y h1' h2' with h | h
  · left
    have hh := congrArg (r a) h
    simpa only [map_sub, ←action_conj, hx, map_zero, MulEquiv.coe_toMonoidHom] using hh
  · right
    have hh := congrArg (r a) h
    simpa only [map_sub, ←action_conj, hx, MulEquiv.coe_toMonoidHom] using hh

end BinaryPermutation.FivePairFixedSpaces

namespace BinaryPermutation.FivePair
open FivePairFixedSpaces
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) (Perm × Perm) V)
  (p : V →ₗ[ZMod 2] (Core × Core))
  (hk : ∀ v, p v=0 → ∀ g, ρ g v=v)
  (s₁ s₂ : Core →ₗ[ZMod 2] V)
  (h₁ : ∀ v, p (s₁ v)=(v,0)) (h₂ : ∀ v, p (s₂ v)=(0,v))
  (he₁ : ∀ g v, s₁ (coreRepresentation (Fin 5) g.1 v)=ρ g (s₁ v))
  (he₂ : ∀ g v, s₂ (coreRepresentation (Fin 5) g.2 v)=ρ g (s₂ v))

include hk h₁ h₂ he₁ he₂ in
theorem displacement_eq (g : Perm × Perm) (v : V) :
    ρ g v-v = s₁ (coreRepresentation (Fin 5) g.1 (p v).1-(p v).1) +
      s₂ (coreRepresentation (Fin 5) g.2 (p v).2-(p v).2) := by
  have hz : p (v-s₁ (p v).1-s₂ (p v).2)=0 := by
    rw [map_sub,map_sub,h₁,h₂]
    ext <;> simp
  have hh := hk _ hz g
  rw [map_sub,map_sub,←he₁,←he₂] at hh
  simp only [map_sub]
  have h := congrArg (fun w => w + s₁ (coreRepresentation (Fin 5) g.1 (p v).1) +
    s₂ (coreRepresentation (Fin 5) g.2 (p v).2) - v) hh
  abel_nf at h ⊢
  exact h

end BinaryPermutation.FivePair
