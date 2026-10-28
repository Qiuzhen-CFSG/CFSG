module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.SL2NaturalOffenders.Semilinear

/-!
# The centralizing natural two-dimensional factor

The conclusion witness `NaturalTwo` identifies a normal subgroup with the
actual SL₂(2) matrix group and intertwines its action on its actual moved
space with the natural matrix action. This witness must be constructed
from B.1.8 in the solvable branch; its existence is not asserted here.

The scalar centralizer calculation for SL₂ shows that every commuting
invertible binary operator is the identity on this space. The action
commutator identity then gives [E,L]≤C_E(K). This supplies the
three-subgroup step in the centralizing case of Lemma 13.8.5.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
combined manuscript of 1 March 2004, printed pp.947–948.
The matrix centralizer theorem is reused from SL2NaturalOffenders.Semilinear.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition

private theorem centralizer_fixes_binary_two
    {A : Type*} [Group A] (σ : Representation (ZMod 2) A (Fin 2 → ZMod 2))
    (K : Subgroup A) (eK : K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hnat : ∀ (k : K) v, σ k v = (eK k).val.mulVec v)
    (a : A) (hcomm : ∀ k ∈ K, Commute a k) (v : Fin 2 → ZMod 2) : σ a v = v := by
  obtain ⟨c, hc⟩ := Representation.SL2NaturalOffenders.centralizer_scalar
    (σ a).toAddMonoidHom (by
      intro g w
      obtain ⟨k, rfl⟩ := eK.surjective g
      rw [← hnat, ← hnat]
      change (σ a * σ k) w = (σ k * σ a) w
      rw [← map_mul, ← map_mul, (hcomm k k.property).eq])
  have hc01 : c = 0 ∨ c = 1 := by
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hc01 with hz | ho
  · have hz' : σ a (fun _ => (1 : ZMod 2)) = 0 := by simpa [hz] using hc (fun _ => 1)
    have hz'' := congrArg (σ a⁻¹) hz'
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, map_zero] at hz''
    have : (1 : ZMod 2) = 0 := congrFun hz'' 0
    exact (one_ne_zero this).elim
  · simpa [ho] using hc v

variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) A E) (K : Subgroup A) [K.Normal]

private theorem moved_invariant (a : A) (w : E)
    (hw : w ∈ subspaceCommutator ρ ⊤ K) : ρ a w ∈ subspaceCommutator ρ ⊤ K := by
  have hi : (⊤ : Subgroup A) ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ K) :=
    subspaceCommutator_invariant_normalizer ρ
      (by intro a _ w; simp) le_normalizer_of_normal
  exact (hi (mem_top a) w).2 hw

/-- The actual action on the commutator space of a normal subgroup. -/
def movedRepresentation :
    Representation (ZMod 2) A (subspaceCommutator ρ ⊤ K) where
  toFun a := (ρ a).restrict (by exact moved_invariant ρ K a)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

/-- A concrete equivariant natural two-dimensional model for the moved space. -/
structure NaturalTwo where
  groupEquiv : K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
  moduleEquiv : subspaceCommutator ρ ⊤ K ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)
  intertwines : ∀ (k : K) w,
    moduleEquiv (movedRepresentation ρ K k w) =
      (groupEquiv k).val.mulVec (moduleEquiv w)

/-- Commuting actors fix the actual natural two-dimensional moved space. -/
theorem fixes_moved_of_commutes (d : NaturalTwo ρ K)
    (a : A) (hcomm : ∀ k ∈ K, Commute a k)
    (w : subspaceCommutator ρ ⊤ K) : ρ a w = w := by
  let e := d.moduleEquiv
  let σ := movedRepresentation ρ K
  let τ : Representation (ZMod 2) A (Fin 2 → ZMod 2) :=
    { toFun a := e.toLinearMap.comp ((σ a).comp e.symm.toLinearMap)
      map_one' := by ext; simp
      map_mul' a b := by ext; simp }
  have hn : ∀ (k : K) v, τ k v = (d.groupEquiv k).val.mulVec v := by
    intro k v
    change e (σ k (e.symm v)) = _
    rw [d.intertwines, e.apply_symm_apply]
  have hf := centralizer_fixes_binary_two τ K d.groupEquiv hn a hcomm (e w)
  have he : e (σ a w) = e w := by simpa [τ] using hf
  exact congrArg Subtype.val (e.injective he)

/-- The three-subgroup calculation in the last paragraph of 13.8.5.
Commutation and the concrete natural model imply [E,L] ≤ C_E(K). -/
theorem commutator_le_fixed_of_naturalTwo (d : NaturalTwo ρ K) (L : Subgroup A)
    (hcomm : ∀ l ∈ L, ∀ k ∈ K, Commute l k) :
    subspaceCommutator ρ ⊤ L ≤ fixedSpace ρ K := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, v, _, rfl⟩ k
  have hd : ρ k v - v ∈ subspaceCommutator ρ ⊤ K :=
    Submodule.subset_span ⟨k, k.property, v, Submodule.mem_top, rfl⟩
  have hf := fixes_moved_of_commutes ρ K d l (hcomm l hl) ⟨_, hd⟩
  change ρ l (ρ k v - v) = ρ k v - v at hf
  have hkl : ρ k (ρ l v) = ρ l (ρ k v) := by
    change (ρ k * ρ l) v = (ρ l * ρ k) v
    rw [← map_mul, ← map_mul, (hcomm l hl k k.property).eq]
  change ρ (k : A) (ρ l v - v) = ρ l v - v
  rw [map_sub] at hf ⊢
  rw [hkl]
  exact sub_eq_sub_iff_sub_eq_sub.mp hf

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition

end
