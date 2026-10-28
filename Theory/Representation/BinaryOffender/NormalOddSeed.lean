module

public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.InvariantAction

/-!
# Normal odd actors and Sylow-fixed generating seeds

Suppose a binary module is spanned by the ambient translates of a seed fixed
by S. If normal subgroups P ≤ K satisfy K = P(K ∩ S), every K-displacement
of the seed is a P-displacement. Normality extends this to all translates,
so [V,K] = [V,P]. For odd P, the coprime fixed/moved splitting then yields
C_V(P) = C_V(K), and K acts fully on the moved summand.

This is the linear reduction in the first paragraph of Aschbacher--Smith,
15.1.2, printed pp.1084--1085, before the applications of D.2.16 and D.2.17. The subgroup S need
not be Sylow once its fixed seed and the displayed factorization are supplied.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.NormalOddSeed
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)

/-- The normal factorization makes K and P have the same moved space. -/
theorem moved_eq (K P S : Subgroup G) [K.Normal] [P.Normal]
    (hKP : K = P ⊔ (K ⊓ S)) (Z : Submodule (ZMod 2) V)
    (hZ : Z ≤ fixedSpace ρ S)
    (hgen : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤) :
    subspaceCommutator ρ ⊤ K = subspaceCommutator ρ ⊤ P := by
  let W := subspaceCommutator ρ ⊤ P
  have hW : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ W :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) le_normalizer_of_normal
  have hseed (k : G) (hk : k ∈ K) (z : V) (hz : z ∈ Z) : ρ k z - z ∈ W := by
    obtain ⟨p, hp, s, hs, rfl⟩ := mem_sup_of_normal_left.mp (hKP ▸ hk)
    have hsfix : ρ s z = z := hZ hz ⟨s, hs.2⟩
    rw [map_mul, Module.End.mul_apply, hsfix]
    exact Submodule.subset_span ⟨p, hp, z, Submodule.mem_top, rfl⟩
  have hall (k : G) (hk : k ∈ K) (v : V) : ρ k v - v ∈ W := by
    have hspan : Submodule.span (ZMod 2) {w | ∃ g z, z ∈ Z ∧ ρ g z = w} ≤
        W.comap (ρ k - 1) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g,z,hz,rfl⟩
      have hconj : g⁻¹ * k * g ∈ K := by
        simpa only [inv_inv] using (inferInstance : K.Normal).conj_mem k hk g⁻¹
      have hm := (hW (mem_top g) _).2 (hseed (g⁻¹*k*g) hconj z hz)
      change ρ k (ρ g z) - ρ g z ∈ W
      convert hm using 1
      simp only [map_sub, ← Module.End.mul_apply, ← map_mul]
      simp only [← mul_assoc, mul_inv_cancel, one_mul]
    exact hspan (hgen.ge Submodule.mem_top)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,v,_,rfl⟩
    exact hall k hk v
  · apply Submodule.span_mono
    rintro _ ⟨p,hp,v,hv,rfl⟩
    exact ⟨p, hKP.symm ▸ mem_sup_left hp, v, hv, rfl⟩

/-- Odd-order splitting identifies the fixed spaces of P and K. -/
theorem fixed_eq [Finite G] (K P S : Subgroup G) [K.Normal] [P.Normal]
    (hodd : Odd (Nat.card P)) (hKP : K = P ⊔ (K ⊓ S))
    (Z : Submodule (ZMod 2) V) (hZ : Z ≤ fixedSpace ρ S)
    (hgen : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤) :
    fixedSpace ρ P = fixedSpace ρ K := by
  have he := moved_eq ρ K P S hKP Z hZ hgen
  have hc : IsCompl (fixedSpace ρ P) (subspaceCommutator ρ ⊤ P) :=
    by simpa only [RegularCyclicNormalClosure.displacementSpan, subspaceCommutator, eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hodd)
  apply le_antisymm
  · intro v hv k
    apply sub_eq_zero.mp
    apply Submodule.disjoint_def.mp hc.disjoint
    · exact (fixedSpace ρ P).sub_mem
        ((fixedSpace_stable_of_normal ρ P (mem_top (k:G)) v).2 hv) hv
    · rw [← he]
      exact Submodule.subset_span ⟨k,k.property,v,Submodule.mem_top,rfl⟩
  · intro v hv p
    exact hv ⟨p,hKP.symm ▸ mem_sup_left p.property⟩


/-- The odd moved summand has a complement fixed by all of K. -/
theorem isCompl_moved_fixed [Finite G] (K P S : Subgroup G) [K.Normal] [P.Normal]
    (hodd : Odd (Nat.card P)) (hKP : K = P ⊔ (K ⊓ S))
    (Z : Submodule (ZMod 2) V) (hZ : Z ≤ fixedSpace ρ S)
    (hgen : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤) :
    IsCompl (subspaceCommutator ρ ⊤ P) (fixedSpace ρ K) := by
  rw [← fixed_eq ρ K P S hodd hKP Z hZ hgen]
  simpa only [RegularCyclicNormalClosure.displacementSpan, subspaceCommutator, eq_comm] using
    (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hodd).symm

private theorem moved_self_of_fixed_complement (H : Subgroup G)
    (W : Submodule (ZMod 2) V) (he : subspaceCommutator ρ ⊤ H = W)
    (hspan : W ⊔ fixedSpace ρ H = ⊤) : subspaceCommutator ρ W H = W := by
  apply le_antisymm
  · exact (subspaceCommutator_mono_left ρ le_top H).trans he.le
  · apply he.ge.trans
    apply Submodule.span_le.mpr
    rintro _ ⟨h,hh,v,_,rfl⟩
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ W ⊔ fixedSpace ρ H by rw [hspan]; trivial)
    have hf : ρ h w = w := hw ⟨h,hh⟩
    have heq : ρ h (u+w) - (u+w) = ρ h u-u := by rw [map_add,hf]; abel
    rw [heq]
    exact Submodule.subset_span ⟨h,hh,u,hu,rfl⟩

/-- An odd actor acts fully on its moved summand. -/
theorem odd_moved_self (P : Subgroup G) [Finite P] (hodd : Odd (Nat.card P)) :
    subspaceCommutator ρ (subspaceCommutator ρ ⊤ P) P = subspaceCommutator ρ ⊤ P := by
  apply moved_self_of_fixed_complement ρ P _ rfl
  simpa only [RegularCyclicNormalClosure.displacementSpan, subspaceCommutator, eq_comm] using
    (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hodd).symm.sup_eq_top

/-- The larger normal actor also acts fully on the odd moved summand. -/
theorem moved_self [Finite G] (K P S : Subgroup G) [K.Normal] [P.Normal]
    (hodd : Odd (Nat.card P)) (hKP : K = P ⊔ (K ⊓ S))
    (Z : Submodule (ZMod 2) V) (hZ : Z ≤ fixedSpace ρ S)
    (hgen : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤) :
    subspaceCommutator ρ (subspaceCommutator ρ ⊤ P) K = subspaceCommutator ρ ⊤ P :=
  moved_self_of_fixed_complement ρ K _ (moved_eq ρ K P S hKP Z hZ hgen)
    (isCompl_moved_fixed ρ K P S hodd hKP Z hZ hgen).sup_eq_top

end Representation.BinaryOffender.NormalOddSeed
