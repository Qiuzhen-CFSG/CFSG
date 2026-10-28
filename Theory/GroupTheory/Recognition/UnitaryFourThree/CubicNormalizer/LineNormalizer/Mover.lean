module

public import Theory.GroupTheory.IndexThreeCubicLineMover
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.QuaternionRotation

/-!
# The literal cubic-line mover in a group of type U₄(3)

The original reflected rotation has square z.  Once the earlier U-line
normalizer has the source index-three action on X, the subgroup mover
produces an actual conjugate of the second line, inverted by z and lying
in the displacement subgroup [V,z].  Thus any original odd kernel
containing that displacement also contains the chosen line.

Source: Aschbacher, *Sporadic Groups* (1994),45.8,printed p.246.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G : Type*} [Group G] [Finite G] {z : G}

theorem exists_inverted_cubic_line (h : IsType z) (P : Sylow 3 (centralizer z))
    (m : CubicNormalizer.ReflectedMarking z
      ((P : Subgroup (centralizer z)).map (centralizer z).subtype))
    (U B D : Subgroup G) (hB : Nat.card B = 3)
    (hjoin : U ⊔ B = (P : Subgroup (centralizer z)).map (centralizer z).subtype)
    (hKV : normalizer (U : Set G) ≤ normalizer (CubicNormalizer.oddKernel
      ((P : Subgroup (centralizer z)).map (centralizer z).subtype) : Set G))
    (hNB : normalizer (U : Set G) ⊓ normalizer
      ((P : Subgroup (centralizer z)).map (centralizer z).subtype : Set G) ≤
        normalizer (B : Set G))
    (hindex : (normalizer ((P : Subgroup (centralizer z)).map
      (centralizer z).subtype : Set G)).relIndex (normalizer (U : Set G)) = 3)
    (hD : ⁅CubicNormalizer.oddKernel
      ((P : Subgroup (centralizer z)).map (centralizer z).subtype), zpowers z⁆ ≤ D) :
    ∃ g ∈ normalizer (U : Set G), let F := B.map (MulAut.conj g).toMonoidHom
      F ≤ CubicNormalizer.oddKernel
        ((P : Subgroup (centralizer z)).map (centralizer z).subtype) ⊓ D ∧
      Nat.card F = 3 ∧
      ¬F ≤ (P : Subgroup (centralizer z)).map (centralizer z).subtype ∧
      (∀ x ∈ F, z*x*z⁻¹=x⁻¹) ∧ ⁅F,zpowers z⁆=F := by
  let X := (P : Subgroup (centralizer z)).map (centralizer z).subtype
  let V := CubicNormalizer.oddKernel X
  have hUX : U ≤ X := le_sup_left.trans_eq hjoin
  have hBX : B ≤ X := le_sup_right.trans_eq hjoin
  have hfixed : V ⊓ centralizer z = X := (h.cubic_sylow_structure P).2.2.2.2.1
  have hXV : X ≤ V := hfixed ▸ inf_le_left
  have hr : m.s*m.t ∈ normalizer (U : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      change (m.s*m.t)*x*(m.s*m.t)⁻¹ ∈ U
      rw [m.rotation_inverts x (hUX hx)]
      exact U.inv_mem hx
    · rw [card_map_of_injective (MulAut.conj (m.s*m.t)).injective]
  have hr4 : (m.s*m.t)^4=1 := by
    rw [show (4:ℕ)=2*2 from rfl,pow_mul,m.rotation_square,←h.involution]
    exact pow_orderOf_eq_one z
  obtain ⟨g,hg,hFV,hFc,hFX,hinv,hcomm⟩ :=
    exists_inverted_cubic_conjugate_of_index_three (normalizer (U : Set G))
      V X U B z (m.s*m.t) hr hr4 m.rotation_square hB (hBX.trans hXV) hjoin
      le_rfl hKV hfixed hNB hindex
  refine ⟨g,hg,le_inf hFV ?_,hFc,hFX,hinv,hcomm⟩
  rw [←hcomm]
  exact (commutator_mono hFV le_rfl).trans hD

end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
