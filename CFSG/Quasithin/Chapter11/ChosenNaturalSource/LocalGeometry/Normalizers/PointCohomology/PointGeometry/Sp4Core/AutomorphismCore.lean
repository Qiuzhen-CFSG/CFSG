module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExtensionCores
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.MarkedParabolicPair
public import Theory.GroupTheory.SylowKernelCore
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# The point-local core inside the symplectic automorphism group

An actor preserving the point local preserves its normalizer, the point
parabolic; fixing one parabolic class fixes the two-point diagram. The
proved local SL₂ action detects every two-element in its kernel as an
inner point-local actor. This proves the point-local core identity in the
full automorphism group without an assumed diagram-preservation premise.

Source: Aschbacher–Smith F.1.12, printed p.264, applied to 11.1.5,
printed pp.765–766.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core
open Theory.SpecificGroups.SymplecticFour DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
/-- The characteristic-two symplectic group has faithful inner action. -/
theorem inner_injective : Function.Injective (MulAut.conj : Sp F →* MulAut (Sp F)) := by
  apply (MulAut.conj : Sp F →* MulAut (Sp F)).ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  have hc : g ∈ center (Sp F) := by
    rw [mem_center_iff]
    intro x
    have he := congrArg (fun a : MulAut (Sp F) => a x) hg
    change g * x * g⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  simpa only [EvenProjective.center_eq_bot,mem_bot] using hc

omit [Finite F] in
/-- Normalizing a faithful inner image preserves the original subgroup. -/
theorem preserves_of_normalizes_inner
    (U : Subgroup (Sp F)) (b : MulAut (Sp F))
    (hb : b ∈ normalizer (U.map MulAut.conj : Set _)) : U.map b.toMonoidHom = U := by
  rw [mem_normalizer_iff_map_conj_eq] at hb
  have he : (MulAut.conj b : MulAut (Sp F) →* _).comp MulAut.conj =
      MulAut.conj.comp b.toMonoidHom := by
    ext x y
    simp
  rw [Subgroup.map_map,he,←Subgroup.map_map] at hb
  exact map_injective inner_injective hb

/-- The point local itself detects the diagram type of a normalizing actor. -/
theorem preservesDiagram_of_pointLocal {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (a : MulAut (Sp F)) (ha : pointLocal.map a.toMonoidHom = pointLocal) :
    PreservesDiagram a := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  apply preservesDiagram_of_one_parabolic_class hq a
  apply Or.inl
  refine ⟨1,?_⟩
  rw [←pointLocal_normalizer hF hn,map_equiv_normalizer_eq,ha,map_one]
  exact (Subgroup.map_id _).symm

/-- Inside the full automorphism group, the point-local core survives adjoining
any subgroup preserving that local. Diagram preservation is derived locally. -/
theorem local_join_core_in_aut {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (U : Subgroup (MulAut (Sp F)))
    (hU : ∀ a ∈ U, pointLocal.map a.toMonoidHom = pointLocal) :
    ((pointLocal (F := F)).map MulAut.conj ⊔ U).pCoreIn 2 =
      ((pointLocal (F := F)).map MulAut.conj).pCoreIn 2 := by
  let K := (pointLocal (F := F)).map MulAut.conj
  have hnorm : U ≤ normalizer (K : Set (MulAut (Sp F))) := by
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq]
    have he : (MulAut.conj a).toMonoidHom.comp MulAut.conj =
        MulAut.conj.comp a.toMonoidHom := by ext x y; simp
    change K.map (MulAut.conj a).toMonoidHom = K
    dsimp only [K]
    rw [Subgroup.map_map,he,←Subgroup.map_map,hU a ha]
  apply join_pCore_eq_of_quotient_action_detection 2 K U hnorm
  intro a ha htwo hc
  have hL := preserves_of_normalizes_inner pointLocal a
    ((sup_le K.le_normalizer hnorm) ha)
  obtain ⟨l,hl⟩ := pointSL2Action_kernel_of_preservesDiagram hF hn a
    (preservesDiagram_of_pointLocal hF hn a hL) hL htwo (by
      apply MulEquiv.ext
      intro A
      obtain ⟨l,rfl⟩ := pointQuotient_surjective A
      rw [pointSL2Action_quotient]
      change pointQuotient (restrict a pointLocal hL l) = pointQuotient l
      rw [←pointLocalCoreQuotientEquiv_mk hF hn,←pointLocalCoreQuotientEquiv_mk hF hn]
      apply congrArg (pointLocalCoreQuotientEquiv hF hn)
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hh := hc ⟨MulAut.conj l.val,mem_map_of_mem _ l.property⟩
      change ⁅a,MulAut.conj l.val⁆ ∈ K.pCoreIn 2 at hh
      have he : MulAut.conj (a l.val / l.val) = ⁅a,MulAut.conj l.val⁆ := by
        ext x
        simp [commutatorElement_def,div_eq_mul_inv,mul_assoc]
      rw [←map_pCoreIn_of_injective 2 pointLocal MulAut.conj inner_injective,←he] at hh
      have hm := (Subgroup.mem_map_iff_mem inner_injective).mp hh
      exact (Subgroup.mem_map_iff_mem pointLocal.subtype_injective).mp hm)
  exact hl ▸ mem_map_of_mem MulAut.conj l.property

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core
