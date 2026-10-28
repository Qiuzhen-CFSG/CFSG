module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairResidual
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedOrbitSpan
public import Theory.Representation.ResidualMovedGeneration
/-!
# The natural first-axis residual and its two fixed lines

Two elementary transvections generate the moved space. The binary
residual preserves this generation, and an actual residual conjugator
makes two Sylow fixed lines span that space. The same calculation holds
on the literal first axis of any equivariant quotient, without a split
module assumption.
Source: Aschbacher–Smith B.6.10, printed p.117.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
open QuasisimpleSource
variable (F : BinaryField)
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F.Carrier
local notation "V" => Fin 2 → F.Carrier
local notation "N" => linearNatural F 2
private theorem natural_full_moved : subspaceCommutator N ⊤ ⊤ = ⊤ := by
  apply top_unique
  intro v _
  let a : D := Matrix.SpecialLinearGroup.transvection zero_ne_one 1
  let b : D := Matrix.SpecialLinearGroup.transvection one_ne_zero 1
  have ha : N a ![0,v 0] - ![0,v 0] ∈ subspaceCommutator N ⊤ ⊤ :=
    Submodule.subset_span ⟨a,mem_top _,![0,v 0],Submodule.mem_top,rfl⟩
  have hb : N b ![v 1,0] - ![v 1,0] ∈ subspaceCommutator N ⊤ ⊤ :=
    Submodule.subset_span ⟨b,mem_top _,![v 1,0],Submodule.mem_top,rfl⟩
  have he : (N a ![0,v 0] - ![0,v 0]) + (N b ![v 1,0] - ![v 1,0]) = v := by
    change (specialLinearNatural 2 a ![0,v 0] - ![0,v 0]) +
      (specialLinearNatural 2 b ![v 1,0] - ![v 1,0]) = v
    rw [Representation.OneCohomology.SLHigherNatural.action_transvection,Representation.OneCohomology.SLHigherNatural.action_transvection]
    ext i
    fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail]

  exact he ▸ (subspaceCommutator N ⊤ ⊤).add_mem ha hb

theorem natural_residual_moved : subspaceCommutator N ⊤ (pResidual 2 D) = ⊤ := by
  have h := commutator_pResidual_eq_top N ⊤ (natural_full_moved F)
  have he : (pResidual 2 (⊤ : Subgroup D)).map (⊤ : Subgroup D).subtype = pResidual 2 D :=
    map_pResidual_of_surjective 2 _ (fun x => ⟨⟨x,mem_top _⟩,rfl⟩)
  rwa [he] at h

private theorem natural_sylow_codim (P : Sylow 2 D) :
    fixedCodim N (P : Subgroup D) = Module.finrank (ZMod 2) F.Carrier := by
  let Q := P.mapSurjective (f := (topEquiv (G := D)).symm.toMonoidHom)
    (topEquiv (G := D)).symm.surjective
  have hh := SL2NaturalOffenders.Ratios.sylowImage_fixedCodim (⊤ : Subgroup D) topEquiv N (fun _ _ => rfl) Q
  have he : (Q : Subgroup (⊤ : Subgroup D)).map (⊤ : Subgroup D).subtype = P := by
    change ((P : Subgroup D).map (topEquiv (G := D)).symm.toMonoidHom).map _ = _
    rw [Subgroup.map_map]
    exact Subgroup.map_id _
  rwa [he] at hh

theorem exists_residual_fixed_line_span (P : Sylow 2 D) :
    ∃ g ∈ pResidual 2 D,
      fixedSpace N (P : Subgroup D) ⊔ (fixedSpace N (P : Subgroup D)).map (N g) = ⊤ := by
  obtain ⟨g,hg,hgen⟩ := Matrix.SpecialLinearGroup.exists_residual_conjugate_sylow_image_sup_eq_top P
    (MonoidHom.id D) Function.surjective_id
  simp only [Subgroup.map_id] at hgen
  have hd : fixedCodim N (⊤ : Subgroup D) = 2 * Module.finrank (ZMod 2) F.Carrier := by
    have hz : fixedSpace N (⊤ : Subgroup D) = ⊥ := by
      ext v
      change (∀ a : (⊤ : Subgroup D), N a v = v) ↔ v = 0
      constructor
      · intro hv
        apply (ExtensionConsequences.linearNatural_invariants F (by decide)).le
        exact fun g => hv ⟨g,mem_top _⟩
      · rintro rfl g
        exact map_zero _
    have hh := fixedCodim_add_finrank N (⊤ : Subgroup D)
    rw [hz,finrank_bot,add_zero] at hh
    simpa [Module.finrank_pi_fintype,mul_comm] using hh
  have hs := fixedSpace_sup_eq_top_of_codim_sum N (P : Subgroup D)
    ((P : Subgroup D).map (MulAut.conj g).toMonoidHom) ⊤ hgen.ge (by
      rw [fixedCodim_map_conj,natural_sylow_codim,hd]; omega)
  refine ⟨g,hg,?_⟩
  have hm : (fixedSpace N (P : Subgroup D)).map (N g) =
      fixedSpace N ((P : Subgroup D).map (MulAut.conj g).toMonoidHom) := by
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩
      intro b
      obtain ⟨a,ha,hba⟩ := b.property
      change N b (N g w) = N g w
      rw [←hba]
      change N (g * a * g⁻¹) (N g w) = N g w
      rw [map_mul,map_mul]
      simp only [Module.End.mul_apply]
      have hgi : N g⁻¹ (N g w) = w := by
        rw [← Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
      rw [hgi]
      exact congrArg (N g) (hw ⟨a,ha⟩)
    · intro hv
      let w := N g⁻¹ v
      have hw : w ∈ fixedSpace N (P : Subgroup D) := by
        intro a
        have hmem : g*(a:D)*g⁻¹ ∈ (P : Subgroup D).map (MulAut.conj g).toMonoidHom :=
          ⟨a,a.property,rfl⟩
        have hh := hv ⟨_,hmem⟩
        change N (g*(a:D)*g⁻¹) v = v at hh
        have hh' := congrArg (fun x => N g⁻¹ x) hh
        rw [map_mul,map_mul] at hh'
        simp only [Module.End.mul_apply] at hh'
        change N (a:D) w = w
        have hc : g⁻¹ * (g * (a:D) * g⁻¹) = (a:D) * g⁻¹ := by group
        have hgi (z : V) : N g⁻¹ (N g z) = z := by
          rw [← Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
        rw [hgi] at hh'
        exact hh'
      refine ⟨w,hw,?_⟩
      change N g (N g⁻¹ v) = v
      rw [← Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  rwa [hm]

variable {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
theorem first_axis_moved_map
    (ρ : Representation (ZMod 2) H X) (j : D →* H)
    (f : X →ₗ[ZMod 2] (V × V)) (hf : Function.Surjective f)
    (he : ∀ g v, f (ρ (j g) v) = (N g (f v).1,(f v).2)) :
    (subspaceCommutator ρ ⊤ ((pResidual 2 D).map j)).map f =
      (⊤ : Submodule (ZMod 2) V).prod ⊥ := by
  let τ : Representation (ZMod 2) D (V × V) := Representation.prod N (Representation.trivial (ZMod 2) D V)
  have ht : subspaceCommutator τ ⊤ (pResidual 2 D) =
      (⊤ : Submodule (ZMod 2) V).prod ⊥ := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,v,hv,rfl⟩
      exact ⟨Submodule.mem_top,sub_self v.2⟩
    · rintro ⟨v,w⟩ ⟨_,hw⟩
      have hw' : w = 0 := hw
      subst w
      let C := (subspaceCommutator τ ⊤ (pResidual 2 D)).comap
        (LinearMap.inl (ZMod 2) V V)
      have hc : subspaceCommutator N ⊤ (pResidual 2 D) ≤ C := by
        apply Submodule.span_le.mpr
        rintro _ ⟨g,hg,u,hu,rfl⟩
        change (N g u - u,0) ∈ subspaceCommutator τ ⊤ (pResidual 2 D)
        have hh : τ g (u,0) - (u,0) ∈ subspaceCommutator τ ⊤ (pResidual 2 D) :=
          Submodule.subset_span ⟨g,hg,(u,0),Submodule.mem_top,rfl⟩
        have heq : τ g (u,0) - (u,0) = ((N g u - u,0) : V × V) := by
          simp [τ]
        rw [heq] at hh
        exact hh
      rw [natural_residual_moved] at hc
      exact hc Submodule.mem_top
  have h₁ := subspaceCommutator_map_embedding τ (ρ.comp j) (MonoidHom.id D) f
    (fun g v => (he g v).symm) (pResidual 2 D) ⊤
  rw [Submodule.map_top,LinearMap.range_eq_top.mpr hf,Subgroup.map_id,ht] at h₁
  have h₂ := subspaceCommutator_map_embedding (ρ.comp j) ρ j
    (LinearMap.id : X →ₗ[ZMod 2] X) (fun _ _ => rfl) (pResidual 2 D) ⊤
  simp only [Submodule.map_id] at h₂
  rw [h₂] at h₁
  exact h₁.symm
end CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
