module
public import Theory.Representation.AlternatingSixPairedCovers.InvolutionMovement
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# Exhausting component commutators from a paired-cover budget

A quadratic actor on a marked pair has rank two and contains a component
involution. The pair already costs four dimensions for that involution.
A ratio-two bound on the whole module therefore leaves zero movement on
the quotient. Simplicity makes the component trivial on that quotient.
If the pair is component-generated, it is the full component commutator.
This argument retains all central covering kernels.

Source: Aschbacher--Smith F.9.18 and14.6.22, printed pp.325--326,1038.
-/

public section
open Representation Representation.BinaryOffender Subgroup
namespace AlternatingSixPairedCovers.Data
variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (W : Subrepresentation ρ) (C : Data W.toRepresentation)

/-- The same quadratic budget excludes further component movement outside
the marked pair; no FF classification or split-cover assertion is needed. -/
theorem exhausts_commutator
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hb : fixedCodim ρ A ≤ 2*rank A)
    (hc : subspaceCommutator ρ W.toSubmodule C.component.range = W.toSubmodule) :
    subspaceCommutator ρ ⊤ C.component.range = W.toSubmodule := by
  have hsum := fixedCodim_quotient_add_subrepresentation_le ρ W A
  obtain ⟨hr,t,ht,htA⟩ := C.quadratic_member A hA (quadratic_subrepresentation ρ W hq) (by omega)
  have htne : t ≠ 1 := by intro h; simp [h] at ht
  have hm := C.component_movement t htne
  have hmono := Submodule.finrank_mono
    (fixedSpace_antitone W.toRepresentation (zpowers_le.mpr htA))
  have hdim := fixedCodim_add_finrank W.toRepresentation A
  have hdimt := fixedCodim_add_finrank W.toRepresentation (zpowers (C.component t))
  have hz : fixedCodim W.quotientRepresentation A = 0 := by omega
  have hfix := (fixedCodim_eq_zero_iff W.quotientRepresentation A).mp hz
  let σ := W.quotientRepresentation.comp C.component
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have htker : t ∈ σ.ker := by
    apply LinearMap.ext
    intro v
    exact (show v ∈ fixedSpace W.quotientRepresentation A from hfix ▸ Submodule.mem_top) ⟨_,htA⟩
  have hk : σ.ker = ⊤ :=
    (MonoidHom.normal_ker σ).eq_bot_or_eq_top.resolve_left (fun hh => htne (mem_bot.mp (show t ∈ (⊥ : Subgroup (alternatingGroup (Fin 6))) from hh ▸ htker)))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,⟨k,rfl⟩,v,_,rfl⟩
    have hv := LinearMap.congr_fun (show σ k = 1 from show k ∈ σ.ker from hk ▸ mem_top k)
      (W.toSubmodule.mkQ v)
    exact (Submodule.Quotient.eq W.toSubmodule).mp hv
  · exact hc.symm.le.trans (subspaceCommutator_mono_left ρ le_top C.component.range)
end AlternatingSixPairedCovers.Data
