module

public import Theory.Representation.G2BinaryNondegeneratePlane.CubicDisplacement

/-!
# The unitary chief-factor obstruction in 13.3.12

Transport the literal G₂(2)′ cubic through the actual actor equivalence. Every
nontrivial binary actor module has fixed codimension at least three, excluding
a single noncentral cyclic-three chief factor, whose binary displacement is
two. This is the concrete obstruction used after the original C.1.34 block
filtration has supplied that chief-factor bound.

Source: Aschbacher–Smith 13.3.12, printed p.890.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
open Atlas.G2.Natural.BinaryNondegeneratePlane
variable {L V : Type*} [Group L] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem not_single_cubic_factor
    (e : L≃*commutator (Atlas.G2.Model (ZMod 2)))
    (σ : Representation (ZMod 2) L V) (hσ : σ≠1) (x : L)
    (hx : e x=derivedCubic)
    (hd : Representation.BinaryOffender.fixedCodim σ (zpowers x)≤2) : False := by
  let τ := σ.comp e.symm.toMonoidHom
  have hτ : τ≠1 := by
    intro he
    apply hσ
    apply MonoidHom.ext
    intro g
    have hh := congrArg (fun f : Representation (ZMod 2) (commutator (Atlas.G2.Model (ZMod 2))) V => f (e g)) he
    change σ (e.symm (e g))=1 at hh
    simpa only [e.symm_apply_apply,MonoidHom.one_apply] using hh
  have h := cubic_fixedCodim_ge_three_of_nontrivial τ hτ
  rw [Representation.BinaryOffender.fixedCodim_zpowers_eq_displacement_rank] at h hd
  have he : τ derivedCubic=σ x := by
    change σ (e.symm derivedCubic)=σ x
    rw [←hx,e.symm_apply_apply]
  rw [he] at h
  omega
end CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
