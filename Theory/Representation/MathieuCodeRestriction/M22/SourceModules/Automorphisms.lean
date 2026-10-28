module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms.Compatibility
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Pairing

/-!
# The literal M22 modules as representations of Aut(M22)

Transport along the genuine degree-24 setwise-pair equivalence extends both
native ten-dimensional actions. Its marked conjugation equation proves that
restriction along the inner automorphisms gives exactly the published actions.
The original coordinate duality remains equivariant after this transport.

Source: Aschbacher--Smith, H.13.1, printed p.395.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu
namespace MathieuCode

def m22AutCodeRepresentation : Representation (ZMod 2) (MulAut M22) M22Code :=
  m22OuterCodeRepresentation.comp m22PairStabilizerEquivAut.symm.toMonoidHom

def m22AutCocodeRepresentation : Representation (ZMod 2) (MulAut M22) M22Cocode :=
  m22OuterCocodeRepresentation.comp m22PairStabilizerEquivAut.symm.toMonoidHom

@[simp] theorem m22AutCodeRepresentation_pair (g : m22PairStabilizer) (v : M22Code) :
    m22AutCodeRepresentation (m22PairStabilizerEquivAut g) v =
      m22OuterCodeRepresentation g v := by
  change m22OuterCodeRepresentation (m22PairStabilizerEquivAut.symm
    (m22PairStabilizerEquivAut g)) v = _
  rw [MulEquiv.symm_apply_apply]

@[simp] theorem m22AutCocodeRepresentation_pair (g : m22PairStabilizer) (v : M22Cocode) :
    m22AutCocodeRepresentation (m22PairStabilizerEquivAut g) v =
      m22OuterCocodeRepresentation g v := by
  change m22OuterCocodeRepresentation (m22PairStabilizerEquivAut.symm
    (m22PairStabilizerEquivAut g)) v = _
  rw [MulEquiv.symm_apply_apply]

@[simp] theorem m22AutCodeRepresentation_inner (g : M22) (v : M22Code) :
    m22AutCodeRepresentation (MulAut.conj g) v = m22CodeRepresentation g v := by
  rw [← m22PairStabilizerEquivAut_inner, m22AutCodeRepresentation_pair,
    m22OuterCodeRepresentation_restrict]

@[simp] theorem m22AutCocodeRepresentation_inner (g : M22) (v : M22Cocode) :
    m22AutCocodeRepresentation (MulAut.conj g) v = m22CocodeRepresentation g v := by
  rw [← m22PairStabilizerEquivAut_inner, m22AutCocodeRepresentation_pair]
  rfl

theorem m22AutCodeCocodeDuality_equivariant (g : MulAut M22) (v : M22Code) :
    m22CodeCocodeDuality (m22AutCodeRepresentation g v) =
      m22AutCocodeRepresentation.dual g (m22CodeCocodeDuality v) := by
  apply LinearMap.ext
  intro u
  have h := LinearMap.congr_fun
    (m22CodeCocodeDuality_equivariant (m22PairStabilizerEquivAut.symm g) v) u
  change m22CodeCocodeDuality (m22OuterCodeRepresentation
    (m22PairStabilizerEquivAut.symm g) v) u =
      m22CodeCocodeDuality v (m22OuterCocodeRepresentation
        (m22PairStabilizerEquivAut.symm g⁻¹) u)
  rw [map_inv]
  exact h

end MathieuCode
