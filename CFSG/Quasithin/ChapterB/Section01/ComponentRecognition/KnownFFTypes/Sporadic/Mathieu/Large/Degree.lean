module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large.GM02.Reduction

/-!
# Assembly of the M23 and M24 degree-eleven sieve

The intrinsic generation calculations bound the original binary degree,
including arbitrary quasisimple covers. Applying the low-degree spectra to
the actual generalized Fitting subgroup then gives eleven, except for the
M24 degree-forty-four alternative. Its involution displacement contradicts
the bound twelve already proved for the source action.

The named independent calculations remain explicit: these are conditional
assemblies, not completed assertions of GM02 Theorem 6.6 or Table 6.7.
Source: GM02 Proposition 5.1, manuscript pp.16--17; Theorem 6.6, p.21;
Aschbacher--Smith K.4, printed p.457.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu
open Subgroup Theory.GroupTheory Representation Sporadic.Mathieu
universe u v

/-- Generation and the independent small spectrum imply the exact M23 source contract. -/
theorem m23DegreeEleven_of_gm02_inputs
    (hg : GM02.InvolutionGeneration M23 3) (hs : GM02.M23SmallSpectrum.{u,v}) :
    M23DegreeEleven.{u,v} := by
  intro G _ _ V _ _ _ ρ h he
  obtain ⟨e⟩ := he
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  exact hs (ρ.comp (generalizedFitting G).subtype)
    (h.faithful.comp Subtype.val_injective) h.irreducible ⟨e⟩
    (GM02.m23_degree_le_twenty_four hg ρ h e)

/-- The M24 spectrum and displacement calculation finish the source degree sieve. -/
theorem m24DegreeEleven_of_gm02_inputs
    (hg : GM02.InvolutionGeneration M24 4) (hs : GM02.M24SmallSpectrum.{u,v})
    (hmoved : GM02.M24Degree44Displacement.{u,v}) : M24DegreeEleven.{u,v} := by
  intro G _ _ V _ _ _ ρ h he
  obtain ⟨e⟩ := he
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  rcases hs (ρ.comp (generalizedFitting G).subtype)
    (h.faithful.comp Subtype.val_injective) h.irreducible ⟨e⟩
    (GM02.m24_degree_le_forty_eight hg ρ h e) with hd | hd
  · exact hd
  · exact (GM02.m24_degree_ne_forty_four hmoved ρ h e hd).elim

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu
