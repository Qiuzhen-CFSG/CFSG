module

public import CFSG.Quasithin.MainConverse.ReeSections.MaximalCover.Exhaustion.Branches
public import Theory.GroupTheory.CComponent.SimpleNormalCentralizer
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal

/-!
# Reduction of the simple-normal branch of Ree exhaustion

A nontrivial relative centralizer supplies two distinct commuting C-components,
so the multiple-component branch applies. With trivial relative centralizer,
recognition of the supplied simple subgroup and the three overgroup calculations
give the PGU₃, Sp₄, and full Ree subfield alternatives. The subfield calculation
retains the prime-power field relation, including the full group at parameter zero.

This is a conditional assembly theorem. The component branch, socle recognition,
and all three concrete overgroup calculations remain proof obligations; this
module does not yet export `simpleNormalMaximals : SimpleNormalMaximals`.

Source: Malle, J. Algebra 139 (1991), 52–69, and the unconditional list inside
the proof of Theorem 5 of Himstedt–Nguyen–Tiep, arXiv:0910.4758, pp.2–3.
-/

public section

namespace CFSG.Quasithin.MainConverse.ReeSections

open Subgroup ReeF4.MaximalSubgroups.SimpleNormal

/-- Reduce the simple-normal branch to the existing multiple-component
branch and independent intrinsic recognition and overgroup calculations.
Every additional premise remains explicit until its producer is proved. -/
theorem simpleNormalMaximals_of_recognition_and_overgroups
    (hpair : CommutingComponentMaximals) (hrec : SocleRecognition)
    (hU : UnitaryOvergroups) (hSp : SymplecticOvergroups)
    (hSub : SubfieldOvergroups) : SimpleNormalMaximals := by
  intro m hm M hM hsolv hR S hSn hSs hSa
  let := hSn
  let := hSs
  by_cases hC : centralizer (S : Set M) = ⊥
  · cases hrec m hm M hM hsolv hR S hSn hSs hSa hC with
    | unitary F J hcard hconj e =>
        obtain ⟨N, hN, ⟨f⟩, hindex⟩ :=
          hU m hm M hM hsolv hR S hSn hSs hSa hC F J hcard hconj e
        let := hN
        exact .projectiveUnitary F J hcard hconj N f hindex
    | symplectic F hcard e =>
        exact .symplectic F hcard S e
          (hSp m hm M hM hsolv hR S hSn hSs hSa hC F hcard e)
    | reeDerived k hlt hdiv e =>
        obtain ⟨a, ha, hfield, ⟨f⟩⟩ :=
          hSub m hm M hM hsolv hR S hSn hSs hSa hC k hlt hdiv e
        exact .subfield_of_fieldSize_pow_eq ha hfield f
  · obtain ⟨K, hS, hK, hne, hcomm⟩ :=
      exists_commuting_component_of_simple_normal_centralizer_ne_bot S hR hSa hC
    exact hpair m hm M hM hsolv hR S K hS hK hne hcomm

end CFSG.Quasithin.MainConverse.ReeSections
