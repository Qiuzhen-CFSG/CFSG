module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.CoreInvolutionFusion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.OutsideInvolutionFusion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Basic

/-!
# The §46 fusion package for the J₂ local census

Every core involution is already proved ambient-conjugate to z. Thompson's
mixed-dihedral argument places an involution of the other ambient class in
C_G(z); this representative is consequently outside the core. The local
minus-extraspecial A₅ extension theorem makes the outside involutions a single
class inside C_G(z), so none of them can be fused to z. This proves the exact
core-fusion equivalence and the weak-closure assertion from `Seed` alone.

The sources are Aschbacher, *Sporadic Groups* (1994), 46.1(2), printed p.251;
46.11, printed p.255; and the weak-closure clause of 46.14(5)(b), printed p.258.
The local theorem uses the actual core and quotient isomorphisms from `HTypeAt`;
the two-class separation uses `Seed.classes`. Neither argument needs ambient
simplicity or recognition. The earlier conditional APIs are retained below.
`localCensus_of_count` supplies the literal `LocalCensus` consumer with both
fusion premises discharged, retaining only the independent count 960 from
47.1, printed pp.259–260.
-/

public section

open Subgroup Theory.GroupTheory
open Theory.GroupTheory.ExtraspecialCentralizerSimplicity

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry

variable {G : Type*} [Group G] [Finite G]

/-- An involution in the other ambient class never belongs to the local core. -/
theorem OtherInvolution.not_mem_core {D : Seed G} {t : G}
    (ht : OtherInvolution D t) : t ∉ ambientCore D.z :=
  fun htQ => ht.2 (D.localType.core_involution_isConj htQ ht.1)

/-- Two ambient classes and the local outside orbit separate core and outside fusion. -/
theorem core_fusion_of_outside_fusion (D : Seed G)
    (hout : ∀ u v : involutionCentralizer D.z,
      orderOf u = 2 → orderOf v = 2 →
      (u : G) ∉ ambientCore D.z → (v : G) ∉ ambientCore D.z → IsConj u v)
    {u : G} (huH : u ∈ involutionCentralizer D.z) (hu : orderOf u = 2) :
    IsConj D.z u ↔ u ∈ ambientCore D.z := by
  refine ⟨?_, fun huQ => D.localType.core_involution_isConj huQ hu⟩
  intro hzu
  by_contra huQ
  obtain ⟨t, ht, hzt⟩ := exists_commuting_other D
  let tH : involutionCentralizer D.z := ⟨t, mem_centralizer_singleton_iff.mpr hzt.symm.eq⟩
  let uH : involutionCentralizer D.z := ⟨u, huH⟩
  have htH : orderOf tH = 2 := (orderOf_coe tH).symm.trans ht.1
  have huH2 : orderOf uH = 2 := (orderOf_coe uH).symm.trans hu
  exact ht.2 (hzu.trans ((involutionCentralizer D.z).subtype.map_isConj
    (hout uH tH huH2 htH huQ ht.not_mem_core)))

/-- The same local orbit gives the weak-closure clause of source 46.14(5)(b). -/
theorem weakClosure_eq_core_of_outside_fusion (D : Seed G)
    (hout : ∀ u v : involutionCentralizer D.z,
      orderOf u = 2 → orderOf v = 2 →
      (u : G) ∉ ambientCore D.z → (v : G) ∉ ambientCore D.z → IsConj u v) :
    weakClosure D.z (involutionCentralizer D.z) = ambientCore D.z := by
  apply D.localType.not_hasFusionOutsideCore_iff.mp
  rintro ⟨u, huH, hzu, huQ⟩
  have hu : orderOf u = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hzu
    exact (congrArg orderOf hg).symm.trans
      (((MulAut.conj g).orderOf_eq D.z).trans D.localType.involution)
  exact huQ ((core_fusion_of_outside_fusion D hout huH hu).mp hzu)

/-- Actual application to the existing census, with its remaining local inputs explicit. -/
theorem localCensus_of_outside_fusion_and_count (D : Seed G)
    (hout : ∀ u v : involutionCentralizer D.z,
      orderOf u = 2 → orderOf v = 2 →
      (u : G) ∉ ambientCore D.z → (v : G) ∉ ambientCore D.z → IsConj u v)
    (hcount : ∀ t : G, OtherInvolution D t → sourceCount D.z t D.z = 960) :
    LocalCensus D where
  core_fusion := fun _ huH hu => core_fusion_of_outside_fusion D hout huH hu
  outside_fusion := hout
  count_at_z := hcount

/-- Source 46.11 for the literal centralizer and core of the recognition seed. -/
theorem outside_involutions_isConj (D : Seed G)
    (u v : involutionCentralizer D.z) (hu : orderOf u = 2) (hv : orderOf v = 2)
    (huQ : (u : G) ∉ ambientCore D.z) (hvQ : (v : G) ∉ ambientCore D.z) :
    IsConj u v :=
  D.localType.outside_involutions_isConj u v hu hv huQ hvQ

/-- In the two-class branch, the local involutions fused to z are exactly those
in the core. Both local fusion inputs are proved from the source hypotheses. -/
theorem core_fusion (D : Seed G) {u : G}
    (huH : u ∈ involutionCentralizer D.z) (hu : orderOf u = 2) :
    IsConj D.z u ↔ u ∈ ambientCore D.z :=
  core_fusion_of_outside_fusion D (outside_involutions_isConj D) huH hu

/-- The weak-closure clause of source 46.14(5)(b), with no extra fusion premise. -/
theorem weakClosure_eq_core (D : Seed G) :
    weakClosure D.z (involutionCentralizer D.z) = ambientCore D.z :=
  weakClosure_eq_core_of_outside_fusion D (outside_involutions_isConj D)

/-- The §46 fusion package discharges both fusion fields of the actual census.
Only the independent first pair count of 47.1 remains for its source owner. -/
theorem localCensus_of_count (D : Seed G)
    (hcount : ∀ t : G, OtherInvolution D t → sourceCount D.z t D.z = 960) :
    LocalCensus D where
  core_fusion := fun _ huH hu => core_fusion D huH hu
  outside_fusion := outside_involutions_isConj D
  count_at_z := hcount

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry
