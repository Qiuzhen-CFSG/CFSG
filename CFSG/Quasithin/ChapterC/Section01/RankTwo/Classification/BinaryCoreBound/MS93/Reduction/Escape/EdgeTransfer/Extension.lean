module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Extension.Action
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Extension.Marking
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Extension.Residual

/-!
# Realizing the neighboring binary extension

`Extension.Groups` constructs the literal neighboring carrier, its relative
normal quotient, elementary structure, and local-kernel descent. The genuine
SL3(2) action, its Z_alpha subrepresentation, the quotient involution fixing
the displacement, and the exact natural-image preimage are constructed in
`Extension.Action`.

`Extension.Marking` identifies the actual natural submodule equivariantly;
`Extension.Residual` proves trivial action on its quotient and that the whole
quotient has zero fixed space. Applying the checked nonsplit cocycle calculation
to the involution in the image of Q_delta puts every displacement vector in
the natural image. Its preimage is U_alpha D_alpha, proving the first
unequal-kernel step of (4.2)(i) from the source hypotheses alone.

Adapted from the checked marked-extension proof in
`DistanceFour/Early/EdgeStructure/Containment/Transfer/SpanBound/Extension`.
The general construction uses the source and module data and b > 2.

Source: Meierfrankenfeld--Stellmacher (1993), (1.5)(i) and (4.2)(i),
printed pp.843 and 882.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer.Extension
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Conditional assembly on the actual amalgam quotient. The marking, quotient
triviality, and fixed-space premises must be discharged to obtain the source step. -/
theorem neighbor_le_natural_sup_fixedCore_of_module_facts
    (hlarge : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b) (hne : Q R a ≠ Q R d)
    (A : Action a b d) (hmark : A.HasNaturalMarking)
    (htriv : letI := A.normal; letI := A.elementary
      Representation.OneCohomology.HasTrivialQuotient A.natural)
    (hfixed : letI := A.normal; letI := A.elementary
      Representation.OneCohomology.fixed A.representation = ⊥) :
    ⁅Z R d,Q R b⁆ ≤ U R a ⊔ fixedCore R a := by
  let := A.normal
  let := A.elementary
  obtain ⟨marking,e,he⟩ := hmark
  obtain ⟨g,hg,hgne,hgfix⟩ := fixed_involution_exists hlarge modules a b d ha hab hdb hne A
  intro x hx
  let xH : carrier a b d := ⟨x,
    (show layer a b d ≤ carrier a b d from le_sup_left)
      ((show ⁅Z R d,Q R b⁆ ≤ layer a b d from le_sup_left) hx)⟩
  have hv := DistanceFour.Early.Containment.Transfer.SpanBound.fixed_involution_mem_natural_sup_fixed
    A.representation A.natural
    marking e he htriv g hg hgne
    (Additive.ofMul (QuotientGroup.mk' ((fixedCore R a).subgroupOf (carrier a b d)) xH))
    (hgfix xH hx)
  rw [hfixed, sup_bot_eq] at hv
  exact (natural_preimage modules a b d ha A xH).mp hv

/-- The first unequal-kernel step of MS93 (4.2)(i), printed p.882.
The neighboring B-containment constructs the literal quotient action; its
natural marking, trivial quotient action, and zero fixed space are all proved
from the source data. No splitting of the binary extension is assumed. -/
theorem neighbor_le_natural_sup_fixedCore
    (hlarge : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b) (hne : Q R a ≠ Q R d)
    (hB : ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ⁅Z R d,Q R b⁆ ≤ U R a ⊔ fixedCore R a := by
  obtain ⟨A⟩ := action_nonempty hlarge modules a b d ha hab hdb hB
  exact neighbor_le_natural_sup_fixedCore_of_module_facts hlarge modules a b d ha hab hdb hne A
    (action_hasNaturalMarking modules a b d ha hab hdb hB A)
    (action_hasTrivialQuotient hlarge modules a b d ha hab hB A)
    (action_fixed_eq_bot hlarge modules a b d ha hab hB A)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer.Extension

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The neighboring natural bound from the source module data and b > 2.
This discharges the marked-extension premise in the general (4.2)(i) assembly. -/
theorem neighborNaturalBound (hlarge : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) : NeighborNaturalBound geometry := by
  intro a b d ha hab hdb hne hB
  exact Extension.neighbor_le_natural_sup_fixedCore hlarge modules a b d ha hab hdb hne hB

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer
