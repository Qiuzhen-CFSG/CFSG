module

public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.ComponentGeometry
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.BridgeReduction
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.ChartTransport
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Endgame
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.FarExclusion
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.FarTransitivity
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.LineViews
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.LineViewsPolar
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.ResidueOvals
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.OctadOverlap

/-!
# AS91 source cycle-base development

The single earlier-source `SourceCycleBase.Input` retains the literal coset
geometry and both native residue markings. Sections (1.2)–(1.4) are proved in
nonabelian walk closure. The actual filtration satisfies B1; its level-one
pairs have connected common-neighbor graphs by (7.5). The visible-line
clique/coclique calculations are now identified with singular pencils and
ovals in the actual binary symplectic residue. The native octad-overlap
exclusion is transported to the literal point residue; the original-involution
endgame is proved.

The native (3.8) far-line orbit is proved by a checked forest certificate,
with coverage from the independently proved trio count. Its literal Todd
transport proves `Input.FarLineTransitive` and the fixed-neighbor criterion
(7.8), without adding fields to `Input`. Native (3.11.1) and a literal
(3.13.2) representative are now proved. The earlier-source orbital transitivity
transports the latter to every ambient δ₄ pair under the same Todd marking.
These calculations produce an oval inside the chosen common-neighbor
component and discharge the far branch of B2. ComponentClose also implies
the source's R₁ distance bound (7.6.1). The δ₃ plane-hitting assertion (7.4.2) follows from a checked common
δ₁ line, the actual core action, and oval–pencil incidence. A second checked
forest proves native (3.11.2) on all 1771 sextets. The native outside-line
pencil gives the two source ovals and the bound of seven in the associated
plane; the disc-or-nine lemma then proves its actual six-point clique and
disc (7.4.1), retaining the originally selected common-neighbor component.

Consequently `triangulable_of_input` and `source_isBase` prove (7.9) and the
base of the literal ambient system with only the unchanged earlier-source
Input. The marked Mathieu application uses the same original central
involution, whole-module marking, and cubic quotient. Construction of every
Input field and the section 8 compatible comparison remain with the original
source-recognition producer; no unconditional J₄ recognition is asserted.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄* (1991), §§1–3,7.
-/
