module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceRecognition

/-!
# Recognition of a finite simple group of J₂-type

`J2Recognition.recognition` proves the actual simple-source specialization of
Aschbacher–Smith I.4.7(1), printed p.418: the original J₂-type condition gives
an equivalence to the concrete ATLAS Hall–Janko carrier. The source local maps,
edge compatibilities and target cycle base are all proved. The universal
conditional local-geometry interfaces remain publicly re-exported.

The proof follows the uniqueness-system construction of Aschbacher,
*Sporadic Groups* (1994), §§37 and 47. A checked finite triangle reduction
supplies the target cycle base, extending the inverse local maps to the source.
The existing source order calculation then proves this surjection bijective.
-/
