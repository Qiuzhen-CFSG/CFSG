module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.PerfectQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UniversalSimpleSocle

/-!
# Uniform roots in the finite universal apartment quotient

Apply the original-factor Cartan and root-containment proofs through
geometricMarkedIso. Both canonical roots of the same finite quotient lie
in its simple two-residual. Ordered-root generation, when supplied by the
independent coordinate producer, then gives simplicity of the whole quotient.
The numerator remains the possibly infinite universal completion; no map
from its quotient to the actual generated source carrier is asserted.

The original apartment, exchange, root quotient and Cartan intersection
premises remain explicit. Both endpoint squares and the entire overlap
are those of the supplied original marking composed with geometricMarkedIso.
This is a conditional minimal reduction, not the seven-row Lie recognition.
Source: DGS, Groups and Graphs, Part II, (3.6)–(3.7), pp.77–80,
pp.80–81 and Theorem D, p.224; Aschbacher–Smith F.1.1, p.259.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.GroupTheory.WeakBNPair.RegularTree
open Subgroup.CosetGeometry RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

universe u v
variable {G : Type v} [Group G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  {A C E : Type u} [Group A] [Group C] [Group E] [Finite A] [Finite E]
  (α : RankTwoAmalgam A C E)
  (hL : Function.Injective α.left) (hR : Function.Injective α.right)
  (h : HypothesisF11 L S) (hp : ∀ i, Group.IsPerfect (L i))
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) α)
  (T : Set (SourceVertex α)) (n : ℕ)
  (hbase : ∀ i, base (Universal.cosetFamily α) i ∈ T)
  (hdeg : TwoNeighborsIn (sourceGraph α) T)
  (htrans : BasedPathTransitive (X := α.Universal) (sourceGraph α) (n+1))
  (hline : NoBranchingIn (sourceGraph α) T)
  (hunique : ApartmentsUnique (X := α.Universal) (sourceGraph α) T (n+1))
  (hexchange : ChosenApartmentExchange (X := α.Universal) (sourceGraph α) T n)
  (hn : 1 < n)
  (hcore : ((Universal.left α).range ⊓ (Universal.right α).range).normalCore = ⊥)
  (roots : RootQuotientData (quotientMap α T n))
  (hB : roots.B = originalMiddle α)
  (hP : ∀ i, roots.endpoint i = Universal.cosetFamily α i)
  (hBN : roots.B.map (quotientMap α T n) ⊓ roots.N.map (quotientMap α T n) =
    (roots.B ⊓ roots.N).map (quotientMap α T n))

local notation "Q" => recognitionQuotient α T n hL hR hbase hdeg htrans hline
  hunique hexchange hn hcore roots hB hP hBN

include h hp e in
/-- Both actual simple roots of the geometric quotient lie in its same two-residual. -/
theorem geometric_quotient_roots_le_twoResidual
    (split : SplitData (Q).tits) (i : Fin 2) :
    RootCoordinates.simpleRoot Q split i ≤ pResidual 2 (QuotientGroup α T n) :=
  MarkedLocal.simpleRoot_le_twoResidual Q
    (e.trans (geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      roots hB hP hBN)) h hp split i

include h hp e in
/-- The whole geometric quotient is simple once its canonical Weyl roots
generate U; all maps are those of the same universal apartment construction. -/
theorem geometric_quotient_isSimple_of_weyl_roots
    (split : SplitData (Q).tits)
    (hroots : split.U ≤ ⨆ (i : Fin 2) (a : (Q).tits.N),
      RootCoordinates.rightConjugate (RootCoordinates.simpleRoot Q split i)
        a) :
    IsSimpleGroup (QuotientGroup α T n) :=
  MarkedLocal.isSimple_of_weyl_roots Q
    (e.trans (geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      roots hB hP hBN)) h hp split hroots

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
