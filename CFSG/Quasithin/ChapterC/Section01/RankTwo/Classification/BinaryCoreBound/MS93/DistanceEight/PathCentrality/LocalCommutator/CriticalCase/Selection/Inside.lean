module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Displacement

/-!
# Inside-B selection from the two representation steps

The actual quotient-centralizer and escaping spans are constructed in
Conjugates. Containment of the escaping span gives the order-two bound in
Displacement. Once the dual-module inclusion and the marked natural-section
recognition are supplied, this bound contradicts the no-natural-section
branch and selects one conjugator with both required properties.

The two representation implications below remain explicit premises. This
conditional assembly does not prove the inside-B source branch until its
owner discharges them, including the actual action, kernel and splitting.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), claim (2), p.891;
the two representation inputs are the uses of (1.5) and (1.6), pp.843--847.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The precise inside-branch consumer, retaining the two unproved
representation implications as explicit inputs. -/
theorem exists_conjugate_of_representation_inputs
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c e : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hB : ⁅Z R a, Q R c⁆ ≤ B R c (geometry.Z_normal c))
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (hnone : ¬ HasNaturalSection R a c)
    (htriple : ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c)
    (p : CriticalPath R geometry c e)
    (hdual : ∀ x : stabilizer R c, (x : FreeAmalgam R) ∈ ⁅Z R a, Q R c⁆ →
      (x : FreeAmalgam R) ∈ Z R c ⊔ fixedCore R c)
    (hrecognition : ∀ x : stabilizer R c,
      (x : FreeAmalgam R) ∈ ⁅Z R a, Q R c⁆ →
      (x : FreeAmalgam R) ∉ fixedCore R c →
      (x : FreeAmalgam R) ∈ Z R c ⊔ fixedCore R c →
      ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c →
      (Z R c).relIndex ⁅escapingSpan a c e x, Z R e⁆ ≤ 2 →
      HasNaturalSection R a c) :
    ∃ g ∈ stabilizer R c,
      ¬ Z R (act R g a) ≤ Q R (p.walk.getVert (p.walk.length - 2)) ∧
      ⁅⁅Z R (act R g a), Q R c⁆, Z R e⁆ ≠ ⊥ := by
  obtain ⟨x, hx, hnot, _⟩ := exists_displacement_point common ha hc hd hB hn
  apply exists_conjugate_of_escaping_span p (by omega) x hx
  intro htrap
  exact hnone (hrecognition x hx hnot (hdual x hx) htriple
    (escapingSpan_displacement_index_le_two common hb hd p x htrap))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside
