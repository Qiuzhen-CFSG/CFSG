module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Transfer.Midpoint.Basic

/-!
# The remaining source inputs for midpoint edge centrality

These two propositions describe separate steps in the second MS93 (4.6.6).
They are explicit conditional interfaces, with no constructors here.
`ConjugateEscape` is the conclusion of the first paragraph: a conjugate
plane different from the original cannot have its endpoint kernel contain
the original radius group. The already proved splitting theorem in Basic
then gives the two complementary lines of that conjugate plane.

`CenterSpan` is the subsequent generation and symmetry output, retaining
one actual element of the midpoint edge stabilizer and its fixed index on
the literal edge Z-layer. Its producer may assume `ConjugateEscape`; the
parent must discharge both before claiming midpoint centrality.

The printed second index formula on p.904 reads q, while the first reads
q squared. The contract below retains the subgroup product before that
numeric comparison. Basic derives the needed index four from the genuine
marked natural decomposition, rather than adopting either printed exponent
as an additional premise.

Source: Meierfrankenfeld--Stellmacher (1993), pp.903--904, from the second
(4.6.6) through the fixed-index contradiction.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The first conjugate comparison still to be established from the source. -/
def ConjugateEscape (geometry : Geometry R) : Prop :=
  ∀ (d e c b : Vertex R) (hd : color R d = false),
    CriticalPair R d e (geometry.exists_critical d hd) →
    (cosetGraph R).dist d c = 2 → (cosetGraph R).dist c e = 2 →
    Adjacent R d b → Adjacent R c b →
    ⁅V R d, V R d⁆ ≤ (center (stabilizer R d)).map (stabilizer R d).subtype →
    ¬ ⁅Z R d, Q R b⁆ ≤ (center (stabilizer R c)).map (stabilizer R c).subtype →
    ∀ h : FreeAmalgam R, h ∈ stabilizer R c → h ∈ stabilizer R b →
      ⁅Z R (act R h d), Q R b⁆ ≠ ⁅Z R d, Q R b⁆ →
      ¬ V R d ≤ Q R (act R h d)

/-- The generation and symmetry witness, before the final index contradiction. -/
def CenterSpan (geometry : Geometry R) : Prop :=
  ∀ (d e c b : Vertex R) (hd : color R d = false),
    CriticalPair R d e (geometry.exists_critical d hd) →
    (cosetGraph R).dist d c = 2 → (cosetGraph R).dist c e = 2 →
    Adjacent R d b → Adjacent R c b →
    ⁅V R d, V R d⁆ ≤ (center (stabilizer R d)).map (stabilizer R d).subtype →
    ¬ ⁅Z R d, Q R b⁆ ≤ (center (stabilizer R c)).map (stabilizer R c).subtype →
    ∃ h : FreeAmalgam R, h ∈ stabilizer R c ∧ h ∈ stabilizer R b ∧
      Z R b =
        (Z R b ⊓ (center (stabilizer R d)).map (stabilizer R d).subtype) ⊔
        (Z R b ⊓ (center (stabilizer R (act R h d))).map
          (stabilizer R (act R h d)).subtype) ∧
      (centralizer ({h} : Set (FreeAmalgam R))).relIndex (Z R b) ≤ 2


/-- Apply the escape input to the actual critical-line comparison. This
retains both the disjointness and the full conjugate plane needed by the
subsequent generation argument. -/
theorem conjugate_plane_split [Finite M] {L : Subgroup M}
    {source : LocalSource L R} {geometry : Geometry R}
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (edge : EdgeFacts R) (escape : ConjugateEscape geometry)
    (d e c b : Vertex R) (hd : color R d = false)
    (hcrit : CriticalPair R d e (geometry.exists_critical d hd))
    (hdc : (cosetGraph R).dist d c = 2) (hce : (cosetGraph R).dist c e = 2)
    (hdb : Adjacent R d b) (hcb : Adjacent R c b)
    (hcentral : ⁅V R d, V R d⁆ ≤
      (center (stabilizer R d)).map (stabilizer R d).subtype)
    (hnot : ¬ ⁅Z R d, Q R b⁆ ≤
      (center (stabilizer R c)).map (stabilizer R c).subtype)
    (h : FreeAmalgam R) (hhc : h ∈ stabilizer R c) (hhb : h ∈ stabilizer R b)
    (hne : ⁅Z R (act R h d), Q R b⁆ ≠ ⁅Z R d, Q R b⁆) :
    ⁅Z R d, Z R e⁆ ⊓ ⁅V R d, Z R (act R h d)⁆ = ⊥ ∧
      ⁅Z R d, Z R e⁆ ⊔ ⁅V R d, Z R (act R h d)⁆ = ⁅Z R (act R h d), Q R b⁆ :=
  conjugate_plane_split_of_radius_escape common hb edge d e c b hd hcrit hdc hce hdb hcb
    hcentral h hhc hhb (escape d e c b hd hcrit hdc hce hdb hcb hcentral hnot h hhc hhb hne)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint
