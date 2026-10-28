module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Local

/-!
# The two source calculations still needed for the original replacement

Local calculations apply uniformly to every critical pair. Paired estimates
apply to a literal conjugate of a reversed critical orbit. Their conclusions
are geometric subgroup statements, with no natural subgroup complement,
Sylow hypothesis, or disjointness of moving layers.

The conditional assembly in Geometry.Source constructs the final PairedOrbit;
these contracts alone do not assert that the source calculations hold.
Source: MS93 (3.3), (3.6), printed pp.866--871.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
universe u
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M) (geo : Geometry R)

/-- Uniform local identities before the favorable orientation is selected. -/
structure LocalCalculations : Prop where
  edge_centralizer : EdgeCentralizerCondition R
  orbit_core : ∀ c b,
    CriticalPair R (alpha R) c (geo.exists_critical _ rfl) →
    Adjacent R (alpha R) b → Adjacent R c b →
    criticalOrbitNative R c b ≤ pCore 2 M
  commutator_edge : ∀ c b,
    CriticalPair R (alpha R) c (geo.exists_critical _ rfl) →
    Adjacent R (alpha R) b → Adjacent R c b →
    ⁅Q R (alpha R),criticalOrbit R c b⁆ ≤ Z R b
  commutator_core : ∀ c b,
    CriticalPair R (alpha R) c (geo.exists_critical _ rfl) →
    Adjacent R (alpha R) b → Adjacent R c b →
    ⁅criticalOrbit R c b,Ltilde R (alpha R)⁆ = core R (alpha R)
  commutator_central : ∀ c b,
    CriticalPair R (alpha R) c (geo.exists_critical _ rfl) →
    Adjacent R (alpha R) b → Adjacent R c b →
    ⁅⁅pCore 2 M,criticalOrbitNative R c b⁆,pResidual 2 M⁆ = ⊥
  image_two : ∀ c,
    CriticalPair R (alpha R) c (geo.exists_critical _ rfl) →
    (Q R c).relIndex (Z R (alpha R)) = 2

/-- The opposite subgroup is the actual orbit from a reversed and rebased
critical pair, with its literal conjugation map. -/
def RebasedOrbit (c b : Vertex R) (B : Subgroup (FreeAmalgam R)) : Prop :=
  ∃ (g : FreeAmalgam R) (d : Vertex R),
    act R g (alpha R) = c ∧ act R g d = alpha R ∧ act R g (beta R) = b ∧
    CriticalPair R (alpha R) d (geo.exists_critical _ rfl) ∧
    Adjacent R d (beta R) ∧
    B = (criticalOrbit R d (beta R)).map (MulAut.conj g⁻¹).toMonoidHom

/-- The remaining paired-orbit calculation retains only elementary
commutators, allowing a common central attachment to both moving layers. -/
structure PairEstimates (c b : Vertex R) (B : Subgroup (FreeAmalgam R)) : Prop where
  full_image : criticalOrbit R c b ⊔ Q R c = Q R b
  moved_plane : criticalPlane R c b ≤
    ⁅criticalOrbit R c b,stabilizer R (alpha R)⁆ ⊔ Z R (alpha R)
  elementary_commutator :
    IsElementaryAbelian 2 (⁅criticalOrbit R c b,B⁆ : Subgroup (FreeAmalgam R))

/-- Source producer for the local calculation on the original carriers. -/
def LocalCalculationInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥), InitialNatural h e hz →
      ∀ d : Replacement L R, CentralLayer d → replacementDistance h d = 2 →
        (¬ core d.radical (alpha d.radical) ≤
          (frattini (Q d.radical (alpha d.radical))).map
            (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) →
        LocalCalculations d.radical (replacementGeometry h d)

/-- Independent paired estimate producer. The local identities may be used
explicitly; final assembly must construct them from the preceding input. -/
def PairEstimateInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥), InitialNatural h e hz →
      ∀ d : Replacement L R, CentralLayer d → replacementDistance h d = 2 →
        (¬ core d.radical (alpha d.radical) ≤
          (frattini (Q d.radical (alpha d.radical))).map
            (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) →
        LocalCalculations d.radical (replacementGeometry h d) →
        ∀ (c b : Vertex d.radical) (B : Subgroup (FreeAmalgam d.radical)),
          CriticalPair d.radical (alpha d.radical) c
            ((replacementGeometry h d).exists_critical _ rfl) →
          Adjacent d.radical (alpha d.radical) b → Adjacent d.radical c b →
          RebasedOrbit d.radical (replacementGeometry h d) c b B →
          2 * (commutatorPreimage (criticalOrbit d.radical c b) B
            (Z d.radical (alpha d.radical))).relIndex (criticalOrbit d.radical c b) ≤
              (Q d.radical c).relIndex (criticalOrbit d.radical c b) →
          (Q d.radical c).relIndex (criticalOrbit d.radical c b) ≤
            (Q d.radical (alpha d.radical)).relIndex B →
          PairEstimates d.radical c b B

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
