module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveWholePresentation
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MarkedWeyl
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.SourceHomomorphisms

/-!
# Explicit unitary equations on the same marked source quotient

Both data types retain the four parameter groups, full Cartan, marked
normalizer lifts, exact finite relation schemes and generation. The proved
presentations construct onto maps from the WHOLE SU₄ or SU₅ carrier, with
all generator images prescribed and the model Borel mapped into the actual
source Borel. Neither a model homomorphism nor its faithfulness is input.
The source coordinate owner must supply these equations and placements.
Source: DGS, Groups and Graphs, Theorem D, printed p.224; Steinberg,
Lectures on Chevalley Groups, Theorem 33 and the Bruhat presentation proof.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
variable {X E : Type*} [Group X] [Field E] [CharP E 2]
variable {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

/-- Explicit U₄ equation and source-placement data; the model map is constructed. -/
structure FourData (σ : E ≃+* E) (hσ : Function.Involutive σ) where
  roots : PositiveMaps (X ⧸ Q.D) (Multiplicative E)
    (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ))
    (Multiplicative E)
    (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ))
  cartan : FourWeyl.torusParameters E σ →* (X ⧸ Q.D)
  lifts : MarkedWeyl.Lifts Q i
  equations : (FourPresentation.parameters E σ hσ).Satisfies
    (Presentation.Generator.ofMaps roots cartan (lifts.s : X ⧸ Q.D) (lifts.t : X ⧸ Q.D))
  generate : ReflectionLaws.fullGenerated roots cartan (lifts.s : X ⧸ Q.D) (lifts.t : X ⧸ Q.D)=⊤
  positive_le : roots.generated≤split.U
  cartan_le : cartan.range≤Q.tits.B ⊓ Q.tits.N

/-- U₅ retains both entire nonabelian Hermitian parameter groups at arbitrary q. -/
structure FiveData (J : HermitianForm 5 E) where
  roots : PositiveMaps (X ⧸ Q.D) (Multiplicative E) (FivePositive.Parameter J)
    (Multiplicative E) (FivePositive.Parameter J)
  cartan : (Eˣ × Eˣ) →* (X ⧸ Q.D)
  lifts : MarkedWeyl.Lifts Q i
  equations : (FivePresentation.parameters J).Satisfies
    (Presentation.Generator.ofMaps roots cartan (lifts.s : X ⧸ Q.D) (lifts.t : X ⧸ Q.D))
  generate : ReflectionLaws.fullGenerated roots cartan (lifts.s : X ⧸ Q.D) (lifts.t : X ⧸ Q.D)=⊤
  positive_le : roots.generated≤split.U
  cartan_le : cartan.range≤Q.tits.B ⊓ Q.tits.N

namespace FourData
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
variable [Finite E] {Q split i} (σ : E ≃+* E) (hσ : Function.Involutive σ)
variable (d : FourData Q split i σ hσ)

def modelHom : (form E σ hσ).specialSubgroup →* (X ⧸ Q.D) :=
  FourPresentation.lift E σ hσ d.equations

theorem modelHom_surjective : Function.Surjective (d.modelHom σ hσ) := by
  apply FourPresentation.lift_surjective
  rw [(FourPresentation.parameters E σ hσ).roots_ofMaps d.equations,
    (FourPresentation.parameters E σ hσ).torus_ofMaps d.equations]
  exact d.generate

theorem modelHom_generator (j) :
    d.modelHom σ hσ (FourPresentation.modelGenerators E σ hσ j)=
      Presentation.Generator.ofMaps d.roots d.cartan (d.lifts.s : X ⧸ Q.D) (d.lifts.t : X ⧸ Q.D) j :=
  FourPresentation.lift_generator E σ hσ d.equations j

theorem modelHom_borel_le :
    (FourPositive.roots E σ hσ).borel (FourWeyl.hHom E σ hσ)≤Q.tits.B.comap (d.modelHom σ hσ) := by
  intro g hg
  obtain ⟨a,z,c,b,k,rfl⟩ := (FourTorus.torusLaws E σ hσ).exists_word (FourPositive.collects E σ hσ) hg
  have ha := d.modelHom_generator σ hσ (.A a)
  have hz := d.modelHom_generator σ hσ (.D z)
  have hc := d.modelHom_generator σ hσ (.C c)
  have hb := d.modelHom_generator σ hσ (.B b)
  have hk := d.modelHom_generator σ hσ (.torus k)
  change (d.modelHom σ hσ) ((FourPositive.roots E σ hσ).word a z c b*FourWeyl.hHom E σ hσ k)∈Q.tits.B
  change (d.modelHom σ hσ) (FourPositive.A E σ hσ a.toAdd*
    FourPositive.D E σ hσ z.toAdd*FourPositive.C E σ hσ c.toAdd*
    FourPositive.B E σ hσ b.toAdd*FourWeyl.hHom E σ hσ k)∈Q.tits.B
  simp only [map_mul]
  change d.modelHom σ hσ (FourPositive.A E σ hσ a.toAdd)=d.roots.A a at ha
  change d.modelHom σ hσ (FourPositive.D E σ hσ z.toAdd)=d.roots.D z at hz
  change d.modelHom σ hσ (FourPositive.C E σ hσ c.toAdd)=d.roots.C c at hc
  change d.modelHom σ hσ (FourPositive.B E σ hσ b.toAdd)=d.roots.B b at hb
  change d.modelHom σ hσ (FourWeyl.hHom E σ hσ k)=d.cartan k at hk
  rw [ha,hz,hc,hb,hk]
  exact Q.tits.B.mul_mem (split.U_le (d.positive_le (d.roots.word_mem a z c b)))
    (d.cartan_le ⟨k,rfl⟩).1
end FourData

namespace FiveData
variable [Finite E] {Q split i} (J : HermitianForm 5 E)
variable (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1) (d : FiveData Q split i J)

def modelHom : J.specialSubgroup →* (X ⧸ Q.D) := FivePresentation.lift J κ hκ hJ d.equations

theorem modelHom_surjective : Function.Surjective (d.modelHom J κ hκ hJ) := by
  apply FivePresentation.lift_surjective
  rw [(FivePresentation.parameters J).roots_ofMaps d.equations,
    (FivePresentation.parameters J).torus_ofMaps d.equations]
  exact d.generate

theorem modelHom_generator (j) :
    d.modelHom J κ hκ hJ (FivePresentation.modelGenerators J κ hκ hJ j)=
      Presentation.Generator.ofMaps d.roots d.cartan (d.lifts.s : X ⧸ Q.D) (d.lifts.t : X ⧸ Q.D) j :=
  FivePresentation.lift_generator J κ hκ hJ d.equations j

theorem modelHom_borel_le :
    (FivePositive.roots J κ hκ hJ).borel (FiveWeyl.h J κ hκ hJ)≤Q.tits.B.comap (d.modelHom J κ hκ hJ) := by
  intro g hg
  obtain ⟨a,z,c,b,k,rfl⟩ := (FiveTorus.torusLaws J κ hκ hJ).exists_word (FivePositive.collects J κ hκ hJ) hg
  have ha := d.modelHom_generator J κ hκ hJ (.A a)
  have hz := d.modelHom_generator J κ hκ hJ (.D z)
  have hc := d.modelHom_generator J κ hκ hJ (.C c)
  have hb := d.modelHom_generator J κ hκ hJ (.B b)
  have hk := d.modelHom_generator J κ hκ hJ (.torus k)
  change (d.modelHom J κ hκ hJ) ((FivePositive.roots J κ hκ hJ).word a z c b*FiveWeyl.h J κ hκ hJ k)∈Q.tits.B
  change (d.modelHom J κ hκ hJ) (FivePositive.A J κ hκ hJ a.toAdd*
    FivePositive.D J hJ z*FivePositive.C J hJ c.toAdd*FivePositive.B J hJ b*FiveWeyl.h J κ hκ hJ k)∈Q.tits.B
  simp only [map_mul]
  change d.modelHom J κ hκ hJ (FivePositive.A J κ hκ hJ a.toAdd)=d.roots.A a at ha
  change d.modelHom J κ hκ hJ (FivePositive.D J hJ z)=d.roots.D z at hz
  change d.modelHom J κ hκ hJ (FivePositive.C J hJ c.toAdd)=d.roots.C c at hc
  change d.modelHom J κ hκ hJ (FivePositive.B J hJ b)=d.roots.B b at hb
  change d.modelHom J κ hκ hJ (FiveWeyl.h J κ hκ hJ k)=d.cartan k at hk
  rw [ha,hz,hc,hb,hk]
  exact Q.tits.B.mul_mem (split.U_le (d.positive_le (d.roots.word_mem a z c b)))
    (d.cartan_le ⟨k,rfl⟩).1
end FiveData
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
