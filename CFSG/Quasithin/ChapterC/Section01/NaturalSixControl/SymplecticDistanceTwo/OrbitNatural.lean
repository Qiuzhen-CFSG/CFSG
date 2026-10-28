module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.SymmetricSixCover
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitActor
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitLinearMovement
/-!
# Natural recognition of the literal critical-orbit quotient

The source strict index comparison identifies an odd elementary order-eight
actor of fixed codimension two. The actual full edge image gives whole A6
movement. The proved B.5 selection and universal augmentation cover then
produce the natural quotient, retaining its outer marking, literal fixed-space
kernel, and containment of that kernel in movement by the original actor.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

theorem orbit_natural_quotient_fixed_le_moved
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    [IsElementaryAbelian 2 (OrbitQuotient R c b)]
    (hsurj : Function.Surjective s.projection)
    (B : Subgroup (FreeAmalgam R)) (hBQ : B ≤ Q R c)
    (hcommB : ⁅Q R c,B⁆ ≤ Z R b)
    (hcomp : (Q R c).relIndex (criticalOrbit R c b) ≤ (Q R (alpha R)).relIndex B) :
    ∃ (e : S ≃* S)
      (p : Additive (OrbitQuotient R c b) →ₗ[ZMod 2] BinaryPermutation.natural (Fin 6)),
      Function.Surjective p ∧
      p.ker = fixedSpace (s.orbitFullRepresentation hb hc hab hcb hsurj) (alternatingGroup (Fin 6)) ∧
      (∀ g v, p (s.orbitFullRepresentation hb hc hab hcb hsurj g v) =
        BinaryPermutation.naturalRepresentation (Fin 6) (e g) (p v)) ∧
      fixedSpace (s.orbitFullRepresentation hb hc hab hcb hsurj) (alternatingGroup (Fin 6)) ≤
        subspaceCommutator (s.orbitFullRepresentation hb hc hab hcb hsurj) ⊤ (s.orbitActorImage B) := by
  obtain ⟨he,hcard,hcodim,hodd⟩ := s.orbitActorImage_offender h t hfull hb hlarge hc hab hcb
    hsurj B hBQ hcommB hcomp
  let := he
  have himage := (s.criticalOrbit_images_full h t hfull hb hlarge hc hab hcb B hBQ hcommB hcomp).2.1
  exact ChapterB.QuasisimpleSource.SourceCompletion.symmetricSix_natural_quotient_fixed_le_moved
    (s.orbitFullRepresentation hb hc hab hcb hsurj)
    (s.orbitFullRepresentation_injective hb hc hab hcb hsurj h t hfull hlarge)
    (s.alternating_sqtk hsq) (s.orbitActorImage B) hcard hcodim hodd
    (s.orbitFullRepresentation_component_movement h t hfull hb hlarge hc hab hcb himage hsurj)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
