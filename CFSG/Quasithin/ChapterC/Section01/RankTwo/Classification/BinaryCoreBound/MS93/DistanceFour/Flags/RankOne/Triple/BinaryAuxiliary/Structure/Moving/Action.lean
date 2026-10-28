module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel.FixedSummand.Action.Quotient

/-!
# The marked full actor on the auxiliary quotient

The existing full-parabolic quotient transports through the actual local
conjugation to an onto S3 marking with precisely the original local core
as kernel. If that core centralizes Y/U, the genuine quotient action
constructed in `Moving.Quotient` descends through this marking. The
ambient action equation is preserved. Trivial core action is an explicit
geometric obligation, not a consequence of the abstract quotient alone.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
open Incident.Pairing.Transport.Natural.Kernel
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The full local actor has the actual S3 quotient, with its exact core kernel. -/
theorem exists_actorProjection [Finite M] (source : LocalSource L R) (i : Bool) (d : M) :
    ∃ π : localFlagActor source (!i) d →* BinaryS3.Actor,
      Function.Surjective π ∧
      π.ker = (localFlagKernel source (!i) d).subgroupOf (localFlagActor source (!i) d) := by
  obtain ⟨π, hπ, hk⟩ := exists_barProjection source (!i)
  let e := (MulAut.conj (embedM R d)).subgroupMap (flagParabolic source (!i))
  refine ⟨π.comp e.symm.toMonoidHom, hπ.comp e.symm.surjective, ?_⟩
  ext g
  change π (e.symm g) = 1 ↔ (g : FreeAmalgam R) ∈ localFlagKernel source (!i) d
  rw [← MonoidHom.mem_ker, hk, localFlagKernel, localConjugate, mem_map_equiv]
  rfl

/-- Core centralization descends the actual auxiliary representation through
the exact marked quotient, retaining the representative-wise action equation. -/
theorem AuxiliaryModule.exists_descendedRepresentation [Finite M]
    {source : LocalSource L R} {i : Bool} {d : M} (b : AuxiliaryModule source i d)
    (hcore : ⁅Y source i d, localFlagKernel source (!i) d⁆ ≤ secondFlagLayer source i d) :
    ∃ π : localFlagActor source (!i) d →* BinaryS3.Actor,
      Function.Surjective π ∧
      π.ker = (localFlagKernel source (!i) d).subgroupOf (localFlagActor source (!i) d) ∧
      ∃ ρ : Representation (ZMod 2) BinaryS3.Actor b.Space,
        ∀ g v, b.representation g v = ρ (π g) v := by
  obtain ⟨π, hπ, hker⟩ := exists_actorProjection source i d
  have hk : π.ker ≤ b.representation.asGroupHom.ker := by
    intro g hg
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    apply MonoidHom.mem_ker.mp
    exact (b.kernel_iff (localFlagKernel source (!i) d)
      (map_mono (flagKernel_le source (!i)))).mpr hcore (hker ▸ hg)
  let σ := π.liftOfSurjective hπ ⟨b.representation.asGroupHom, hk⟩
  let ρ : Representation (ZMod 2) BinaryS3.Actor b.Space :=
    (Units.coeHom (b.Space →ₗ[ZMod 2] b.Space)).comp σ
  refine ⟨π, hπ, hker, ρ, ?_⟩
  intro g v
  have he : σ (π g) = b.representation.asGroupHom g :=
    π.liftOfRightInverse_comp_apply _ _ _ g
  change b.representation g v = (σ (π g)).val v
  rw [he, Representation.asGroupHom_apply]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
