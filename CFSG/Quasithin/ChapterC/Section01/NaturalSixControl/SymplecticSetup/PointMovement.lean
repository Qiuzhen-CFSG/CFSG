module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalMovedSpace
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.GroupTheory.NormalizedSupConsequences
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeLayer
/-!
# Movement by the full native point radical

The original natural coordinates identify the commutator of W with the
point radical R with the actual natural moved space. The invariant pairing
makes its dimension equal fixed codimension, namely three. Hence the
commutator has order eight. Its intersection with the edge seed has order
at most two, giving relative index at least four after adjoining the seed.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory BinaryPermutation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
include s

theorem module_commutator_card_eight (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom) :
    Nat.card (⁅W,R⁆ : Subgroup M) = 8 := by
  let : IsElementaryAbelian 2 W := s.module_elementary
  let : IsElementaryAbelian 2 (⁅W,R⁆ : Subgroup M) :=
    IsElementaryAbelian.of_le (commutator_le_left W R)
  have hE : R.map s.projection = Model.E.map (MulAut.conj t).toMonoidHom := by
    rwa [Model.pointCore_eq_exceptional] at hfull
  let d : NaturalAction W := ⟨s.projection,
    s.projection_surjective_of_radical_image_le_conjugate t hE.le,
    s.projection_kernel,s.coordinates,s.action⟩
  have he := Nat.card_congr (Representation.NormalElementaryQuotient.movedEquiv
    W d.q d.onto d.kernel_centralizer R).toEquiv
  change Nat.card (⁅W,R⁆ : Subgroup M) =
    Nat.card (subspaceCommutator d.ρ ⊤ (R.map d.q)) at he
  rw [he,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hd := moved_finrank_equivariant d.ρ Model.rho (MonoidHom.id Model.S)
    d.linearCoordinates d.equivariant (R.map d.q)
  rw [map_id] at hd
  rw [hd,NaturalPairing.moved_finrank_eq_fixedCodim]
  change 2 ^ fixedCodim Model.rho (R.map s.projection) = 8
  rw [hE,fixedCodim_map_conj,ChapterB.Offenders.Six.fixedCodim_exceptional.2.2.2]
  rfl

theorem module_commutator_seed_index_four_le (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom) :
    4 ≤ (omegaCenter R).relIndex (⁅W,R⁆ ⊔ omegaCenter R) := by
  have hn : omegaCenter R ≤ normalizer ((⁅W,R⁆ : Subgroup M) : Set M) :=
    (omegaCenter_le R).trans (normalizer_commutator_ge_right W R)
  rw [relIndex_sup_of_normalizes _ _ hn]
  have hI : Nat.card (⁅W,R⁆ ⊓ omegaCenter R : Subgroup M) ≤ 2 := by
    rw [←s.module_inf_seed_card t hfull]
    exact card_le_of_le (inf_le_inf_right _ (commutator_le_left W R))
  have hm := relIndex_mul_relIndex (⊥ : Subgroup M) (⁅W,R⁆ ⊓ omegaCenter R)
    ⁅W,R⁆ bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,
    s.module_commutator_card_eight t hfull] at hm
  nlinarith [Nat.mul_le_mul_right ((omegaCenter R).relIndex ⁅W,R⁆) hI]

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
