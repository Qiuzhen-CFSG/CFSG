module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ReverseCommon

/-!
# A faithful pure plane in the low-rank first-stage case

An outer actor has no nonzero pure fixed vector. A nonidentity involution
in the inner rank-two actor fixes at least a plane of the natural summand.
The rank-three core contains that plane, and the pure-core restriction
makes it fixed by the whole inner actor. Its intersection with the full
actor fixed space is zero, which supplies the faithful reverse actor in
12.1.8. No choice of an unrelated model action is involved.
Source: Aschbacher--Smith, 12.1.8, printed pp.792--793 (PDF809--810).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BinaryNaturalDual
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
variable {K E : Type*} [Group K] [Finite K] [AddCommGroup E] [Module (ZMod 2) E]

omit [Finite K] in
theorem natural_inf_fixed_eq_bot_of_outer (S : SourceSetup 4 K E)
    (I : Subgroup K) (hout : ¬ I ≤ componentLayer K) :
    S.natural ⊓ S.fixed I = ⊥ := by
  obtain ⟨a,ha,ho⟩ := Set.not_subset.mp hout
  apply bot_unique
  intro v hv
  have hn : S.model.coordinates v ∈ BinaryNaturalDual.FourActors.naturalSummand := by
    rw [BinaryNaturalDual.FourActors.mem_naturalSummand]
    exact (ModelOrbits.MarkedGeometry.mem_natural_iff_of_marking S.model.coordinates
      S.naturalCoordinates S.model.natural_marking v).mp hv.1
  have hd := BinaryNaturalDual.FourActors.outer_natural
    (ModelOrbits.AutomorphismModel.coordinateAction S.degree) (S.model.group a)
    (fun h => ho ((S.model.inner_iff a).mp h)) (S.model.coordinates v) hn
  change (ModelOrbits.AutomorphismModel.coordinateAction S.degree).representation
    (S.model.group a) (S.model.coordinates v) ∈ BinaryNaturalDual.FourActors.dualSummand at hd
  have hvf : S.representation a v = v := hv.2 ⟨a,ha⟩
  rw [← S.model.equivariant, hvf] at hd
  have he : S.model.coordinates v = 0 := Prod.ext
    ((BinaryNaturalDual.FourActors.mem_dualSummand _).mp hd)
    ((BinaryNaturalDual.FourActors.mem_naturalSummand _).mp hn)
  exact S.model.coordinates.injective (he.trans (map_zero _).symm)

theorem four_low_pure_plane (S : SourceSetup 4 K E) (I : Subgroup K)
    [IsElementaryAbelian 2 I] (hr : rank I = 3)
    (hj : rank (I ⊓ componentLayer K) = 2) (hout : ¬ I ≤ componentLayer K)
    (hn : S.natural ⊓ generatedCore (S.representation.comp I.subtype) 2 ≤
      S.fixed (I ⊓ componentLayer K)) :
    ∃ P : Submodule (ZMod 2) E,
      P ≤ S.natural ∧ P ≤ generatedCore (S.representation.comp I.subtype) 2 ∧
      P ≤ S.fixed (I ⊓ componentLayer K) ∧ 2 ≤ Module.finrank (ZMod 2) P ∧
      P ⊓ S.fixed I = ⊥ := by
  let J := I ⊓ componentLayer K
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.of_le inf_le_left
  have hJ : J ≠ ⊥ := by
    intro he
    change rank J = 2 at hj
    simp [he,rank] at hj
  obtain ⟨a,ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hJ
  have ha := a.property
  have ha1' : (a : K) ≠ 1 := fun hh => ha1 (Subtype.ext hh)
  let b : J := a
  have hb : b ≠ 1 := ha1
  have ho : orderOf b = 2 := orderOf_eq_prime
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 J) b) hb
  let ρ := innerNatural S I
  let F := fixedSpace ρ (zpowers b)
  let f : BinaryLinear.OuterCyclic.Space 4 →ₗ[ZMod 2] E :=
    S.natural.subtype.comp S.naturalCoordinates.symm.toLinearMap
  have hf : Function.Injective f := fun x y h =>
    S.naturalCoordinates.symm.injective (Subtype.ext h)
  let P := F.map f
  have hPn : P ≤ S.natural := by
    rintro v ⟨x,hx,rfl⟩
    exact (S.naturalCoordinates.symm x).property
  have hPc : P ≤ generatedCore (S.representation.comp I.subtype) 2 := by
    rintro v ⟨x,hx,rfl⟩
    let c : I := ⟨a,ha.1⟩
    have hc : c ≠ 1 := fun hh => ha1' (congrArg Subtype.val hh)
    have hcore := cyclic_fixed_le_core (S.representation.comp I.subtype) c hc
    have hlog : Nat.log 2 (Nat.card I) - 1 = 2 := by change rank I - 1 = 2; omega
    rw [hlog] at hcore
    apply hcore
    rw [mem_fixedSpace_zpowers_iff]
    change S.representation a (S.naturalCoordinates.symm x : E) =
      (S.naturalCoordinates.symm x : E)
    rw [S.natural_action ⟨a,ha.2⟩]
    have hx' := (mem_fixedSpace_zpowers_iff ρ b x).mp hx
    change S.layer ⟨a,ha.2⟩ x = x at hx'
    rw [hx']
  have hdim : 2 ≤ Module.finrank (ZMod 2) P := by
    have hi := (involution_actor_rank_and_fixedCodim ρ b ho).2.2.2
    have hd := fixedCodim_add_finrank ρ (zpowers b)
    have he := (Submodule.equivMapOfInjective f hf F).finrank_eq
    have hx : Module.finrank (ZMod 2) (BinaryLinear.OuterCyclic.Space 4) = 4 := by
      simp [BinaryLinear.OuterCyclic.Space]
    rw [hx] at hi hd
    change Module.finrank (ZMod 2) F = Module.finrank (ZMod 2) P at he
    change fixedCodim ρ (zpowers b) + Module.finrank (ZMod 2) F = 4 at hd
    omega
  refine ⟨P,hPn,hPc,fun v hv => hn ⟨hPn hv,hPc hv⟩,hdim,?_⟩
  apply bot_unique
  exact (inf_le_inf_right (S.fixed I) hPn).trans
    (le_of_eq (natural_inf_fixed_eq_bot_of_outer S I hout))

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
