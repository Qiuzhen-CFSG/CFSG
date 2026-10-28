module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneComparison
public import Theory.Representation.PSL3Two.TwoDimensionalCentralizer
public import Theory.Representation.BinaryOffender.CommutingSectionDegree
public import Theory.Representation.BinaryOffender.Homogeneous.Embedding

/-!
# Excluding rank-one FF actions commuting with a fixed-free linear three

The complete B.5 classifier leaves its symmetric-three and quasisimple
rows at three-rank one. The former has a moved plane, on which PSL₃(2)
acts trivially. An Irr⁺ moved space is fixed by a commuting perfect group.
The doubled natural row is ruled out by its two-dimensional multiplicity
space. Thus none of these rows can commute with a fixed-free PSL₃(2).

Source: Aschbacher–Smith 13.4.7(2), printed p.902, using B.5.1 and B.5.6.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
variable {Q D V : Type*} [Group Q] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem no_irrPlus_moved
    (ρ : Representation (ZMod 2) Q V) (S : Subgroup Q) [Group.IsPerfect S]
    (hfix : fixedSpace ρ S = ⊥)
    (f : D →* Q) (hc : f.range ≤ centralizer (S : Set Q))
    (A : Subgroup D) (hi : IsIrrPlus (ρ.comp f) A (moved (ρ.comp f) A)) : False := by
  have hh := hi.map_equivariant_embedding (ρ.comp f) ρ f LinearMap.id
    (fun _ _ => rfl) Function.injective_id
  rw [Submodule.map_id] at hh
  change IsIrrPlus ρ (A.map f) (subspaceCommutator (ρ.comp f) ⊤ A) at hh
  rw [subspaceCommutator_comp_map] at hh
  exact not_irrPlus_moved_of_commuting_perfect ρ S (A.map f) hfix
    (le_centralizer_iff.mp ((map_le_range f A).trans hc)) hh

private theorem no_plane_moved
    (ρ : Representation (ZMod 2) Q V) (S : Subgroup Q)
    (eS : S ≃* Matrix.PSL3Two.PSL) (hfix : fixedSpace ρ S = ⊥)
    (f : D →* Q) (hc : f.range ≤ centralizer (S : Set Q))
    (hd : Module.finrank (ZMod 2) (moved (ρ.comp f) ⊤) = 2) : False := by
  let W := moved (ρ.comp f) ⊤
  have hs : S ≤ subspaceStabilizer ρ W := by
    change S ≤ subspaceStabilizer ρ (subspaceCommutator (ρ.comp f) ⊤ ⊤)
    rw [subspaceCommutator_comp_map]
    exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      ((le_centralizer_iff.mp ((map_le_range f ⊤).trans hc)).trans
        (Subgroup.centralizer_le_normalizer _))
  let τ := ((stabilizerRepresentation ρ W).comp (inclusion hs)).comp eS.symm.toMonoidHom
  let e : W ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa only [Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] using hd)
  have ht := Representation.PSL3Two.two_dimensional_trivial (e.conjRingEquiv.toMonoidHom.comp τ)
  have hz : W = ⊥ := by
    apply bot_unique
    intro v hv
    apply hfix.le
    intro s
    have hh := LinearMap.congr_fun (ht (eS s)) (e ⟨v,hv⟩)
    have he : τ (eS s) ⟨v,hv⟩ = ⟨v,hv⟩ := e.injective (by
      change e (τ (eS s) (e.symm (e ⟨v,hv⟩))) = e ⟨v,hv⟩ at hh
      simpa only [e.symm_apply_apply] using hh)
    have he' := congrArg Subtype.val he
    change ρ (eS.symm (eS s)) v = v at he'
    rwa [eS.symm_apply_apply] at he'
  change Module.finrank (ZMod 2) W = 2 at hd
  rw [hz,finrank_bot] at hd
  omega

omit [FiniteDimensional (ZMod 2) V] in
private theorem no_doubled_moved
    (ρ : Representation (ZMod 2) Q V) (S : Subgroup Q)
    (eS : S ≃* Matrix.PSL3Two.PSL)
    (hfix : fixedSpace ρ S = ⊥)
    (f : D →* Q) (hc : f.range ≤ centralizer (S : Set Q))
    (A : Subgroup D) (U : Subrepresentation (ρ.comp f))
    (hu : U.toSubmodule = moved (ρ.comp f) A)
    (F : BinaryField)
    (e : ActionEquiv (U.toRepresentation.comp A.subtype) (repeated (linearNatural F 3) 2)) : False := by
  let W := U.toSubmodule
  have hs : S ≤ subspaceStabilizer ρ W := by
    dsimp only [W]
    rw [hu]
    change S ≤ subspaceStabilizer ρ (subspaceCommutator (ρ.comp f) ⊤ A)
    rw [subspaceCommutator_comp_map]
    exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      ((le_centralizer_iff.mp ((map_le_range f A).trans hc)).trans (Subgroup.centralizer_le_normalizer _))
  let τ := ((stabilizerRepresentation ρ W).comp (inclusion hs)).comp eS.symm.toMonoidHom
  let α := (U.toRepresentation.comp A.subtype).comp e.groupEquiv.symm.toMonoidHom
  have hcomm (a : Matrix.PSL3Two.PSL) (b : Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
      (v : W) : τ a (α b v) = α b (τ a v) := by
    apply Subtype.ext
    change ρ (eS.symm a) (ρ (f (e.groupEquiv.symm b)) v) =
      ρ (f (e.groupEquiv.symm b)) (ρ (eS.symm a) v)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    exact LinearMap.congr_fun (congrArg ρ
      (hc (MonoidHom.mem_range.mpr ⟨(e.groupEquiv.symm b : D),rfl⟩)
        (eS.symm a) (eS.symm a).property)) v
  have he (b : Matrix.SpecialLinearGroup (Fin 3) F.Carrier) (v : W) :
      e.linearEquiv (α b v) = SL3DoubledNaturalOffenders.representation F.Carrier b (e.linearEquiv v) := by
    have hh := e.intertwines (e.groupEquiv.symm b) v
    rw [e.groupEquiv.apply_symm_apply] at hh
    exact hh
  have ht := Representation.PSL3Two.doubled_natural_commuting_trivial_of_coordinates τ α hcomm e.linearEquiv he
  have hzero (v : W) : v = 0 := by
    apply Subtype.ext
    apply hfix.le
    intro s
    have hh := congrArg Subtype.val (ht (eS s) v)
    change ρ (eS.symm (eS s)) v = v at hh
    rw [eS.symm_apply_apply] at hh
    exact hh
  let : Nontrivial W := e.linearEquiv.toEquiv.nontrivial
  obtain ⟨v,hv⟩ := exists_ne (0:W)
  exact hv (hzero v)

/-- The genuine B.5.3 action of three-rank at most one cannot commute
with a fixed-free PSL₃(2) component. -/
theorem no_rank_one_FF_of_commuting_linearThree [Finite D] [Nontrivial D]
    (ρ : Representation (ZMod 2) Q V) (S : Subgroup Q)
    (eS : S ≃* Matrix.PSL3Two.PSL) (hfix : fixedSpace ρ S = ⊥)
    (f : D →* Q) (hc : f.range ≤ centralizer (S : Set Q))
    (hr : primeRank 3 D ≤ 1)
    (hyp : FFHypothesis KnownSimple.IsKnownSimple (ρ.comp f)) : False := by
  let : Group.IsPerfect Matrix.PSL3Two.PSL := Atlas.psl_perfect 3 (by decide)
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective (f := eS.symm.toMonoidHom) eS.symm.surjective
  have ha := adequateAlternative_knownSimple (ρ.comp f) hyp
  rcases ha.at_three_rank_le_one hr with ⟨hq,⟨c⟩⟩ | ⟨c⟩
  · cases c.rank_one_action hr with
    | irreducible hi _ _ _ _ =>
      rw [c.sectionData.space_eq] at hi
      exact no_irrPlus_moved ρ S hfix f hc _ hi
    | doubleThree F _ _ e _ _ =>
      exact no_doubled_moved ρ S eS hfix f hc _ c.sectionData.space
        c.sectionData.space_eq F e
  · obtain ⟨c⟩ := c
    exact no_plane_moved ρ S eS hfix f hc c.dimension

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
