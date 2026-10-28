module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry.FirstActors

/-!
# Faithfulness of the surviving degree-four core

The A₂ core contains an outer diagonal and a nonzero pure natural vector.
An inner element fixing the diagonal is trivial, while an outer element
cannot fix the pure vector. Conjugation and the marked model transport
this pointwise faithfulness to the actual source action. The same actor
catalogue gives fixed dimensions 1, 2, or 4 for every rank-four actor.
These are the two model inputs in the reverse-action argument of 12.1.8.
Source: Aschbacher--Smith, H.9.3(4--6) and 12.1.8, pp.391--392,793.
-/

public noncomputable section
open BinaryNaturalDual BinaryNaturalDual.FourActors BinaryLinear.OuterCyclic
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.FourActors
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry
variable (d : CoordinateAction 4)

theorem A2_core_faithful (a : M)
    (hf : ∀ v ∈ actorCore d A2 2, d.representation a v = v) : a = 1 := by
  have hp := Parameters.A2_parameters d transposition_mem_A2
    (show transposition ∉ B2 from fun ht => transposition_outer ht.2)
  have ht : transposition ^ 2 = 1 := by
    simpa only [transposition_order] using pow_orderOf_eq_one transposition
  by_cases hi : a ∈ BinaryNaturalDual.FourActors.inner
  · obtain ⟨g,rfl⟩ := hi
    have hg : g = 1 := by
      apply LinearEquiv.ext
      intro x
      let v := outerDiagonalEquiv d transposition ht transposition_outer x
      have hv : (v : V) ∈ actorCore d A2 2 := by
        rw [hp.2.2.1]
        exact Submodule.mem_sup_right v.property
      have hh := congrArg Prod.fst (hf v hv)
      rw [d.on_inner,naturalDualRepresentation_apply] at hh
      change g x = x
      simpa only [v, outerDiagonalEquiv_fst] using hh
    simp only [hg,map_one]
  · have hn : naturalFixed B2 ≠ ⊥ := by
      intro he
      have hd := Parameters.A2_fixed_planes.1
      rw [he,finrank_bot] at hd
      omega
    obtain ⟨x,hx,hx0⟩ := (naturalFixed B2).ne_bot_iff.mp hn
    have hxfix : (x,(0 : Module.Dual (ZMod 2) X)) ∈ actorFixed d B2 := by
      rw [A2Module.actorFixed_eq_prod d (A := B2) (show B2 ≤ BinaryNaturalDual.FourActors.inner from inf_le_right)]
      exact ⟨hx,Submodule.zero_mem _⟩
    have hxcore : (x,(0 : Module.Dual (ZMod 2) X)) ∈ actorCore d A2 2 := by
      rw [hp.2.2.1]
      exact Submodule.mem_sup_left hxfix
    have hd := outer_natural d a hi (x,0) (by simp)
    change d.representation a (x,0) ∈ dualSummand at hd
    rw [hf _ hxcore] at hd
    exact (hx0 ((mem_dualSummand _).mp hd)).elim

private theorem action_equivariant (a b : M) (v : V) :
    action d a (d.representation b v) =
      d.representation (MulAut.conj a b) (action d a v) := by
  change d.representation a (d.representation b v) =
    d.representation (a * b * a⁻¹) (d.representation a v)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel_right]

theorem coordinate_core_faithful (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 16)
    (h : naturalSummand ⊓ actorCore d A 2 ≤ actorFixed d (A ⊓ inner))
    (b : M) (hb : ∀ v ∈ actorCore d A 2, d.representation b v = v) : b = 1 := by
  obtain ⟨a,ha⟩ := coordinate_first_actor d A hcard h
  have he : MulAut.conj a b = 1 := by
    apply A2_core_faithful d
    intro v hv
    have hm : actorCore d A2 2 = (actorCore d A 2).map (action d a).toLinearMap := by
      rw [core_conjugate,ha]
    rw [hm] at hv
    obtain ⟨u,hu,rfl⟩ := hv
    change d.representation (MulAut.conj a b) (action d a u) = action d a u
    rw [← action_equivariant, hb u hu]
  exact (MulAut.conj a).injective (he.trans (map_one _).symm)

theorem coordinate_fixed_spectrum (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 16) :
    Module.finrank (ZMod 2) (actorFixed d A) = 1 ∨
    Module.finrank (ZMod 2) (actorFixed d A) = 2 ∨
    Module.finrank (ZMod 2) (actorFixed d A) = 4 := by
  obtain ⟨i,a,ha⟩ := PermutationCatalogue.actor_exhaustive A hcard
  have hd := Transport.fixed_finrank d.representation d.representation (MulAut.conj a)
    (action d a) (action_equivariant d a) A
  rw [ha] at hd
  fin_cases i
  · exact Or.inr (Or.inr (hd.trans (Parameters.A0_parameters d).1))
  · exact Or.inl (hd.trans (Parameters.A1_parameters d).1)
  · exact Or.inr (Or.inl (hd.trans (Parameters.A2_parameters d transposition_mem_A2
      (show transposition ∉ B2 from fun ht => transposition_outer ht.2)).2.1))

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry
variable {K E : Type*} [Group K] [Finite K] [AddCommGroup E] [Module (ZMod 2) E]

theorem source_primeRank_le (S : SourceSetup 4 K E) : primeRank 2 K ≤ 4 := by
  let : Finite (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))) :=
    Finite.of_equiv K S.projective.toEquiv
  exact (primeRank_equiv 2 S.projective).trans_le
    BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le

theorem source_actor_card (S : SourceSetup 4 K E) (I : Subgroup K)
    [IsElementaryAbelian 2 I] (hr : 4 ≤ rank I) : Nat.card I = 16 := by
  exact le_antisymm
    ((primeRank_le_iff_elementary_card_le K).mp (source_primeRank_le S) I inferInstance)
    (Nat.pow_le_of_le_log Nat.card_pos.ne' hr)

theorem source_core_faithful (S : SourceSetup 4 K E) (I : Subgroup K)
    [IsElementaryAbelian 2 I] (hr : 4 ≤ rank I)
    (h : S.natural ⊓ generatedCore (S.representation.comp I.subtype) 2 ≤
      S.fixed (I ⊓ componentLayer K))
    (b : K) (hb : ∀ v ∈ generatedCore (S.representation.comp I.subtype) 2,
      S.representation b v = v) : b = 1 := by
  let A := I.map S.model.group.toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map S.model.group.toMonoidHom
  have hA : Nat.card A = 16 :=
    (Subgroup.card_map_of_injective S.model.group.injective).trans (source_actor_card S I hr)
  have hn : S.natural.map S.model.coordinates.toLinearMap = naturalSummand := by
    ext v
    obtain ⟨x,rfl⟩ := S.model.coordinates.surjective v
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_naturalSummand]
    exact ModelOrbits.MarkedGeometry.mem_natural_iff_of_marking S.model.coordinates
      S.naturalCoordinates S.model.natural_marking x
  have ht := Submodule.map_mono (f := S.model.coordinates.toLinearMap) h
  rw [Submodule.map_inf _ S.model.coordinates.injective, hn, S.core_map,
    S.fixed_map, Subgroup.map_inf _ _ _ S.model.group.injective, S.layer_map] at ht
  have he : S.model.group b = 1 := by
    apply coordinate_core_faithful (ModelOrbits.AutomorphismModel.coordinateAction S.degree)
      A hA ht
    intro v hv
    change v ∈ generatedCore
      ((ModelOrbits.AutomorphismModel.coordinateAction S.degree).representation.comp A.subtype) 2 at hv
    rw [← S.core_map] at hv
    obtain ⟨u,hu,rfl⟩ := hv
    change (ModelOrbits.AutomorphismModel.coordinateAction S.degree).representation
      (S.model.group b) (S.model.coordinates u) = S.model.coordinates u
    rw [← S.model.equivariant, hb u hu]
  exact S.model.group.injective (he.trans (map_one _).symm)

theorem source_fixed_spectrum (S : SourceSetup 4 K E) (I : Subgroup K)
    [IsElementaryAbelian 2 I] (hr : 4 ≤ rank I) :
    Module.finrank (ZMod 2) (S.fixed I) = 1 ∨
    Module.finrank (ZMod 2) (S.fixed I) = 2 ∨
    Module.finrank (ZMod 2) (S.fixed I) = 4 := by
  let A := I.map S.model.group.toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map S.model.group.toMonoidHom
  have hA : Nat.card A = 16 :=
    (Subgroup.card_map_of_injective S.model.group.injective).trans (source_actor_card S I hr)
  rw [S.fixed_finrank]
  exact coordinate_fixed_spectrum (ModelOrbits.AutomorphismModel.coordinateAction S.degree) A hA

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry
