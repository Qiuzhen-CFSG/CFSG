module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.Models
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank

/-!
# Natural central sections from the actual B.5.1 witnesses

The source moved space and its quotient by fixed vectors give a surjection
with a pointwise fixed kernel; displacement lies in the moved space, so the
outer quotient is trivial. This construction permits both nonsplit extension
orientations. For S₅ only its embedded A₅ is used. A primitive cubic diagonal
pair rules out even-degree SL₃, and one natural copy is explicitly identified
with the one-coordinate repeated representation.

These are constructions from specified action witnesses. The exhaustive
selection of these witnesses from B.5.1 remains a separate obligation.
Source: Aschbacher–Smith, B.5.1, printed pp.99–103, and the proof of 15.3.67,
printed p.1154 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer.RankOneDispatch
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u v w z
variable {D : Type u} [Group D] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  {E : Type w} [Group E] {X : Type z} [AddCommGroup X] [Module (ZMod 2) X]
  {ρ : Representation (ZMod 2) D W} {σ : Representation (ZMod 2) E X}

/-- An actual natural moved module gives a section with zero kernel. -/
noncomputable def modelSection_of_moved {L : Subgroup D} (s : MovedSection ρ L)
    (e : ActionEquiv (s.space.toRepresentation.comp L.subtype) σ) :
    ModelSection ρ (L.subtype.comp e.groupEquiv.symm.toMonoidHom) σ := by
  let U : Subrepresentation (ρ.comp (L.subtype.comp e.groupEquiv.symm.toMonoidHom)) :=
    ⟨s.space.toSubmodule, fun g _ hv => s.space.apply_mem_toSubmodule _ hv⟩
  refine ⟨U, e.linearEquiv.toLinearMap, e.linearEquiv.surjective, ?_, ?_, ?_⟩
  · intro g v
    change e.linearEquiv (s.space.toRepresentation (e.groupEquiv.symm g) v) =
      σ g (e.linearEquiv v)
    rw [show s.space.toRepresentation (e.groupEquiv.symm g) v =
      (s.space.toRepresentation.comp L.subtype) (e.groupEquiv.symm g) v from rfl,
      e.intertwines, e.groupEquiv.apply_symm_apply]
  · intro g v hv
    have hv0 : v = 0 := e.linearEquiv.injective (hv.trans e.linearEquiv.map_zero.symm)
    rw [hv0, map_zero]
  · intro g v
    change ρ (e.groupEquiv.symm g) v - v ∈ s.space.toSubmodule
    apply s.space_eq.ge
    exact Submodule.subset_span ⟨e.groupEquiv.symm g, (e.groupEquiv.symm g).property,
      v, Submodule.mem_top, rfl⟩

/-- The quotient of the actual moved space has a fixed kernel and trivial outer quotient. -/
noncomputable def modelSection_of_moved_quotient {L : Subgroup D} (s : MovedSection ρ L)
    (e : ActionEquiv (s.action.comp L.subtype) σ) :
    ModelSection ρ (L.subtype.comp e.groupEquiv.symm.toMonoidHom) σ := by
  let U : Subrepresentation (ρ.comp (L.subtype.comp e.groupEquiv.symm.toMonoidHom)) :=
    ⟨s.space.toSubmodule, fun g _ hv => s.space.apply_mem_toSubmodule _ hv⟩
  let q := e.linearEquiv.toLinearMap.comp s.central.toSubmodule.mkQ
  refine ⟨U, q, e.linearEquiv.surjective.comp s.central.toSubmodule.mkQ_surjective,
    ?_, ?_, ?_⟩
  · intro g v
    change e.linearEquiv (s.central.toSubmodule.mkQ
      (s.space.toRepresentation (e.groupEquiv.symm g) v)) =
      σ g (e.linearEquiv (s.central.toSubmodule.mkQ v))
    rw [← Subrepresentation.quotientRepresentation_mk]
    change e.linearEquiv ((s.action.comp L.subtype) (e.groupEquiv.symm g)
      (s.central.toSubmodule.mkQ v)) = _
    rw [e.intertwines, e.groupEquiv.apply_symm_apply]
  · intro g v hv
    have hv0 : s.central.toSubmodule.mkQ v = 0 :=
      e.linearEquiv.injective (hv.trans e.linearEquiv.map_zero.symm)
    have hvfix : v ∈ fixedSpace s.space.toRepresentation L := by
      rw [← s.central_eq]
      exact (Submodule.Quotient.mk_eq_zero _).mp hv0
    exact hvfix (e.groupEquiv.symm g)
  · intro g v
    change ρ (e.groupEquiv.symm g) v - v ∈ s.space.toSubmodule
    apply s.space_eq.ge
    exact Submodule.subset_span ⟨e.groupEquiv.symm g, (e.groupEquiv.symm g).property,
      v, Submodule.mem_top, rfl⟩

omit [Group E] [AddCommGroup X] [Module (ZMod 2) X] in
/-- The two independent diagonal cubics exclude every even field degree. -/
theorem linearThree_degree_odd [Finite D] (F : BinaryField)
    (e : D ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
    (hr : primeRank 3 D ≤ 1) : Odd F.degree := by
  by_contra hn
  have hev : Even F.degree := Nat.not_odd_iff_even.mp hn
  have hh := Theory.SpecificGroups.SignedThreeCubicRank.linear_special F.card_eq hev
  rw [← primeRank_equiv 3 e] at hh
  omega

/-- B.5.1(1ii) gives exactly two identical natural copies over an odd-degree field. -/
theorem doubleThree_model [Finite D] {L : Subgroup D}
    (s : MovedSection ρ L) (F : BinaryField) (whole : L = ⊤)
    (e : ActionEquiv (s.space.toRepresentation.comp L.subtype)
      (repeated (linearNatural F 3) 2)) (hr : primeRank 3 D ≤ 1) : RankOneModel ρ := by
  subst L
  let a := (Subgroup.topEquiv : (⊤ : Subgroup D) ≃* D).symm.trans e.groupEquiv
  have ho := linearThree_degree_odd F a hr
  exact RankOneModel.linearThree F ho 2 (Or.inr rfl) a (modelSection_of_moved s e)
/-- Put the same section into the literal one-coordinate repeated representation. -/
noncomputable def repeatedOneSection {f : E →* D} (h : ModelSection ρ f σ) :
    ModelSection ρ f (repeated σ 1) where
  space := h.space
  projection :=
    { toFun := fun v _ => h.projection v
      map_add' := by intros; funext i; exact map_add _ _ _
      map_smul' := by intros; funext i; exact map_smul _ _ _ }
  surjective := by
    intro v
    obtain ⟨w, hw⟩ := h.surjective (v 0)
    refine ⟨w, ?_⟩
    funext i
    change h.projection w = v i
    simpa only [Subsingleton.elim i (0 : Fin 1)] using hw
  intertwines := by intro g v; funext i; exact h.intertwines g v
  kernel_fixed := by intro g v hv; exact h.kernel_fixed g v (congrFun hv 0)
  quotient_trivial := h.quotient_trivial

/-- A whole-actor natural SL₂ quotient gives the prescribed model section. -/
theorem linearTwo_model_of_moved_quotient {L : Subgroup D}
    (s : MovedSection ρ L) (F : BinaryField) (whole : L = ⊤)
    (e : ActionEquiv (s.action.comp L.subtype) (linearNatural F 2)) : RankOneModel ρ := by
  subst L
  let a := (Subgroup.topEquiv : (⊤ : Subgroup D) ≃* D).symm.trans e.groupEquiv
  exact RankOneModel.linearTwo F a (modelSection_of_moved_quotient s e)

/-- A whole-actor natural SL₃ quotient gives one copy, retaining both extension orientations. -/
theorem linearThree_model_of_moved_quotient [Finite D] {L : Subgroup D}
    (s : MovedSection ρ L) (F : BinaryField) (whole : L = ⊤)
    (e : ActionEquiv (s.action.comp L.subtype) (linearNatural F 3))
    (hr : primeRank 3 D ≤ 1) : RankOneModel ρ := by
  subst L
  let a := (Subgroup.topEquiv : (⊤ : Subgroup D) ≃* D).symm.trans e.groupEquiv
  exact RankOneModel.linearThree F (linearThree_degree_odd F a hr) 1 (Or.inl rfl) a
    (repeatedOneSection (modelSection_of_moved_quotient s e))

/-- On the embedded A₅ the central kernel is fixed; no assertion about an outer involution is made. -/
theorem symmetricFive_model_of_moved_quotient {L : Subgroup D}
    (s : MovedSection ρ L)
    (e : ActionEquiv s.action (BinaryPermutation.naturalRepresentation (Fin 5)))
    (hL : L.map e.groupEquiv.toMonoidHom = alternatingGroup (Fin 5)) : RankOneModel ρ := by
  let U : Subrepresentation (ρ.comp
      (e.groupEquiv.symm.toMonoidHom.comp (alternatingGroup (Fin 5)).subtype)) :=
    ⟨s.space.toSubmodule, fun g _ hv => s.space.apply_mem_toSubmodule _ hv⟩
  have hm (g : alternatingGroup (Fin 5)) : e.groupEquiv.symm g ∈ L := by
    have hg : (g : Equiv.Perm (Fin 5)) ∈ L.map e.groupEquiv.toMonoidHom := by
      rw [hL]; exact g.property
    obtain ⟨x, hx, he⟩ := hg
    have he' : e.groupEquiv.symm g = x := by rw [← he]; exact e.groupEquiv.symm_apply_apply x
    exact he' ▸ hx
  let q := e.linearEquiv.toLinearMap.comp s.central.toSubmodule.mkQ
  refine RankOneModel.symmetricFive e.groupEquiv
    ⟨U, q, e.linearEquiv.surjective.comp s.central.toSubmodule.mkQ_surjective, ?_, ?_, ?_⟩
  · intro g v
    change e.linearEquiv (s.central.toSubmodule.mkQ
      (s.space.toRepresentation (e.groupEquiv.symm g) v)) =
      BinaryPermutation.naturalRepresentation (Fin 5) g
        (e.linearEquiv (s.central.toSubmodule.mkQ v))
    rw [← Subrepresentation.quotientRepresentation_mk]
    change e.linearEquiv ((MovedSection.action ρ s) (e.groupEquiv.symm g) (s.central.toSubmodule.mkQ v)) = _
    rw [e.intertwines, e.groupEquiv.apply_symm_apply]
  · intro g v hv
    have hv0 : s.central.toSubmodule.mkQ v = 0 :=
      e.linearEquiv.injective (hv.trans e.linearEquiv.map_zero.symm)
    have hvfix : v ∈ fixedSpace s.space.toRepresentation L := by
      rw [← s.central_eq]
      exact (Submodule.Quotient.mk_eq_zero _).mp hv0
    exact hvfix ⟨e.groupEquiv.symm g, hm g⟩
  · intro g v
    change ρ (e.groupEquiv.symm g) v - v ∈ s.space.toSubmodule
    apply s.space_eq.ge
    exact Submodule.subset_span ⟨e.groupEquiv.symm g, hm g, v, Submodule.mem_top, rfl⟩
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer.RankOneDispatch
