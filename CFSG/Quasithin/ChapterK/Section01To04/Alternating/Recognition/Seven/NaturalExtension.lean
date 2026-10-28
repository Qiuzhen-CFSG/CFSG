module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Branches
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SevenExtension
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# The marked ambient extension of the natural A₇ six-space

Convert the odd-degree deleted permutation module to its augmentation core.
The checked seven-letter extension theorem embeds the ambient actor faithfully
in S₇ with the prescribed component and the same linear coordinates. Its image
contains A₇, so an element outside the component makes that embedding onto.
Transporting back to the deleted module gives the literal K.1 marked action.

The imported extension theorem proves Aut(A₇) = S₇ and linear centralizer
rigidity internally; it assumes no module catalogue or B.4.2 classification.
The actual source input is connected by `sevenNaturalAction_of_restriction`.

Source: Aschbacher–Smith, K.1–K.1.2, printed p.452 (PDF p.463).
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

/-- The natural restricted action has only the component itself or the
marked full symmetric group as its faithful normal extension. -/
theorem seven_natural_extension [L.Normal] (hf : Function.Injective ρ)
    (e : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 7)) :
    L = ⊤ ∨ Nonempty (MarkedActionEquiv ρ ⊤ L
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) := by
  classical
  let c := BinaryPermutation.coreEquivNatural (Fin 7) (by decide)
  have hc (g : Equiv.Perm (Fin 7)) (v : BinaryPermutation.core (Fin 7)) :
      c (BinaryPermutation.coreRepresentation (Fin 7) g v) =
        BinaryPermutation.naturalRepresentation (Fin 7) g (c v) :=
    BinaryPermutation.coreEquivNatural_equivariant (Fin 7) (by decide) g v
  let eV := e.linearEquiv.trans c.symm
  have he (l : L) (v : V) : eV (ρ l v) =
      BinaryPermutation.alternatingCoreRepresentation (Fin 7) (e.groupEquiv l) (eV v) := by
    apply c.injective
    change c (c.symm (e.linearEquiv (ρ l v))) =
      c (BinaryPermutation.coreRepresentation (Fin 7) (e.groupEquiv l).val (eV v))
    rw [c.apply_symm_apply, hc]
    change e.linearEquiv ((ρ.comp L.subtype) l v) = _
    rw [e.intertwines]
    simp only [eV, LinearEquiv.trans_apply, c.apply_symm_apply]
    rfl
  obtain ⟨f, hfi, hfl, hfv⟩ :=
    CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.ModelExtension.SevenExtension.faithful_extension
      L ρ hf e.groupEquiv eV he
  have hfn (g : G) (v : V) : e.linearEquiv (ρ g v) =
      BinaryPermutation.naturalRepresentation (Fin 7) (f g) (e.linearEquiv v) := by
    have hh := congrArg c (hfv g v)
    rw [hc] at hh
    simpa only [eV, LinearEquiv.trans_apply, c.apply_symm_apply] using hh
  have hpre (g : G) : f g ∈ alternatingGroup (Fin 7) ↔ g ∈ L := by
    constructor
    · intro hg
      let l := e.groupEquiv.symm ⟨f g, hg⟩
      have hx : f l.val = f g := by
        rw [hfl]
        exact congrArg Subtype.val (e.groupEquiv.apply_symm_apply ⟨f g, hg⟩)
      exact (hfi hx) ▸ l.property
    · intro hg
      rw [hfl ⟨g, hg⟩]
      exact (e.groupEquiv ⟨g, hg⟩).property
  have hr : alternatingGroup (Fin 7) ≤ f.range := by
    intro g hg
    refine ⟨(e.groupEquiv.symm ⟨g, hg⟩).val, ?_⟩
    rw [hfl, e.groupEquiv.apply_symm_apply]
  by_cases hL : L = ⊤
  · exact Or.inl hL
  right
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ L := by
    by_contra h
    apply hL
    ext g
    simp_all
  have hodd : f g ∉ alternatingGroup (Fin 7) := fun h => hg ((hpre g).mp h)
  have hs : Function.Surjective f := by
    intro x
    by_cases hx : x ∈ alternatingGroup (Fin 7)
    · exact hr hx
    · have hy : x * (f g)⁻¹ ∈ alternatingGroup (Fin 7) := by
        rw [Subgroup.mul_mem_iff_of_index_two alternatingGroup.index_eq_two,
          Subgroup.inv_mem_iff]
        simp [hx, hodd]
      simpa using f.range.mul_mem (hr hy) (show f g ∈ f.range from ⟨g, rfl⟩)
  let A : G ≃* Equiv.Perm (Fin 7) := MulEquiv.ofBijective f ⟨hfi, hs⟩
  refine ⟨{
    action := {
      groupEquiv := Subgroup.topEquiv.trans A
      linearEquiv := e.linearEquiv
      intertwines := fun g v => hfn g.val v }
    contained := le_top
    subgroupEquiv := e.groupEquiv
    compatible := fun l => hfl l }⟩

/-- Apply the natural normalizer calculation to the actual K.1 source input.
The restricted intertwiner remains the independent representation obligation. -/
theorem sevenNaturalAction_of_restriction [Finite G] {K : GroupClass} (h : Input ρ K L)
    (e : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 7)) :
    Nonempty (NaturalAction ρ L 7) := by
  let : L.Normal := by rw [h.fitting]; infer_instance
  exact ⟨⟨e, seven_natural_extension ρ L h.faithful e⟩⟩

end CFSG.Quasithin.ChapterK.Alternating
