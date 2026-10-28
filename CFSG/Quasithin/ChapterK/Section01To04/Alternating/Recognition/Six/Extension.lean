module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Inputs
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# Recovering the marked S₆ extension

An intertwiner on a normal A₆ subgroup puts the ambient operators in the
normalizer of its actual natural image. Once the model normalizer is known,
faithfulness recovers an embedding of the ambient group into S₆. Its image
contains A₆. An odd element then gives all of S₆, and the same embedding
identifies the original normal subgroup with the alternating subgroup.

Only the intrinsic linear-normalizer calculation is an explicit premise;
the group extension, its surjectivity, and its marking are constructed here.
Source: Aschbacher–Smith, K.1–K.1.1, printed p.452.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.QuasisimpleSource RecognitionInputs.Six
open Representation.Hexacode.SixDimensional

/-- The model symmetric group is faithfully represented on the actual natural section. -/
theorem six_naturalLinearAction_injective : Function.Injective naturalLinearAction :=
  coordinateAction_injective _ _
    (BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide))

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

/-- The concrete normalizer calculation supplies the entire marked ambient
extension; it is unnecessary to assume an extension or an ambient isomorphism. -/
theorem six_extension_of_normalizer (hn : RecognitionInputs.Six.Normalizer)
    [L.Normal] (hf : Function.Injective ρ)
    (e : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 6)) :
    L = ⊤ ∨ Nonempty (MarkedActionEquiv ρ ⊤ L
      (BinaryPermutation.naturalRepresentation (Fin 6)) (alternatingGroup (Fin 6))) := by
  classical
  let f := coordinateAction ρ e.linearEquiv
  have he (l : L) : f l = naturalLinearAction (e.groupEquiv l).val := by
    apply LinearEquiv.ext
    intro w
    change e.linearEquiv ((ρ.comp L.subtype) l (e.linearEquiv.symm w)) =
      alternatingNatural 6 (e.groupEquiv l) w
    rw [e.intertwines, e.linearEquiv.apply_symm_apply]
  have himage : L.map f = alternatingLinearImage := by
    ext t
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨e.groupEquiv ⟨l, hl⟩, (he ⟨l, hl⟩).symm⟩
    · rintro ⟨l, rfl⟩
      refine ⟨(e.groupEquiv.symm l).val, (e.groupEquiv.symm l).property, ?_⟩
      rw [he, e.groupEquiv.apply_symm_apply]
      rfl
  have hmem (g : G) : f g ∈ naturalLinearAction.range := by
    rw [← hn, ← himage]
    apply Subgroup.le_normalizer_map f
    exact ⟨g, by rw [L.normalizer_eq_top]; trivial, rfl⟩
  let j := f.codRestrict naturalLinearAction.range hmem
  let a : G →* Equiv.Perm (Fin 6) :=
    (MonoidHom.ofInjective six_naturalLinearAction_injective).symm.toMonoidHom.comp j
  have ha (g : G) : naturalLinearAction (a g) = f g :=
    MonoidHom.apply_ofInjective_symm six_naturalLinearAction_injective (j g)
  have hai : Function.Injective a := by
    intro g h hh
    apply coordinateAction_injective ρ e.linearEquiv hf
    rw [← ha, ← ha, hh]
  have hal (l : L) : a l = (e.groupEquiv l).val := by
    apply six_naturalLinearAction_injective
    rw [ha, he]
  have hr : alternatingGroup (Fin 6) ≤ a.range := by
    intro l hl
    refine ⟨(e.groupEquiv.symm ⟨l, hl⟩).val, ?_⟩
    rw [hal, e.groupEquiv.apply_symm_apply]
  have hpre (g : G) : a g ∈ alternatingGroup (Fin 6) ↔ g ∈ L := by
    constructor
    · intro hg
      let l := e.groupEquiv.symm ⟨a g, hg⟩
      have hx : a l.val = a g := by
        rw [hal]
        exact congrArg Subtype.val (e.groupEquiv.apply_symm_apply ⟨a g, hg⟩)
      exact (hai hx) ▸ l.property
    · intro hg
      rw [hal ⟨g, hg⟩]
      exact (e.groupEquiv ⟨g, hg⟩).property
  by_cases hL : L = ⊤
  · exact Or.inl hL
  right
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ L := by
    by_contra h
    apply hL
    ext g
    simp_all
  have hodd : Equiv.Perm.sign (a g) = -1 :=
    (Int.units_eq_one_or _).resolve_left (fun h => hg ((hpre g).mp h))
  have hs : Function.Surjective a := by
    intro x
    apply show x ∈ a.range from ?_
    rcases Int.units_eq_one_or (Equiv.Perm.sign x) with hx | hx
    · exact hr hx
    · have hy : x * (a g)⁻¹ ∈ a.range :=
        hr (by simp [Equiv.Perm.mem_alternatingGroup, hx, hodd])
      simpa using a.range.mul_mem hy (show a g ∈ a.range from ⟨g, rfl⟩)
  let A : G ≃* Equiv.Perm (Fin 6) := MulEquiv.ofBijective a ⟨hai, hs⟩
  refine ⟨{
    action := {
      groupEquiv := Subgroup.topEquiv.trans A
      linearEquiv := e.linearEquiv
      intertwines := ?_ }
    contained := le_top
    subgroupEquiv := e.groupEquiv
    compatible := ?_ }⟩
  · intro g v
    have hh := LinearEquiv.congr_fun (ha g.val) (e.linearEquiv v)
    change BinaryPermutation.naturalRepresentation (Fin 6) (a g.val) (e.linearEquiv v) =
      e.linearEquiv (ρ g.val (e.linearEquiv.symm (e.linearEquiv v))) at hh
    simpa [A, MulEquiv.ofBijective, Equiv.ofBijective] using hh.symm
  · intro l
    exact hal l

end CFSG.Quasithin.ChapterK.Alternating
