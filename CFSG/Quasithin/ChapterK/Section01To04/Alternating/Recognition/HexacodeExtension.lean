module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Contracts
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.Normalizer

/-!
# The permitted ambient extension of the hexacode action

An actual intertwiner on the normal component identifies its binary image.
The proved binary normalizer theorem embeds the entire faithful ambient actor
in the concrete hexacode automorphism group. The even subgroup has index two,
so the image is either the even subgroup or the entire group. The constructed
full action equivalence retains the original component marking.

This is the extension step in Aschbacher–Smith, K.1.3, printed p.453.
The restricted representation is explicit here; it is constructed from the
six-dimensional hypothesis by `hexacodeAction_of_dimension`.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Atlas.Codes Representation.Hexacode.SixDimensional
namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

/-- A recognized even action determines its only permitted ambient extension. -/
theorem hexacode_extension [L.Normal] (hf : Function.Injective ρ)
    (e : ActionEquiv (ρ.comp L.subtype) Hexacode.evenAction) :
    L = ⊤ ∨ Nonempty (MarkedActionEquiv ρ ⊤ L Hexacode.action hexSign.ker) := by
  classical
  let f := coordinateAction ρ e.linearEquiv
  have he (l : L) : f l = hexAction (e.groupEquiv l).val := by
    apply LinearEquiv.ext
    intro w
    change e.linearEquiv ((ρ.comp L.subtype) l (e.linearEquiv.symm w)) =
      Hexacode.evenAction (e.groupEquiv l) w
    rw [e.intertwines, e.linearEquiv.apply_symm_apply]
  have himage : L.map f = evenBinaryImage := by
    ext t
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨e.groupEquiv ⟨l, hl⟩, (he ⟨l, hl⟩).symm⟩
    · rintro ⟨l, rfl⟩
      refine ⟨(e.groupEquiv.symm l).val, (e.groupEquiv.symm l).property, ?_⟩
      rw [he, e.groupEquiv.apply_symm_apply]
      rfl
  have hmem (g : G) : f g ∈ hexAction.range := by
    rw [← normalizer_evenBinaryImage, ← himage]
    apply Subgroup.le_normalizer_map f
    exact ⟨g, by rw [L.normalizer_eq_top]; trivial, rfl⟩
  let j := f.codRestrict hexAction.range hmem
  let a : G →* HexAutomorphisms :=
    (MonoidHom.ofInjective hexAction_injective).symm.toMonoidHom.comp j
  have ha (g : G) : hexAction (a g) = f g :=
    MonoidHom.apply_ofInjective_symm hexAction_injective (j g)
  have hai : Function.Injective a := by
    intro g h hh
    apply coordinateAction_injective ρ e.linearEquiv hf
    rw [← ha, ← ha, hh]
  have hal (l : L) : a l = (e.groupEquiv l).val := by
    apply hexAction_injective
    rw [ha, he]
  have hr : hexSign.ker ≤ a.range := by
    intro l hl
    refine ⟨(e.groupEquiv.symm ⟨l, hl⟩).val, ?_⟩
    rw [hal, e.groupEquiv.apply_symm_apply]
  have hpre (g : G) : a g ∈ hexSign.ker ↔ g ∈ L := by
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
  have hodd : hexSign (a g) = -1 :=
    (Int.units_eq_one_or _).resolve_left (fun h => hg ((hpre g).mp h))
  have hs : Function.Surjective a := by
    intro x
    apply show x ∈ a.range from ?_
    rcases Int.units_eq_one_or (hexSign x) with hx | hx
    · exact hr hx
    · have hy : x * (a g)⁻¹ ∈ a.range := hr (by simp [MonoidHom.mem_ker, hx, hodd])
      simpa using a.range.mul_mem hy (show a g ∈ a.range from ⟨g, rfl⟩)
  let A : G ≃* HexAutomorphisms := MulEquiv.ofBijective a ⟨hai, hs⟩
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
    change Hexacode.action (a g.val) (e.linearEquiv v) =
      e.linearEquiv (ρ g.val (e.linearEquiv.symm (e.linearEquiv v))) at hh
    simpa [A, MulEquiv.ofBijective, Equiv.ofBijective] using hh.symm
  · intro l
    exact hal l
end CFSG.Quasithin.ChapterK.Alternating
