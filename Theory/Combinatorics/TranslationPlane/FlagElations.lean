module
public import Theory.Combinatorics.TranslationPlane.ProjectiveCompletion
public import Theory.Combinatorics.CollineationAction

/-!
# Flag elations and their affine evaluation

Collineations fixing an axis pointwise and its incident center pencil form
a subgroup. Evaluation at any point off the axis is injective, and its image
lies on the joining line, so the subgroup has at most q elements in a plane
of order q. A subgroup of q such elations is consequently the full flag
elation subgroup. This is the uniqueness step used to synchronize source
and matrix root coordinates, including the plane of order two.

Source: Wagner, On perspectivities of finite projective planes, Section 2;
DGS, Groups and Graphs, centerfree branch of 10.5 and Theorem D.
-/

@[expose] public noncomputable section
namespace Configuration.TranslationPlane
open Collineation
variable {P L : Type*} [Membership P L]

/-- All collineations fixing the axis pointwise and the center pencil. -/
def flagElations (C : P) (l : L) : Subgroup (Collineation P L) where
  carrier := {g | (∀ p : P, p ∈ l → pointHom P L g p = p) ∧
    ∀ m : L, C ∈ m → lineHom P L g m = m}
  one_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  mul_mem' := by
    intro g h hg hh
    constructor
    · intro p hp
      change pointHom P L g (pointHom P L h p) = p
      rw [hh.1 p hp,hg.1 p hp]
    · intro m hm
      change lineHom P L g (lineHom P L h m) = m
      rw [hh.2 m hm,hg.2 m hm]
  inv_mem' := by
    intro g hg
    constructor
    · intro p hp
      change (pointHom P L g).symm p = p
      exact (Equiv.symm_apply_eq _).mpr (hg.1 p hp).symm
    · intro m hm
      change (lineHom P L g).symm m = m
      exact (Equiv.symm_apply_eq _).mpr (hg.2 m hm).symm

/-- Conjugating a flag elation transports its actual center and axis. -/
theorem flagElations_conjugate_mem_iff (C : P) (l : L) (a g : Collineation P L) :
    a * g * a⁻¹ ∈ flagElations (pointHom P L a C) (lineHom P L a l) ↔
      g ∈ flagElations C l := by
  constructor
  · intro hg
    constructor
    · intro p hp
      have hh := hg.1 (pointHom P L a p) ((Collineation.mem_iff a p l).mpr hp)
      change pointHom P L a (pointHom P L g ((pointHom P L a).symm
        (pointHom P L a p))) = pointHom P L a p at hh
      rw [Equiv.symm_apply_apply] at hh
      exact (pointHom P L a).injective hh
    · intro m hm
      have hh := hg.2 (lineHom P L a m) ((Collineation.mem_iff a C m).mpr hm)
      change lineHom P L a (lineHom P L g ((lineHom P L a).symm
        (lineHom P L a m))) = lineHom P L a m at hh
      rw [Equiv.symm_apply_apply] at hh
      exact (lineHom P L a).injective hh
  · intro hg
    constructor
    · intro p hp
      have hp' : (pointHom P L a).symm p ∈ l := by
        apply (Collineation.mem_iff a _ l).mp
        simpa only [Equiv.apply_symm_apply] using hp
      change pointHom P L a (pointHom P L g ((pointHom P L a).symm p)) = p
      rw [hg.1 _ hp',Equiv.apply_symm_apply]
    · intro m hm
      have hm' : C ∈ (lineHom P L a).symm m := by
        apply (Collineation.mem_iff a C _).mp
        simpa only [Equiv.apply_symm_apply] using hm
      change lineHom P L a (lineHom P L g ((lineHom P L a).symm m)) = m
      rw [hg.2 _ hm',Equiv.apply_symm_apply]

/-- The entire flag subgroup follows the same incidence conjugation. -/
theorem flagElations_map_conj (C : P) (l : L) (a : Collineation P L) :
    (flagElations C l).map (MulAut.conj a).toMonoidHom =
      flagElations (pointHom P L a C) (lineHom P L a l) := by
  apply le_antisymm
  · rintro _ ⟨g,hg,rfl⟩
    exact (flagElations_conjugate_mem_iff C l a g).mpr hg
  · intro y hy
    obtain ⟨g,rfl⟩ := (MulAut.conj a).surjective y
    exact Subgroup.mem_map_of_mem _ ((flagElations_conjugate_mem_iff C l a g).mp hy)

local instance pointAction : MulAction (Collineation P L) P :=
  MulAction.compHom P (pointHom P L)
local instance lineAction : MulAction (Collineation P L) L :=
  MulAction.compHom L (lineHom P L)
local instance collineationAction : IsCollineationAction (Collineation P L) P L where
  smul_mem_smul_iff := mem_iff

private theorem flagElations_isElation (C : P) (l : L) (hCl : C ∈ l)
    (g : flagElations C l) (hg : g ≠ 1) : IsElation (g : Collineation P L) C l := by
  refine ⟨hCl,g.property.1,g.property.2,?_⟩
  by_contra! hm
  apply hg
  apply Subtype.ext
  apply Collineation.ext
  · exact hm.1
  · exact hm.2

variable [Finite P] [Finite L] [ProjectivePlane P L]

/-- Evaluation at a single off-axis point determines the entire flag elation. -/
theorem flagElations_evaluation_injective (C : P) (l : L) (hCl : C ∈ l)
    (o : P) (ho : o ∉ l) :
    Function.Injective (fun g : flagElations C l => pointHom P L g o) := by
  intro a b hab
  by_contra hne
  have hd : b⁻¹ * a ≠ 1 := fun hh => hne (inv_mul_eq_one.mp hh).symm
  have he := flagElations_isElation C l hCl (b⁻¹*a) hd
  apply he.smul_ne_of_not_mem_axis ho
  change (pointHom P L b).symm (pointHom P L a o) = o
  change pointHom P L (a : Collineation P L) o = pointHom P L (b : Collineation P L) o at hab
  rw [hab,Equiv.symm_apply_apply]

/-- The full flag elation subgroup has at most one field parameter's worth of elements. -/
theorem flagElations_card_le (C : P) (l : L) (hCl : C ∈ l)
    (o : P) (ho : o ∉ l) : Nat.card (flagElations C l) ≤ ProjectivePlane.order P L := by
  have hoC : o ≠ C := fun he => ho (he ▸ hCl)
  let m : L := HasLines.mkLine hoC
  have hom : o ∈ m := (HasLines.mkLine_ax hoC).1
  have hCm : C ∈ m := (HasLines.mkLine_ax hoC).2
  have hml : m ≠ l := fun he => ho (he ▸ hom)
  let f : flagElations C l → {p : P // p ∈ m ∧ p ∉ l} := fun g =>
    ⟨pointHom P L g o,by
      have hh := (Collineation.mem_iff (g : Collineation P L) o m).mpr hom
      rwa [g.property.2 m hCm] at hh,by
      intro hp
      have hf := g.property.1 _ hp
      have hh := (pointHom P L (g : Collineation P L)).injective hf
      exact ho (hh ▸ hp)⟩
  have hinj : Function.Injective f := by
    intro g h he
    exact flagElations_evaluation_injective C l hCl o ho (congrArg Subtype.val he)
  have hc := Nat.card_le_card_of_injective f hinj
  rwa [card_line_off_axis l m C hCl hCm hml] at hc

/-- Any q-element subgroup of flag elations exhausts the full geometric root group. -/
theorem eq_flagElations_of_card (C : P) (l : L) (hCl : C ∈ l)
    (o : P) (ho : o ∉ l) (R : Subgroup (Collineation P L))
    (hR : R ≤ flagElations C l) (hc : Nat.card R = ProjectivePlane.order P L) :
    R = flagElations C l := by
  apply Subgroup.eq_of_le_of_card_ge hR
  rw [hc]
  exact flagElations_card_le C l hCl o ho

end Configuration.TranslationPlane
