module

public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Flags

/-!
# Comparing intersected binary chief sections

For literal sections R/V and B/N with V ≤ N, the coordinates on R ∩ B
induce a surjective equivariant map from its image in R/V to its image
in B/N. The kernel is precisely the image of R ∩ N. This construction
retains both quotient maps and works under a common subgroup of the two
actors. An irreducible noncentral target then gives an actual chief
interval in the first module's invariant-subspace lattice.

Source application: the second noncentral L₁-factor of R/V in
Aschbacher–Smith 14.7.23(2), printed pp.1050–1051, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G]

/-- Compare the images of intersecting literal sections. The induced
intertwiner is onto, and its kernel is exactly the image of the second
section's denominator in the first section. -/
theorem exists_intersection_intertwiner
    {J H A R V B N : Subgroup G} (hAJ : A ≤ J) (hAH : A ≤ H)
    {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    {τ : Representation (ZMod 2) J X} {σ : Representation (ZMod 2) H Y}
    (s : BinaryConjugationSection J R V τ) (t : BinaryConjugationSection H B N σ)
    (hVN : V ≤ N)
    (D₀ D₁ : Subrepresentation (τ.comp (inclusion hAJ)))
    (D : Subrepresentation (σ.comp (inclusion hAH)))
    (h₀ : D₀.toSubmodule = s.imageSpace N) (h₁ : D₁.toSubmodule = s.imageSpace B)
    (hD : D.toSubmodule = t.imageSpace R) :
    ∃ f : D₁.toRepresentation.IntertwiningMap D.toRepresentation,
      Function.Surjective f ∧ ∀ x : D₁.toSubmodule, f x = 0 ↔ (x : X) ∈ D₀ := by
  let I := R ⊓ B
  let q : I →* Multiplicative D₁.toSubmodule := {
    toFun x := Multiplicative.ofAdd ⟨(s.coordinates ⟨x,x.property.1⟩).toAdd,
      h₁.symm ▸ (s.mem_imageSpace_iff B _).mpr ⟨⟨x,x.property.1⟩,x.property.2,rfl⟩⟩
    map_one' := by apply Subtype.ext; exact s.coordinates.map_one
    map_mul' x y := by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd
        (s.coordinates.map_mul ⟨x,x.property.1⟩ ⟨y,y.property.1⟩) }
  let r : I →* Multiplicative D.toSubmodule := {
    toFun x := Multiplicative.ofAdd ⟨(t.coordinates ⟨x,x.property.2⟩).toAdd,
      hD.symm ▸ (t.mem_imageSpace_iff R _).mpr ⟨⟨x,x.property.2⟩,x.property.1,rfl⟩⟩
    map_one' := by apply Subtype.ext; exact t.coordinates.map_one
    map_mul' x y := by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd
        (t.coordinates.map_mul ⟨x,x.property.2⟩ ⟨y,y.property.2⟩) }
  have hq : Function.Surjective q := by
    intro x
    have hx : x.toAdd.val ∈ s.imageSpace B := h₁.le x.toAdd.property
    obtain ⟨a,ha,he⟩ := (s.mem_imageSpace_iff B _).mp hx
    exact ⟨⟨a,a.property,ha⟩,Subtype.ext he⟩
  have hr : Function.Surjective r := by
    intro x
    have hx : x.toAdd.val ∈ t.imageSpace R := hD.le x.toAdd.property
    obtain ⟨a,ha,he⟩ := (t.mem_imageSpace_iff R _).mp hx
    exact ⟨⟨a,ha,a.property⟩,Subtype.ext he⟩
  have hk : q.ker ≤ r.ker := by
    intro x hx
    apply Subtype.ext
    apply (t.coordinates_eq_one_iff _).mpr
    apply hVN
    apply (s.coordinates_eq_one_iff ⟨x,x.property.1⟩).mp
    exact congrArg (fun z : Multiplicative D₁.toSubmodule => (z.toAdd : X)) hx
  let f₀ := q.liftOfSurjective hq ⟨r,hk⟩
  have hf₀ (x : I) : f₀ (q x) = r x := q.liftOfRightInverse_comp_apply _ _ _ x
  let f : D₁.toSubmodule →ₗ[ZMod 2] D.toSubmodule :=
    (AddMonoidHom.toMultiplicative.symm f₀).toZModLinearMap 2
  have hf (x : I) : f (q x).toAdd = (r x).toAdd := hf₀ x
  have hequiv (a : A) (x : D₁.toSubmodule) :
      f (D₁.toRepresentation a x) = D.toRepresentation a (f x) := by
    obtain ⟨v,hv⟩ := hq (Multiplicative.ofAdd x)
    have hx : (q v).toAdd = x := congrArg Multiplicative.toAdd hv
    rw [←hx]
    let y : I := ⟨(a : G)*v*(a : G)⁻¹,
      (mem_normalizer_iff.mp (s.normalized (hAJ a.property)) v).mp v.property.1,
      (mem_normalizer_iff.mp (t.normalized (hAH a.property)) v).mp v.property.2⟩
    have hqy : (q y).toAdd = D₁.toRepresentation a (q v).toAdd :=
      Subtype.ext (s.equivariant (inclusion hAJ a) ⟨v,v.property.1⟩)
    have hry : (r y).toAdd = D.toRepresentation a (r v).toAdd :=
      Subtype.ext (t.equivariant (inclusion hAH a) ⟨v,v.property.2⟩)
    rw [←hqy,hf,hf,hry]
  let f' : D₁.toRepresentation.IntertwiningMap D.toRepresentation :=
    ⟨f,fun a => LinearMap.ext (hequiv a)⟩
  refine ⟨f',?_,?_⟩
  · intro y
    obtain ⟨x,hx⟩ := hr (Multiplicative.ofAdd y)
    exact ⟨(q x).toAdd,(hf x).trans (congrArg Multiplicative.toAdd hx)⟩
  · intro x
    obtain ⟨a,ha⟩ := hq (Multiplicative.ofAdd x)
    have hx : (q a).toAdd = x := congrArg Multiplicative.toAdd ha
    rw [←hx]
    change f (q a).toAdd = 0 ↔ (q a).toAdd.val ∈ D₀.toSubmodule
    rw [hf,Subtype.ext_iff,h₀]
    exact (t.coordinates_eq_one_iff ⟨a,a.property.2⟩).trans
      (s.coordinates_mem_imageSpace_iff_of_kernel_le N hVN ⟨a,a.property.1⟩).symm

open BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- A surjection onto a nontrivial irreducible action identifies a genuine
noncentral chief interval, with the given kernel inside the original action. -/
theorem chief_interval_of_surjective_intertwiner
    {A X Y : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    {τ : Representation (ZMod 2) A X} {ν : Representation (ZMod 2) A Y}
    [ν.IsIrreducible]
    (D₀ D₁ : Subrepresentation τ) (hle : D₀ ≤ D₁)
    (f : D₁.toRepresentation.IntertwiningMap ν) (hf : Function.Surjective f)
    (hk : ∀ x : D₁.toSubmodule, f x = 0 ↔ (x : X) ∈ D₀)
    (hnc : ¬ ∀ a y, ν a y = y) : D₀ ⋖ D₁ ∧ ¬ Central D₀ D₁ := by
  have hne : D₀ ≠ D₁ := by
    intro he
    apply hnc
    intro a y
    obtain ⟨x,rfl⟩ := hf y
    have hz : f x = 0 := (hk x).mpr (he.symm ▸ x.property)
    rw [hz,map_zero]
  refine ⟨⟨lt_of_le_of_ne hle hne,?_⟩,?_⟩
  · intro I h₀ h₁
    let J : Subrepresentation ν := {
      toSubmodule := (I.toSubmodule.comap D₁.toSubmodule.subtype).map f.toLinearMap
      apply_mem_toSubmodule a y hy := by
        obtain ⟨x,hx,rfl⟩ := hy
        exact ⟨D₁.toRepresentation a x,I.apply_mem_toSubmodule a hx,
          IntertwiningMap.isIntertwining _ _ f _ _⟩ }
    rcases eq_bot_or_eq_top J with hb | ht
    · apply h₀.not_ge
      intro x hx
      apply (hk ⟨x,h₁.le hx⟩).mp
      have hm : f ⟨x,h₁.le hx⟩ ∈ J := ⟨⟨x,h₁.le hx⟩,hx,rfl⟩
      rw [hb] at hm
      exact hm
    · apply h₁.not_ge
      intro x hx
      have hm : f ⟨x,hx⟩ ∈ J := ht ▸ Submodule.mem_top
      obtain ⟨y,hy,he⟩ := hm
      change f y = f ⟨x,hx⟩ at he
      change (y : X) ∈ I at hy
      have hz : f (⟨x,hx⟩-y)=0 := by rw [map_sub,he,sub_self]
      have hn : x-(y:X) ∈ I := h₀.le ((hk _).mp hz)
      change x ∈ I.toSubmodule
      simpa only [sub_add_cancel] using I.toSubmodule.add_mem hn hy
  · intro hc
    apply hnc
    intro a y
    obtain ⟨x,rfl⟩ := hf y
    have hz : f (D₁.toRepresentation a x-x)=0 := (hk _).mpr (hc a x x.property)
    rw [map_sub,IntertwiningMap.isIntertwining] at hz
    exact sub_eq_zero.mp hz


end Representation.BinaryConjugationSection
