module

public import Theory.SpecificGroups.Suzuki.SchurCoverReduction
public import Theory.SpecificGroups.Suzuki.RootOvoidGeometry

/-!
# The marked additive quotient of the Suzuki root group

The first matrix coordinate identifies the root group modulo its derived
subgroup with the additive Suzuki field. Conjugation by the literal split
torus induces multiplication by the torus parameter on this quotient.
These maps are the coordinate input to the central-cover defect calculation.

Source: Huppert--Blackburn III, XI.3.1, in the upper-triangular matrix
convention of `BenderSuzuki.MatrixGroups.Suzuki`.
-/

@[expose] public noncomputable section
namespace BenderSuzuki.MatrixGroups.SchurCover.Family
open Subgroup PFAppendixIII

abbrev Field (m : ℕ) := BinaryGaloisField (2 * m + 1)

/-- The literal root matrix with its two coordinates. -/
def rootPoint (m : ℕ) (a b : Field m) : SuzukiRootSubgroup m :=
  ⟨⟨SuzukiRootGL m a b, suzukiRootClosure_le m (subset_closure ⟨a,b,rfl⟩)⟩,
    subset_closure ⟨a,b,rfl⟩⟩

theorem rootPoint_mul (m : ℕ) (hm : 0 < m) (a b c d : Field m) :
    rootPoint m a b * rootPoint m c d =
      rootPoint m (a+c) (b+d+a*suzukiTits m c) := by
  apply Subtype.ext
  apply Subtype.ext
  exact (External.huppert_blackburn_XI_3_1 m hm (suzukiTits m)
    (suzukiTits_sq m)).2.2.2.2.2.2.2.2.1 a b c d

theorem rootPoint_zero (m : ℕ) : rootPoint m 0 0 = 1 :=
  Subtype.ext (Subtype.ext (External.suzukiRootGL_zero_zero m))

theorem rootPoint_surjective (m : ℕ) (x : SuzukiRootSubgroup m) :
    ∃ a b, x = rootPoint m a b := by
  obtain ⟨a,b,h⟩ := (mem_suzukiRootSubgroup_iff m x.val).mp x.property
  exact ⟨a,b,Subtype.ext (Subtype.ext h)⟩

/-- The first matrix coordinate, with the additive field written multiplicatively. -/
def rootCoordinate (m : ℕ) (hm : 0 < m) :
    SuzukiRootSubgroup m →* Multiplicative (Field m) where
  toFun x := Multiplicative.ofAdd (x.val.val (0 : Fin 4) (1 : Fin 4))
  map_one' := rfl
  map_mul' := by
    intro x y
    obtain ⟨a,b,rfl⟩ := rootPoint_surjective m x
    obtain ⟨c,d,rfl⟩ := rootPoint_surjective m y
    rw [rootPoint_mul m hm]
    rfl

@[simp] theorem rootCoordinate_rootPoint (m : ℕ) (hm : 0 < m) (a b : Field m) :
    rootCoordinate m hm (rootPoint m a b) = Multiplicative.ofAdd a := rfl

theorem rootCoordinate_surjective (m : ℕ) (hm : 0 < m) :
    Function.Surjective (rootCoordinate m hm) :=
  fun a => ⟨rootPoint m a.toAdd 0, rfl⟩

/-- The first-coordinate kernel is exactly the derived subgroup. -/
theorem rootCoordinate_ker (m : ℕ) (hm : 0 < m) :
    (rootCoordinate m hm).ker = _root_.commutator (SuzukiRootSubgroup m) := by
  let e : SuzukiRootSubgroup m ≃* SuzukiRootClosure m :=
    subgroupOfEquivOfLe (suzukiRootClosure_le m)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hz,_⟩ :=
    External.huppert_blackburn_XI_3_1 m hm (suzukiTits m) (suzukiTits_sq m)
  change ∀ x : SuzukiRootClosure m, x ∈ _root_.commutator (SuzukiRootClosure m) ↔
    ∃ b : Field m, x.val = SuzukiRootGL m 0 b at hz
  have hmap : (_root_.commutator (SuzukiRootSubgroup m)).map e.toMonoidHom =
      _root_.commutator (SuzukiRootClosure m) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  have hmem (x : SuzukiRootSubgroup m) :
      x ∈ _root_.commutator (SuzukiRootSubgroup m) ↔
      e x ∈ _root_.commutator (SuzukiRootClosure m) := by
    rw [← hmap]
    exact (mem_map_iff_mem e.injective).symm
  ext x
  rw [hmem, hz]
  obtain ⟨a,b,rfl⟩ := rootPoint_surjective m x
  change Multiplicative.ofAdd a = 1 ↔ ∃ c, SuzukiRootGL m a b = SuzukiRootGL m 0 c
  constructor
  · intro h
    have ha : a = 0 := congrArg Multiplicative.toAdd h
    exact ⟨b, ha ▸ rfl⟩
  · rintro ⟨c,hc⟩
    have ha : a = 0 := congrArg (fun g : GL (Fin 4) (Field m) => g 0 1) hc
    exact congrArg Multiplicative.ofAdd ha

/-- The root group has central derived subgroup in its actual carrier. -/
theorem root_commutator_eq_center (m : ℕ) (hm : 0 < m) :
    _root_.commutator (SuzukiRootSubgroup m) = center (SuzukiRootSubgroup m) := by
  let e : SuzukiRootSubgroup m ≃* SuzukiRootClosure m :=
    subgroupOfEquivOfLe (suzukiRootClosure_le m)
  have hc := (External.huppert_blackburn_XI_3_1 m hm (suzukiTits m)
    (suzukiTits_sq m)).2.2.2.2.2.2.2.2.2.1
  change _root_.commutator (SuzukiRootClosure m) = center (SuzukiRootClosure m) at hc
  apply (map_injective (f := e.toMonoidHom) e.injective)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  change _root_.commutator (SuzukiRootClosure m) = _
  rw [hc]
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x, (centerCongr e).symm ⟨x,hx⟩ |>.property, e.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    exact (centerCongr e ⟨y,hy⟩).property

/-- The literal split torus as a homomorphism from field units. -/
def torusPoint (m : ℕ) (hm : 0 < m) : (Field m)ˣ →* SuzukiMatrixGroup m where
  toFun t := ⟨SuzukiTorusGL m t, suzukiSplitTorusClosure_le m (subset_closure ⟨t,rfl⟩)⟩
  map_one' := Subtype.ext (External.suzukiTorusGL_one m)
  map_mul' t s := by
    obtain ⟨e,he⟩ := (External.huppert_blackburn_XI_3_1 m hm (suzukiTits m)
      (suzukiTits_sq m)).2.2.2.2.2.2.2.2.2.2.2.1
    apply Subtype.ext
    have h := congrArg Subtype.val (e.map_mul t s)
    simpa only [Subgroup.coe_mul, he] using h

@[simp] theorem torusPoint_val (m : ℕ) (hm : 0 < m) (t : (Field m)ˣ) :
    (torusPoint m hm t).val = SuzukiTorusGL m t := rfl

theorem torusPoint_mem (m : ℕ) (hm : 0 < m) (t : (Field m)ˣ) :
    torusPoint m hm t ∈ SuzukiSplitTorus m := subset_closure ⟨t,rfl⟩

theorem torusPoint_conj (m : ℕ) (hm : 0 < m) (t : (Field m)ˣ) (a b : Field m) :
    torusPoint m hm t * (rootPoint m a b).val * (torusPoint m hm t)⁻¹ =
      (rootPoint m (t*a) (t*suzukiTits m t*b)).val := by
  apply Subtype.ext
  exact External.suzukiTorusGL_conj_root m (suzukiTits m) (suzukiTits_sq m)
    (suzukiTits_apply m) a b t

end BenderSuzuki.MatrixGroups.SchurCover.Family
end
