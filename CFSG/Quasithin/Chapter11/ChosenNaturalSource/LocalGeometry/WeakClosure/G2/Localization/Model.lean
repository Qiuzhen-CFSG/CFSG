module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization.SmallDisplacement
public import Theory.Representation.G2NaturalOffenders.Coordinates

/-!
# Fixed families in the actual G₂ point radical

The five-root subgroup omitting E acts on the upper natural three-space
by shears into its first line. The displacement homomorphism therefore
has image of order at most the field order. The source A_k condition for
k > n forces fixation of every vector of that three-space, including
through any original central cover with exact fixed-vector lifting.

The root formulas come from the attributed ATLAS octonion implementation;
see LICENSES/ATLAS.txt. The original R₁ application is in Localization.Source.
Source: Aschbacher--Smith B.4.6(12) and 11.2.2(6), printed pp.89,768.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization
open Atlas.G2 Atlas.G2.Restricted.NaturalCoordinates Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

private def axis : Submodule F (Fin 6 → F) where
  carrier := {v | ∀ i, i ≠ 0 → v i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [hx i hi, hy i hi]
  smul_mem' := by intro c x hx i hi; simp [hx i hi]

private def axisEquiv : axis (F := F) ≃ F where
  toFun v := v.val 0
  invFun t := ⟨Pi.single 0 t, by intro i hi; simp [hi]⟩
  left_inv v := by
    apply Subtype.ext
    ext i
    by_cases hi : i = 0
    · subst i; simp
    · simp [hi, v.property i hi]
  right_inv t := by simp

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem radical_displacement {g : Model F} (hg : g ∈ radical₂)
    {v : Fin 6 → F} (hv : v ∈ NaturalOffenders.upper) :
    action F g v - v ∈ axis := by
  obtain ⟨t,ht,rfl⟩ := hg
  intro i hi
  fin_cases i <;> simp_all [unipotentProduct, map_mul, Module.End.mul_apply,
    NaturalOffenders.mem_upper, Pi.sub_apply]

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem radical_fixes_axis {g : Model F} (hg : g ∈ radical₂)
    {v : Fin 6 → F} (hv : v ∈ axis) : action F g v = v := by
  obtain ⟨t,ht,rfl⟩ := hg
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  have h4 := hv 4 (by decide)
  have h5 := hv 5 (by decide)
  ext i
  fin_cases i <;> simp [unipotentProduct, map_mul, Module.End.mul_apply, h1,h2,h3,h4,h5]

/-- B.4.6(12) on the actual five-root point radical: an A_k actor with
k > n fixes the upper three-space, also through any fixed-lifting cover. -/
theorem radical_family_fixes_upper
    {H X : Type*} [Group H] [Finite H] [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) H X)
    (ρ : Representation (ZMod 2) H (Fin 6 → F))
    (q : X →ₗ[ZMod 2] (Fin 6 → F)) (hq : Function.Surjective q)
    (he : ∀ a x, q (σ a x) = ρ a (q x))
    {A : Subgroup H} {k n : ℕ} (hA : A ∈ fixedSpaceFamily σ k)
    (hF : Nat.card F = 2 ^ n) (hn : n < k)
    (j : A →* Model F) (hj : j.range ≤ radical₂)
    (hact : ∀ a : A, ∀ v, ρ a v = action F (j a) v)
    (hlift : ∀ a : A, ∀ x, ρ a (q x) = q x → σ a x = x)
    (v : Fin 6 → F) (hv : v ∈ NaturalOffenders.upper) :
    ∀ a : A, ρ a v = v := by
  apply fixes_of_small_displacement σ ρ q hq he hA hn
    ((axis (F := F)).restrictScalars (ZMod 2)) _ v _ _ hlift
  · exact (Nat.card_congr (axisEquiv (F := F))).trans hF |>.le
  · intro a
    rw [hact]
    exact radical_displacement (hj ⟨a,rfl⟩) hv
  · intro a u hu
    rw [hact]
    exact radical_fixes_axis (hj ⟨a,rfl⟩) hu
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization
