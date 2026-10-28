module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.SixNodes
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.AdjointBlocks.Integral

/-!
# The actual E6 root and lattice inclusions in E7 and E8

The E6 coordinate roots satisfy two orthogonality equations inside E8; E7
imposes the first. Their real-span inclusions preserve the literal first six
simple roots. Every ambient root in the E6 span satisfies both equations,
which proves saturation and hence preservation of complete root strings.

The root and simple-node injections give integral inclusions of the Cartan-plus-root
Geck bases. No inverse Cartan matrix or division by three occurs.
Source: GLS3 §2.6.2–3 (`refs/KGroup/GLS3/chapter2.tex`), for the exceptional
subsystems in Aschbacher–Smith A.2.17, printed p.39 (`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.HigherRealizations.AdjointBlocks
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

/-- The source roots are literal roots of the E7 coordinate system. -/
def rootE7 : typeE6Roots ↪ typeE7Roots where
  toFun r := ⟨r.val, r.property.1⟩
  inj' _ _ h := Subtype.ext (congrArg (fun r : typeE7Roots => r.val) h)

/-- The source roots are literal roots of the E8 coordinate system. -/
def rootE8 : typeE6Roots ↪ typeE8Roots where
  toFun r := ⟨r.val, r.property.1.1⟩
  inj' _ _ h := Subtype.ext (congrArg (fun r : typeE8Roots => r.val) h)

private theorem span_le_e7 : typeE6RootSpan ≤ typeE7Space := by
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  exact r.property.1.2

private theorem span_orthogonal (x : typeE6RootSpan) :
    dot x.val (basisVector 1 - basisVector 2) = 0 := by
  let K : Submodule ℝ (Vec 8) := LinearMap.ker
    ((dotProductEquiv ℝ (Fin 8)).toLinearMap.flip (basisVector 1 - basisVector 2))
  have h : typeE6RootSpan ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    exact r.property.2
  exact h x.property

/-- The inclusion of real spans is used only to check the integral root strings. -/
def weightE7 : typeE6RootSpan →ₗ[ℝ] typeE7Space := Submodule.inclusion (by exact span_le_e7)

def baseE7 : typeE6RootPairing_base.support ↪ typeE7RootPairing_base.support where
  toFun i := typeE7RootPairing_baseEquiv
    ((typeE6RootPairing_baseEquiv.symm i).castLE (by decide))
  inj' _ _ h := typeE6RootPairing_baseEquiv.symm.injective
    (Fin.castLE_injective (by decide) (typeE7RootPairing_baseEquiv.injective h))

def baseE8 : typeE6RootPairing_base.support ↪ typeE8RootPairing_base.support where
  toFun i := typeE8RootPairing_baseEquiv
    ((typeE6RootPairing_baseEquiv.symm i).castLE (by decide))
  inj' _ _ h := typeE6RootPairing_baseEquiv.symm.injective
    (Fin.castLE_injective (by decide) (typeE8RootPairing_baseEquiv.injective h))

@[simp] theorem baseE7_numbered (i : Fin 6) :
    baseE7 (simpleIndex i) = typeE7RootPairing_baseEquiv (i.castLE (by decide)) := by
  change typeE7RootPairing_baseEquiv
    ((typeE6RootPairing_baseEquiv.symm (typeE6RootPairing_baseEquiv i)).castLE (by decide)) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem baseE8_numbered (i : Fin 6) :
    baseE8 (simpleIndex i) = typeE8RootPairing_baseEquiv (i.castLE (by decide)) := by
  change typeE8RootPairing_baseEquiv
    ((typeE6RootPairing_baseEquiv.symm (typeE6RootPairing_baseEquiv i)).castLE (by decide)) = _
  rw [Equiv.symm_apply_apply]

/-- The root and Cartan inclusions satisfy every based-subsystem condition in E7. -/
def e7Embedding : BasedEmbedding typeE6RootPairing_base typeE7RootPairing_base where
  index := rootE7
  weight := weightE7
  injective := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : typeE7Space => z.val) h)
  root _ := rfl
  saturated x hx := by
    obtain ⟨r, hr⟩ := hx
    have hv : r.val = x.val := congrArg Subtype.val hr
    have hx7 : x.val ∈ typeE7Roots := hv ▸ r.property
    refine ⟨⟨x.val, hx7, span_orthogonal x⟩, ?_⟩
    apply Subtype.ext
    rfl
  base := baseE7
  base_root i := by
    obtain ⟨i, rfl⟩ := typeE6RootPairing_baseEquiv.surjective i
    change rootE7 (simpleIndex i) = (baseE7 (simpleIndex i) : typeE7Roots)
    rw [baseE7_numbered]
    apply Subtype.ext
    rfl
  cartan i j := by
    obtain ⟨i, rfl⟩ := typeE6RootPairing_baseEquiv.surjective i
    obtain ⟨j, rfl⟩ := typeE6RootPairing_baseEquiv.surjective j
    change typeE7RootPairing_base.cartanMatrix
      (baseE7 (simpleIndex i)) (baseE7 (simpleIndex j)) = _
    rw [baseE7_numbered, baseE7_numbered,
      typeE7RootPairing_base_cartan_apply, typeE6RootPairing_base_cartan_apply]
    exact e7_cartan_restrict i j

/-- The same integral block inside E8, with all root-span conditions proved. -/
def e8Embedding : BasedEmbedding typeE6RootPairing_base typeE8RootPairing_base where
  index := rootE8
  weight := typeE6RootSpan.subtype
  injective := Subtype.val_injective
  root _ := rfl
  saturated x hx := by
    obtain ⟨r, hr⟩ := hx
    have hv : r.val = x.val := hr
    have hx8 : x.val ∈ typeE8Roots := hv ▸ r.property
    refine ⟨⟨x.val, ⟨hx8, span_le_e7 x.property⟩, span_orthogonal x⟩, ?_⟩
    apply Subtype.ext
    rfl
  base := baseE8
  base_root i := by
    obtain ⟨i, rfl⟩ := typeE6RootPairing_baseEquiv.surjective i
    change rootE8 (simpleIndex i) = (baseE8 (simpleIndex i) : typeE8Roots)
    rw [baseE8_numbered]
    apply Subtype.ext
    rfl
  cartan i j := by
    obtain ⟨i, rfl⟩ := typeE6RootPairing_baseEquiv.surjective i
    obtain ⟨j, rfl⟩ := typeE6RootPairing_baseEquiv.surjective j
    change typeE8RootPairing_base.cartanMatrix
      (baseE8 (simpleIndex i)) (baseE8 (simpleIndex j)) = _
    rw [baseE8_numbered, baseE8_numbered,
      typeE8RootPairing_base_cartan_apply, typeE6RootPairing_base_cartan_apply]
    exact e8_cartan_restrict i j

@[simp] theorem e7Embedding_base_numbered (i : Fin 6) :
    e7Embedding.base (simpleIndex i) = typeE7RootPairing_baseEquiv (i.castLE (by decide)) :=
  baseE7_numbered i

@[simp] theorem e8Embedding_base_numbered (i : Fin 6) :
    e8Embedding.base (simpleIndex i) = typeE8RootPairing_baseEquiv (i.castLE (by decide)) :=
  baseE8_numbered i

/-- Inclusion of the 78 integral E6 basis vectors among the 133 E7 basis vectors. -/
abbrev e7Lattice := inclusion e7Embedding.indexMap

/-- Inclusion of the 78 integral E6 basis vectors among the 248 E8 basis vectors. -/
abbrev e8Lattice := inclusion e8Embedding.indexMap

end TwistedE6.FoldedSubsystem.HigherRealizations.AdjointBlocks
