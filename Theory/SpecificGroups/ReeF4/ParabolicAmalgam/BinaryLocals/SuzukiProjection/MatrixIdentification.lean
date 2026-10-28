module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Basic
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Diagonal


/-!
# The fixed binary middle-node Levi is Sz(2)

A representation of the actual split middle-node F₄ Levi that sends its four
signed simple generators to the standard B₂ matrices identifies the generated
graph of the Ree twist with `pairedSubgroup`. If the representation is faithful,
every diagonal pair lifts to an actual fixed element. This proves both
injectivity and surjectivity of the induced comparison with `pairedDiagonal`.

The four-dimensional restriction constructed in `Representation` is faithful
on the whole split Levi, and `Diagonal` proves the concrete identity
`pairedDiagonal = SuzukiMatrixSubgroup 0`. Substituting these results into
`leviMatrixEquivOfComparison` gives the unconditional `leviMatrixEquiv` for
the full fixed subgroup in ²F₄(2). No fixed-point surjectivity for a quotient
is assumed.

Source: the middle-node Levi underlying Aschbacher–Smith F.1.12(I)(5) and its
binary case, printed pp.263–264 (PDF pp.274–275) of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics.BinarySuzuki.MatrixIdentification

open Subgroup

/-- Pair a representation with its composite with the actual Ree twist. -/
def pairedMap (f : splitLevi →* BinaryGL) : splitLevi →* BinaryGL × BinaryGL :=
  f.prod (f.comp splitTwist)

/-- Simple-root compatibility determines the whole generated graph. -/
theorem pairedMap_range (f : splitLevi →* BinaryGL)
    (hgen : ∀ i, f (splitGenerator i) = matrixGenerator i) :
    (pairedMap f).range = pairedSubgroup := by
  rw [MonoidHom.range_eq_map, ← splitGenerator_closure,
    MonoidHom.map_closure, ← Set.range_comp, pairedSubgroup]
  congr 2
  funext i
  apply Prod.ext
  · exact hgen i
  · change f (splitTwist (splitGenerator i)) = matrixGenerator (swapIndex i)
    rw [splitTwist_generator, hgen]

/-- Forget the ambient fixed seed, retaining the exact split Levi element. -/
def forgetToSplitLevi : leviInSeed →* splitLevi where
  toFun x := ⟨toSplitGroup 0 x.val.val, x.property⟩
  map_one' := Subtype.ext (map_one (toSplitGroup 0))
  map_mul' x y := Subtype.ext (map_mul (toSplitGroup 0) x.val.val y.val.val)

theorem forgetToSplitLevi_injective : Function.Injective forgetToSplitLevi := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact toSplitGroup_injective 0 (congrArg Subtype.val h)

@[simp] theorem splitTwist_forget (x : leviInSeed) :
    splitTwist (forgetToSplitLevi x) = forgetToSplitLevi x := by
  apply Subtype.ext
  exact reeTwist_toSplitGroup 0 x.val.val

/-- Reinsert a fixed split Levi element into the specified fixed seed. -/
def ofSplitFixed (x : splitLevi) (hx : splitTwist x = x) : leviInSeed :=
  ⟨⟨⟨x.val, (mem_fixedSubgroup 0 x.val).mpr (congrArg Subtype.val hx)⟩, by
      change toSplitGroup 0 _ ∈ LargeLocalSeeds.splitSeed 0 .suzuki
      rw [toSplitGroup_apply]
      exact splitLevi_le_seed x.property⟩, by
    change toSplitGroup 0 _ ∈ splitLevi
    rw [toSplitGroup_apply]
    exact x.property⟩

@[simp] theorem forget_ofSplitFixed (x : splitLevi) (hx : splitTwist x = x) :
    forgetToSplitLevi (ofSplitFixed x hx) = x := by
  apply Subtype.ext
  exact toSplitGroup_apply 0 _

/-- Restrict a compatible representation to the fixed subgroup. -/
def toPairedDiagonal (f : splitLevi →* BinaryGL)
    (hgen : ∀ i, f (splitGenerator i) = matrixGenerator i) :
    leviInSeed →* pairedDiagonal where
  toFun x := ⟨f (forgetToSplitLevi x), by
    change (f (forgetToSplitLevi x), f (forgetToSplitLevi x)) ∈ pairedSubgroup
    rw [← pairedMap_range f hgen]
    exact ⟨forgetToSplitLevi x,
      Prod.ext rfl (congrArg f (splitTwist_forget x))⟩⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem toPairedDiagonal_injective (f : splitLevi →* BinaryGL)
    (hf : Function.Injective f)
    (hgen : ∀ i, f (splitGenerator i) = matrixGenerator i) :
    Function.Injective (toPairedDiagonal f hgen) := by
  intro x y h
  apply forgetToSplitLevi_injective
  exact hf (congrArg Subtype.val h)

/-- Faithfulness is essential: it turns equal matrix images into actual fixedness. -/
theorem toPairedDiagonal_surjective (f : splitLevi →* BinaryGL)
    (hf : Function.Injective f)
    (hgen : ∀ i, f (splitGenerator i) = matrixGenerator i) :
    Function.Surjective (toPairedDiagonal f hgen) := by
  rintro ⟨a, ha⟩
  change (a, a) ∈ pairedSubgroup at ha
  rw [← pairedMap_range f hgen] at ha
  obtain ⟨x, hx⟩ := ha
  have h1 : f x = a := congrArg Prod.fst hx
  have h2 : f (splitTwist x) = a := congrArg Prod.snd hx
  have hfixed : splitTwist x = x := hf (h2.trans h1.symm)
  refine ⟨ofSplitFixed x hfixed, ?_⟩
  apply Subtype.ext
  change f (forgetToSplitLevi (ofSplitFixed x hfixed)) = a
  rw [forget_ofSplitFixed, h1]

/-- The faithful four-generator comparison identifies the full fixed subgroup. -/
def leviEquivPairedDiagonal (f : splitLevi →* BinaryGL)
    (hf : Function.Injective f)
    (hgen : ∀ i, f (splitGenerator i) = matrixGenerator i) :
    leviInSeed ≃* pairedDiagonal :=
  MulEquiv.ofBijective (toPairedDiagonal f hgen)
    ⟨toPairedDiagonal_injective f hf hgen, toPairedDiagonal_surjective f hf hgen⟩

end ReeF4.Parabolics.BinarySuzuki.MatrixIdentification

namespace ReeF4.Parabolics.BinarySuzuki

open MatrixIdentification

/-- Assemble the comparison after the faithful root representation and the
finite matrix diagonal calculation have both been proved. -/
def leviMatrixEquivOfComparison (f : splitLevi →* BinaryGL)
    (hf : Function.Injective f)
    (hgen : ∀ i, f (splitGenerator i) = matrixGenerator i)
    (hdiag : pairedDiagonal = BenderSuzuki.MatrixGroups.SuzukiMatrixSubgroup 0) :
    leviInSeed ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  (leviEquivPairedDiagonal f hf hgen).trans (MulEquiv.subgroupCongr hdiag)

/-- The actual fixed middle-node Levi in the full ²F₄(2) is the concrete
Suzuki matrix group Sz(2). Faithfulness of the four-space restriction and the
paired matrix calculation discharge every comparison premise. -/
def leviMatrixEquiv :
    leviInSeed ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  leviMatrixEquivOfComparison splitLeviRepresentation
    splitLeviRepresentation_injective splitLeviRepresentation_generator
    pairedDiagonal_eq_suzuki

/-- The equivalence is the restriction of the actual four-dimensional action. -/
@[simp] theorem leviMatrixEquiv_apply_val (x : leviInSeed) :
    (leviMatrixEquiv x).val = splitLeviRepresentation (forgetToSplitLevi x) := rfl

end ReeF4.Parabolics.BinarySuzuki
