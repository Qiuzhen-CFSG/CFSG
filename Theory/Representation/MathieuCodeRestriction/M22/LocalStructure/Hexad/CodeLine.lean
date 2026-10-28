module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.PairVectors
public import Theory.Representation.MathieuCodeRestriction.CodeLocal
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The hexad code line and a cocode weight-two vector

The proven M24 octad fixed line lies in the M22 code hyperplane whenever the
marked pair belongs to the octad. Exact comparison of the acting kernels
therefore identifies the fixed space with the line of the actual octad word,
for both inner and outer actors. No displacement hypothesis is needed here.

For the compatible source octad the pair {0,7}, with native moving label 2,
gives an actual member of the source weight-two family in the cocode fixed
space. A subspace avoiding this family is proper; once the fixed dimension
is five, its dimension is at most four.

Source: Aschbacher--Smith, H.15.2(3) and H.16.4(1), printed pp.399,403,
combined manuscript of 1 March 2004.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
namespace MathieuCode.Hexad

theorem octadVector_mem_hyperplane (O : Octad) (hp : m22Pair ⊆ O.val) :
    octadVector O ∈ m22Hyperplane := by
  change pairFunctional (octadVector O) = 0
  rw [octadVector, pairFunctional_mk]
  have h0 : (0 : Fin 24) ∈ O.val := hp (by decide +kernel)
  have h9 : (9 : Fin 24) ∈ O.val := hp (by decide +kernel)
  simp [wordOfSet, h0, h9]

def codeVector (O : Octad) (hp : m22Pair ⊆ O.val) : M22Code :=
  ⟨octadVector O, octadVector_mem_hyperplane O hp⟩

theorem codeVector_ne_zero (O : Octad) (hp : m22Pair ⊆ O.val) : codeVector O hp ≠ 0 := by
  intro h
  exact octadVector_ne_zero O (congrArg Subtype.val h)

variable {G : Type*} [Group G] (f : G →* m22PairStabilizer) (K : Subgroup G) (O : Octad)

theorem code_fixedSpace_eq_comap
    (hK : K.map (m22PairStabilizer.subtype.comp f) = octadPointwiseKernel O) :
    fixedSpace (m22OuterCodeRepresentation.comp f) K =
      (fixedSpace codeRepresentation (octadPointwiseKernel O)).comap m22CodeInclusion := by
  rw [← hK]
  ext v
  constructor
  · intro hv
    rintro ⟨g, a, ha, rfl⟩
    exact congrArg Subtype.val (hv ⟨a, ha⟩)
  · intro hv a
    exact Subtype.ext (hv ⟨_, Subgroup.mem_map_of_mem _ a.property⟩)

theorem code_fixedSpace_finrank (hp : m22Pair ⊆ O.val)
    (hK : K.map (m22PairStabilizer.subtype.comp f) = octadPointwiseKernel O) :
    Module.finrank (ZMod 2) (fixedSpace (m22OuterCodeRepresentation.comp f) K) = 1 := by
  rw [code_fixedSpace_eq_comap f K O hK]
  have hle : fixedSpace codeRepresentation (octadPointwiseKernel O) ≤ m22Hyperplane := by
    rw [octad_fixedSpace_eq_span]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (octadVector_mem_hyperplane O hp))
  exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq.trans (octad_fixedSpace_finrank O)

theorem code_fixedSpace_eq_span (hp : m22Pair ⊆ O.val)
    (hK : K.map (m22PairStabilizer.subtype.comp f) = octadPointwiseKernel O) :
    fixedSpace (m22OuterCodeRepresentation.comp f) K =
      Submodule.span (ZMod 2) {codeVector O hp} := by
  apply eq_span_singleton_of_mem_of_finrank_eq_one (code_fixedSpace_finrank f K O hp hK)
    _ (codeVector_ne_zero O hp)
  rw [code_fixedSpace_eq_comap f K O hK]
  exact octadVector_fixed O

theorem evenPair_fixed (g : M24) (i j : Fin 24)
    (hi : g • i = i) (hj : g • j = j) :
    cocodeRepresentation g (codeInCore.mkQ (m22EvenPair i j)) =
      codeInCore.mkQ (m22EvenPair i j) := by
  rw [cocodeRepresentation_mk]
  congr 1
  apply Subtype.ext
  change fullRepresentation g (Pi.single i 1 + Pi.single j 1) = Pi.single i 1 + Pi.single j 1
  ext k
  change (Pi.single i 1 + Pi.single j 1 : Full) (g.val.symm k) =
    (Pi.single i 1 + Pi.single j 1 : Full) k
  have hi' : g.val i = i := hi
  have hj' : g.val j = j := hj
  simp only [Pi.add_apply, Pi.single_apply, Equiv.symm_apply_eq, hi', hj']

theorem cocodePair_mem_fixedSpace (i j : Fin 24) (hi : i ∈ O.val) (hj : j ∈ O.val)
    (hK : K.map (m22PairStabilizer.subtype.comp f) = octadPointwiseKernel O) :
    m22CocodePair i j ∈ fixedSpace (m22OuterCocodeRepresentation.comp f) K := by
  intro a
  have ha : (f a.val).val ∈ octadPointwiseKernel O := by
    rw [← hK]
    exact Subgroup.mem_map_of_mem _ a.property
  change m22OuterCocodeRepresentation (f a.val) (m22CocodePair i j) = m22CocodePair i j
  unfold m22CocodePair
  rw [m22OuterCocodeRepresentation_mk, evenPair_fixed _ _ _
    ((mem_octadPointwiseKernel O _).mp ha i hi)
    ((mem_octadPointwiseKernel O _).mp ha j hj)]

theorem source_fixedSpace_meets_weightTwo
    (hK : K.map (m22PairStabilizer.subtype.comp f) = octadPointwiseKernel m22SourceOctad) :
    ∃ v ∈ fixedSpace (m22OuterCocodeRepresentation.comp f) K, v ∈ m22WeightTwoFamily := by
  refine ⟨m22CocodePair 0 (m22Coordinates 2), ?_, ⟨2, rfl⟩⟩
  exact cocodePair_mem_fixedSpace f K m22SourceOctad _ _ (by decide +kernel) (by decide +kernel) hK

theorem avoiding_weightTwo_finrank_le
    (hK : K.map (m22PairStabilizer.subtype.comp f) = octadPointwiseKernel m22SourceOctad)
    (hd : Module.finrank (ZMod 2) (fixedSpace (m22OuterCocodeRepresentation.comp f) K) = 5)
    (I : Submodule (ZMod 2) M22Cocode)
    (hI : I ≤ fixedSpace (m22OuterCocodeRepresentation.comp f) K)
    (havoid : Disjoint (I : Set M22Cocode) m22WeightTwoFamily) :
    Module.finrank (ZMod 2) I ≤ 4 := by
  have hne : I ≠ fixedSpace (m22OuterCocodeRepresentation.comp f) K := by
    intro he
    obtain ⟨v, hv, hw⟩ := source_fixedSpace_meets_weightTwo f K hK
    exact Set.disjoint_left.mp havoid (he ▸ hv) hw
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hI hne)
  rw [hd] at hlt
  omega

end MathieuCode.Hexad
