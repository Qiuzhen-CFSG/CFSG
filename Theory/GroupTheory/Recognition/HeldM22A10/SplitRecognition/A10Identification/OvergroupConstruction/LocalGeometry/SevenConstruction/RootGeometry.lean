module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SourceContracts

/-!
# The root-centralizer geometry needed for Held's seven-point extension

`RootGeometry` records an actual internal factor W of `C_G(uv)`, its
extension by `mu'` as S7, the even subgroup, and the transposition assertion
of Held 5.10. Its centralizer equality is in the full ambient group.
Constructing this witness from the original local hypotheses is the
substantial source argument of 5.3–5.10; no existence is asserted here.

`SevenMarking` is the separate finite permutation problem of choosing the
seven letters compatibly with the specified S6 and four transpositions.
It contains neither the root action nor an ambient centralizer assertion.
The source assembly must construct both witnesses and prove those further
clauses before constructing `Source.SevenLocalData`.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, 5.4–5.5, 5.10 and the beginning of 5.11.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e)

/-- The internal A7 factor and its symmetric extension, before choosing letters.
The actual A7 identification is encoded by `even_subgroup` and `symmetricEquiv`.
This is an intermediate hypothesis, not a recognition theorem. -/
public structure RootGeometry where
  W : Subgroup G
  A_le : L.A ≤ W
  centralizer_root : centralizer ({L.u * L.v} : Set G) = zpowers (L.u * L.v) ⊔ W
  root_disjoint : Disjoint (zpowers (L.u * L.v)) W
  mu'_normalizes : mu' D e ∈ normalizer (W : Set G)
  symmetricEquiv : (W ⊔ zpowers (mu' D e) : Subgroup G) ≃* Perm (Fin 7)
  even_subgroup : (alternatingGroup (Fin 7)).comap symmetricEquiv.toMonoidHom =
    W.subgroupOf (W ⊔ zpowers (mu' D e))
  transpositions : ∀ x : (W ⊔ zpowers (mu' D e) : Subgroup G),
    (x : G) ∈ ({mu' D e, L.v * mu' D e, pi D e * mu D e * mu' D e, xi D e} : Set G) →
      (symmetricEquiv x).IsSwap

/-- A compatible choice of letters in an already identified symmetric extension.
Existence is a finite permutation statement, not assumed by `RootGeometry`. -/
public structure SevenMarking (R : RootGeometry D e L) where
  embedding : Perm (Fin 7) →* G
  injective : Function.Injective embedding
  range : embedding.range = R.W ⊔ zpowers (mu' D e)
  even_range : (alternatingGroup (Fin 7)).map embedding = R.W
  six_range : (MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7)).map embedding =
    L.A ⊔ zpowers (mu' D e)
  six_even_range : (alternatingGroup (Fin 7) ⊓
    MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7)).map embedding = L.A
  mark_mu' : embedding (swap 0 1) = mu' D e
  mark_v_mu' : embedding (swap 1 2) = L.v * mu' D e
  mark_pi_mu_mu' : embedding (swap 2 3) = pi D e * mu D e * mu' D e
  mark_xi : embedding (swap 4 5) = xi D e

/-- The finite subgroup that remains after removing the inverted order-three
factor from the ambient root centralizer. Both transpositions are fixed
individually, and the intersection is taken with the actual alternating group. -/
@[expose] public def evenPairCentralizer : Subgroup (Perm (Fin 7)) :=
  alternatingGroup (Fin 7) ⊓ centralizer ({swap 0 1, swap 4 5} : Set (Perm (Fin 7)))

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
