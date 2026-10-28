module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Models

/-!
# The local subgroup in the second centralizer

The subgroup is the literal centralizer of `t` in the join of the original
core and its selected left conjugate. Source 4.1 identifies that join with
`M = N_G(⟨z,s⟩)`. The marked model below is only the local conclusion of
4.1; it includes neither ambient Sylow placement nor centralizer containment.
Those follow separately from the long core orbit and a normalizer argument.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemma 4.1 and the opening of 4.2.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer

variable {G : Type*} [Group G]

/-- `C_{⟨Q,gQg⁻¹⟩}(t)`, as a subgroup of the literal `C_G(t)`. -/
@[expose] public def localCentralizer (z t g : G) : Subgroup (Centralizer t) :=
  (coreInG z ⊔ conjugateCore z g).subgroupOf (Centralizer t)

/-- The local marked isomorphism to be constructed from source 4.1.
The distinguished coordinate is specified in the ambient group, so this
contract is independent of the proof used to put `t` in the local subgroup. -/
public structure LocalModelData (z t g : G) where
  equiv : localCentralizer z t g ≃* Model 4
  central : (((equiv.symm (centralInvolution 4)) : Centralizer t) : G) = t
  first : ∀ x : localCentralizer z t g,
    IsConj z ((x : Centralizer t) : G) ↔ FirstClass (equiv x)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
