module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.Target
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.SourceGeometry

/-!+# Source configuration for the marked definite plane

The terminal argument involves two different pairs of planes. The definite
planes are the supported planes of `NaturalOrthogonalAction`. The totally
singular planes `E` and `F` are conjugate graphs between those two summands.
In the binary orthogonal sum of two definite planes, a vector is singular
exactly when its two coordinates are either both zero or both nonzero.

`SourceConfiguration` records earlier source facts and the actual subgroup
constructions used to distinguish the definite planes in the final module.
It is an input to recognition, not an assertion of any numbered theorem.
In particular, it contains no hexacode coordinates, scalar invariance,
Hamming-weight assertion, or plane-orbit assertion. The normalizer of `Y_E`
is taken in the ambient group; it is not replaced by ambient normality of
`Y_E`. All cores and residuals are formed in their indicated subgroups.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), the definite-plane decomposition on printed
pp.1121–1122; 15.3.7 on p.1122; the choice of `E` and 15.3.66–68 on
pp.1152–1155; and the non-`S₃` branch of the final proof on p.1155.
Each group-theoretic input below is tied to one of these earlier clauses.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane

variable {G : Type*} [Group G]

/-- Total singularity in the specified sum of two definite binary planes.
The value `1` is the zero vector in the multiplicative coordinate convention. -/
def IsSingularIn (M V E : Subgroup G) (d : NaturalOrthogonalAction M V) : Prop :=
  E ≤ V ∧ ∀ v : V, (v : G) ∈ E → ∀ i j : OrthogonalPlaneIndex,
    d.coordinates v i = 1 ↔ d.coordinates v j = 1

/-- The earlier configuration used by terminal marked-plane recognition.
The assembly of 15.3.1 must supply these facts; they do not follow just from
an abstract identification of `G₀/O₂(G₀)` with a triple cover of `S₆`. -/
structure SourceConfiguration (G₀ M V : Subgroup G) (d : NaturalOrthogonalAction M V) where
  T : Sylow 2 G
  Mc : Subgroup G
  Y : Subgroup G
  E : Subgroup G
  F : Subgroup G
  YE : Subgroup G
  YF : Subgroup G
  XE : Subgroup G
  TE : Subgroup G
  G1 : Subgroup G
  G2 : Subgroup G
  Q1 : Subgroup G
  R : Subgroup G
  s : G
  /-- The standing choice of `M` containing the ambient Sylow group. -/
  sylow_le : (T : Subgroup G) ≤ M
  /-- The source vector group, fixed before the plane decomposition. -/
  vector_eq : V = localModule T M
  /-- The residual construction in 15.3.7. -/
  residual_eq : Y = residualY M Mc
  /-- The action-image assertion of 15.3.7, through the compatible actor. -/
  residual_image : d.image Y = pResidual 2 OrthogonalActor
  /-- 15.3.67(1). -/
  ambient_product : M = Y ⊔ (T : Subgroup G)
  /-- The order-four choice preceding 15.3.66. -/
  singular_card : Nat.card E = 4
  /-- Total singularity from 15.3.46(2), recalled before 15.3.66. -/
  singular : IsSingularIn M V E d
  /-- The definition preceding 15.3.66. -/
  sylow_stabilizer_eq : TE = (T : Subgroup G) ⊓ normalizer (E : Set G)
  /-- The definition preceding 15.3.66; this is a two-residual. -/
  first_residual_eq : YE = (pResidual 2 ↥(Y ⊓ normalizer (E : Set G) : Subgroup G)).map
    (Y ⊓ normalizer (E : Set G)).subtype
  /-- The definition in 15.3.67(3); this too is a two-residual. -/
  centralizer_residual_eq : XE = (pResidual 2 (centralizer (E : Set G))).map
    (centralizer (E : Set G)).subtype
  /-- The choice `s ∈ S − T_E` following 15.3.67. -/
  conjugator_mem : s ∈ planeStabilizer T (d.plane 1)
  conjugator_not_mem : s ∉ TE
  /-- The source convention `E^s = s⁻¹ E s`. -/
  conjugate_plane_eq : F = E.map (MulAut.conj s⁻¹).toMonoidHom
  /-- The same conjugator must be used for the residual subgroup. -/
  conjugate_residual_eq : YF = YE.map (MulAut.conj s⁻¹).toMonoidHom
  /-- The product displayed immediately before 15.3.68. -/
  residual_product : (Y : Set G) = (YE : Set G) * (YF : Set G) * (Y.pCoreIn 2 : Set G)
  /-- The definitions immediately before 15.3.68. -/
  first_local_eq : G1 = YF ⊔ TE
  second_local_eq : G2 = XE ⊔ TE
  generated_eq : G₀ = G1 ⊔ G2
  first_core_eq : Q1 = G1.pCoreIn 2
  /-- 15.3.67(1), retaining the original definition of `R`. -/
  centralizer_eq : R = centralizer (V : Set G)
  sylow_centralizer_eq : R = (T : Subgroup G) ⊓ centralizer (V : Set G)
  /-- In both alternatives of 15.3.7, `O₂(Y) ≤ C_G(V) = R`. -/
  residual_core_le : Y.pCoreIn 2 ≤ R
  /-- The cyclic quotient in 15.3.67(3). -/
  first_residual_quotient_card : Nat.card (YE ⧸ pCore 2 YE) = 3
  /-- The local quotient displayed immediately before 15.3.68. -/
  first_local_quotient : Nonempty (G1 ⧸ pCore 2 G1 ≃* Equiv.Perm (Fin 3))
  /-- The observation `T_E = T_F` acting on `Y_F`, before 15.3.68. -/
  second_residual_normalized : TE ≤ normalizer (YF : Set G)
  /-- 15.3.68(1), with relative, not ambient, normality. -/
  first_residual_normalized : G₀ ≤ normalizer (YE : Set G)
  /-- The Sylow conclusion in the proof of 15.3.68(3–4). -/
  local_sylow : ∃ S : Sylow 2 G₀, (S : Subgroup G₀).map G₀.subtype = TE
  /-- 15.3.68(2) supplies this containment before coordinates are chosen. -/
  vector_le : V ≤ G₀
  /-- 15.3.66(5). -/
  first_commutator : V = ⁅V, YE⁆
  /-- Its conjugate, used explicitly in the final proof on p.1155. -/
  second_commutator : V = ⁅V, YF⁆
  /-- The non-`S₃` branch of the final proof on p.1155. -/
  thompson_le : YF.subgroupOf G₀ ≤ thompsonGroup G₀
  /-- The bound used in that same branch; the two-core is not a residual. -/
  local_core_bound : G₀.pCoreIn 2 ⊔ YF.pCoreIn 2 ≤ R
  /-- The commutator used in that same branch, with the actual singular `F`. -/
  local_commutator : ⁅V, Q1⁆ = F

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane
