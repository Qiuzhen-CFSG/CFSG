module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowObstruction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.TwoLocalContract
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.TwoLocal

/-!
# The common prime and Sylow structure in the Suzuki branch

The common-prime conclusion of Lemma 14.4(b) and all conclusions of
Lemmas 14.5–14.6 are proved from the original context, local geometry and
torus semiregularity. In particular the chosen S centralizes A directly
by the odd centralizer index. The two-local proof constructs the actual
quotient S/T and establishes ambient Sylow maximality, relative normality,
the center, normalizer product and conjugation orbits.

The final theorem discharges the adapter's TwoLocalSylowGeometry premise
and supplies the literal shared SylowGeometry contract. No centralizer
embedding is needed once LocalGeometry is supplied; construction of that
earlier geometry remains with the enclosing exclusion argument.
Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 14.4–14.6.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- Assemble the original interface once the separate Lemma 14.6 proof is supplied. -/
public theorem Context.sylowGeometry_of_twoLocal (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    (h : TwoLocalSylowGeometry g) : SylowGeometry g where
  common_prime := d.common_prime g hsemi
  M_product := d.pointStabilizer_eq_centralizer_mul_pair g hsemi
  centralizer_normal := d.distinguished_centralizer_normal
  centralizer_odd_index := d.distinguished_centralizer_odd_index g hsemi
  S_sylow := h.S_sylow
  S_normal := h.S_normal
  S_center := h.S_center
  T_normal := g.T_normal_in_S
  quotient_equiv := h.quotient_equiv
  central_mod_A := h.central_mod_A
  normalizer_product := h.normalizer_product
  U_orbits := h.U_orbits

/-- GLS4, Chapter 2, Lemmas 14.4(b), 14.5 and 14.6, assembled from the
original conditional inputs with no remaining two-local premise. -/
public theorem Context.sylowGeometry (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t) :
    SylowGeometry g :=
  d.sylowGeometry_of_twoLocal g hsemi (d.twoLocalSylowGeometry g hsemi)

end BenderSuzuki.ZD.SuzukiExclusion
