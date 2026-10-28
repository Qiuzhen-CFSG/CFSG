module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers.Inputs
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers.ModelGeometry
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers.Quotient
public import Theory.GroupAction.FourNormalizerMotion

/-!
# The block-normalizer geometry in 15.3.61(2)

An actual elementary block of order 64 saturates the extraspecial and actor
rank bounds. Its intersection with `U` consequently has order 16, and its
literal quotient image is the fixed subgroup of `B*`. The model pointwise
stabilizer calculation then recovers `B=C_H(E)`, and every normalizer of
`B*` lifts to a normalizer of `B`. Its six-element action image on `B*`
moves the order-two subgroup `V*`, giving exactly the ambient witness
required by the orbit census.

`ModelGeometry` proves the intrinsic calculations from `RecognizedAction`,
the actual actor and natural-plus-dual identifications supplied by 15.3.58.
The final three theorems discharge those calculations in the ambient argument.
Their remaining inputs are the earlier 15.3.51–59 conclusions and the cubic
branch's actual elementary block inside `T_K`; the order-two image of `V`
is 15.3.53(2). This completes the normalizer prerequisite, while construction
of the block, the orbit census, and final residual fusion stay with their
assembly owners. No residual-orbit, cubic or census module is imported.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1148–1151.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers
open Recognition
variable {G : Type*} [Group G] [Finite G]
variable (Z ZS T V : Subgroup G) (g : G) (D : Subgroup G)
variable [(Z.subgroupOf (closureU Z ZS)).Normal]
variable [IsExtraspecial 2 (closureU Z ZS)]

/-- The block ranks, literal fixed image, and full centralizer are derived
from the uniform actor-model calculations and the genuine earlier inputs. -/
theorem block_geometry_of_model_facts
    (eB : fusionBlock (pairP Z ZS g) V D ≃* Multiplicative (Fin 6 → ZMod 2))
    (hBT : fusionBlock (pairP Z ZS g) V D ≤ residualSylow T Z)
    (hZZS : Z ≤ ZS) (hZV : Z ≤ V) (hZ : Nat.card Z = 2)
    (hU : closureU Z ZS = coreQ Z) (hUcard : Nat.card (closureU Z ZS) = 128)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hbound : ∀ A : Subgroup (ActorQuotient Z), IsElementaryAbelian 2 A → Nat.card A ≤ 4)
    (hmodel : FourGroupModelFacts Z ZS hkernel) :
    let B := fusionBlock (pairP Z ZS g) V D
    let E := blockIntersection (pairP Z ZS g) V D Z ZS
    IsElementaryAbelian 2 (actorImage Z B) ∧ Nat.card (actorImage Z B) = 4 ∧
      Nat.card E = 16 ∧
      vectorImage Z ZS E = (actorAction Z ZS hkernel).commonFixed (actorImage Z B) ∧
      B = centralizerH Z ⊓ centralizer (E : Set G) := by
  let B := fusionBlock (pairP Z ZS g) V D
  have hBH : B ≤ centralizerH Z :=
    hBT.trans (inf_le_right.trans (map_subtype_le (Stellmacher.twoResidualSubgroup _)))
  have hZU := hZZS.trans (ZS_le_closureU Z ZS)
  have hZB : Z ≤ B := hZV.trans le_sup_right
  obtain ⟨hA, hAcard, hE⟩ := block_image_and_intersection_card Z ZS B eB hBH hU
    hcenter hZB hUcard hbound
  have hAK : actorImage Z B ≤ actorImage Z (residualK Z) :=
    map_mono (comap_mono (hBT.trans inf_le_right))
  obtain ⟨hfixedcard, hfixer, _, _⟩ := hmodel (actorImage Z B) hAK hA hAcard
  let : IsElementaryAbelian 2 B := block_elementary B eB
  have hfixed := vectorImage_intersection_eq_fixed Z ZS B hkernel hZU hZB hZ hE hfixedcard
  have hself := intersection_centralizer_in_U Z ZS B hcenter hZB hUcard hE
  have hc := block_eq_H_centralizer Z ZS B hBH hU hkernel hself (by
    intro a ha
    apply hfixer a
    rwa [← hfixed])
  exact ⟨hA, hAcard, hE, hfixed, hc⟩

/-- Exact ambient moving-normalizer witness consumed by `block_cover_of_census`.
No fixed-space equality, block centralizer identity or moving witness is assumed;
they follow from the indicated uniform model calculations. -/
theorem fusionBlock_moving_normalizer_of_model_facts
    (eB : fusionBlock (pairP Z ZS g) V D ≃* Multiplicative (Fin 6 → ZMod 2))
    (hBT : fusionBlock (pairP Z ZS g) V D ≤ residualSylow T Z)
    (hZZS : Z ≤ ZS) (hZV : Z ≤ V) (hZ : Nat.card Z = 2)
    (hU : closureU Z ZS = coreQ Z) (hUcard : Nat.card (closureU Z ZS) = 128)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hVstar : Nat.card (actorImage Z V) = 2)
    (hbound : ∀ A : Subgroup (ActorQuotient Z), IsElementaryAbelian 2 A → Nat.card A ≤ 4)
    (hmodel : FourGroupModelFacts Z ZS hkernel) :
    ∃ n ∈ normalizer (fusionBlock (pairP Z ZS g) V D : Set G),
      n ∉ normalizer (V : Set G) := by
  let B := fusionBlock (pairP Z ZS g) V D
  obtain ⟨hA, hAcard, _, hfixed, hc⟩ := block_geometry_of_model_facts Z ZS T V g D
    eB hBT hZZS hZV hZ hU hUcard hcenter hkernel hbound hmodel
  have hBH : B ≤ centralizerH Z :=
    hBT.trans (inf_le_right.trans (map_subtype_le (Stellmacher.twoResidualSubgroup _)))
  have hAK : actorImage Z B ≤ actorImage Z (residualK Z) :=
    map_mono (comap_mono (hBT.trans inf_le_right))
  have haction := (hmodel (actorImage Z B) hAK hA hAcard).2.2.2
  have hVB : actorImage Z V ≤ actorImage Z B := map_mono (comap_mono le_sup_right)
  have hmotion := exists_normalizer_not_normalizer_of_four_action
    (actorImage Z B) (actorImage Z V) hAcard hVB hVstar (by rw [haction]; decide)
  exact moving_normalizer_of_actor_motion Z ZS B V (le_sup_right.trans hBH) hkernel
    (hZZS.trans (ZS_le_closureU Z ZS)) (hZV.trans le_sup_right) hfixed hc hmotion

/-- The printed relative centralizer and normalizer identities, with `S₄`
identified as a quotient by the exact kernel rather than as the ambient group. -/
theorem fusionBlock_normalizer_structure_of_model_facts
    (eB : fusionBlock (pairP Z ZS g) V D ≃* Multiplicative (Fin 6 → ZMod 2))
    (hBT : fusionBlock (pairP Z ZS g) V D ≤ residualSylow T Z)
    (hZZS : Z ≤ ZS) (hZV : Z ≤ V) (hZ : Nat.card Z = 2)
    (hU : closureU Z ZS = coreQ Z) (hUcard : Nat.card (closureU Z ZS) = 128)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hbound : ∀ A : Subgroup (ActorQuotient Z), IsElementaryAbelian 2 A → Nat.card A ≤ 4)
    (hmodel : FourGroupModelFacts Z ZS hkernel) :
    let B := fusionBlock (pairP Z ZS g) V D
    let E := blockIntersection (pairP Z ZS g) V D Z ZS
    B = residualSylow T Z ⊓ centralizer (E : Set G) ∧
    centralizerH Z ⊓ normalizer (E : Set G) = centralizerH Z ⊓ normalizer (B : Set G) ∧
    (blockNormalizerActorMap Z B).ker =
      ((closureU Z ZS).subgroupOf (centralizerH Z)).subgroupOf
        ((normalizer (B : Set G)).subgroupOf (centralizerH Z)) ∧
    Nonempty ((((normalizer (B : Set G)).subgroupOf (centralizerH Z)) ⧸
      (blockNormalizerActorMap Z B).ker) ≃* Equiv.Perm (Fin 4)) := by
  let B := fusionBlock (pairP Z ZS g) V D
  obtain ⟨hA, hAcard, _, hfixed, hc⟩ := block_geometry_of_model_facts Z ZS T V g D
    eB hBT hZZS hZV hZ hU hUcard hcenter hkernel hbound hmodel
  have hBH : B ≤ centralizerH Z :=
    hBT.trans (inf_le_right.trans (map_subtype_le (Stellmacher.twoResidualSubgroup _)))
  have hAK : actorImage Z B ≤ actorImage Z (residualK Z) :=
    map_mono (comap_mono (hBT.trans inf_le_right))
  obtain ⟨eN⟩ := (hmodel (actorImage Z B) hAK hA hAcard).2.2.1
  exact ⟨block_eq_residualSylow_centralizer Z ZS T B hBT hc,
    intersection_normalizer_eq_block Z ZS B hc,
    blockNormalizerActorMap_ker Z ZS B hU,
    ⟨blockNormalizerQuotientEquiv Z ZS B hBH hkernel
      (hZZS.trans (ZS_le_closureU Z ZS)) (hZV.trans le_sup_right) hfixed hc eN⟩⟩

variable [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

/-- The source block ranks and fixed-space identity, with the intrinsic model
premises discharged by the actual recognition from 15.3.58. In particular the
fixed subgroup is the literal image of `B ∩ U`, and `C_H(B ∩ U)` is exactly `B`.
The elementary block and its containment in `T_K` are the cubic branch's inputs. -/
theorem block_geometry
    (eB : fusionBlock (pairP Z ZS g) V D ≃* Multiplicative (Fin 6 → ZMod 2))
    (hBT : fusionBlock (pairP Z ZS g) V D ≤ residualSylow T Z)
    (hZZS : Z ≤ ZS) (hZV : Z ≤ V) (hZ : Nat.card Z = 2)
    (hU : closureU Z ZS = coreQ Z) (hUcard : Nat.card (closureU Z ZS) = 128)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (d : RecognizedAction Z ZS hkernel) :
    let B := fusionBlock (pairP Z ZS g) V D
    let E := blockIntersection (pairP Z ZS g) V D Z ZS
    IsElementaryAbelian 2 (actorImage Z B) ∧ Nat.card (actorImage Z B) = 4 ∧
      Nat.card E = 16 ∧
      vectorImage Z ZS E = (actorAction Z ZS hkernel).commonFixed (actorImage Z B) ∧
      B = centralizerH Z ⊓ centralizer (E : Set G) :=
  block_geometry_of_model_facts Z ZS T V g D eB hBT hZZS hZV hZ hU hUcard
    hcenter hkernel d.elementary_card_le_four d.fourGroupModelFacts

/-- The source relative centralizer and normalizer identities, with every model
calculation proved from recognition. The `S₄` isomorphism concerns the quotient
of `N_H(B)` by its exact intersection with `U`, not the whole normalizer. -/
theorem fusionBlock_normalizer_structure
    (eB : fusionBlock (pairP Z ZS g) V D ≃* Multiplicative (Fin 6 → ZMod 2))
    (hBT : fusionBlock (pairP Z ZS g) V D ≤ residualSylow T Z)
    (hZZS : Z ≤ ZS) (hZV : Z ≤ V) (hZ : Nat.card Z = 2)
    (hU : closureU Z ZS = coreQ Z) (hUcard : Nat.card (closureU Z ZS) = 128)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (d : RecognizedAction Z ZS hkernel) :
    let B := fusionBlock (pairP Z ZS g) V D
    let E := blockIntersection (pairP Z ZS g) V D Z ZS
    B = residualSylow T Z ⊓ centralizer (E : Set G) ∧
    centralizerH Z ⊓ normalizer (E : Set G) = centralizerH Z ⊓ normalizer (B : Set G) ∧
    (blockNormalizerActorMap Z B).ker =
      ((closureU Z ZS).subgroupOf (centralizerH Z)).subgroupOf
        ((normalizer (B : Set G)).subgroupOf (centralizerH Z)) ∧
    Nonempty ((((normalizer (B : Set G)).subgroupOf (centralizerH Z)) ⧸
      (blockNormalizerActorMap Z B).ker) ≃* Equiv.Perm (Fin 4)) :=
  fusionBlock_normalizer_structure_of_model_facts Z ZS T V g D eB hBT hZZS hZV hZ
    hU hUcard hcenter hkernel d.elementary_card_le_four d.fourGroupModelFacts

/-- The exact ambient witness required by `Census.block_cover_of_census`, with
the four-group model premises discharged. The order of `V*` is the earlier
15.3.53(2) conclusion. Neither an orbit census nor a fusion cover is required. -/
theorem fusionBlock_moving_normalizer
    (eB : fusionBlock (pairP Z ZS g) V D ≃* Multiplicative (Fin 6 → ZMod 2))
    (hBT : fusionBlock (pairP Z ZS g) V D ≤ residualSylow T Z)
    (hZZS : Z ≤ ZS) (hZV : Z ≤ V) (hZ : Nat.card Z = 2)
    (hU : closureU Z ZS = coreQ Z) (hUcard : Nat.card (closureU Z ZS) = 128)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (d : RecognizedAction Z ZS hkernel)
    (hVstar : Nat.card (actorImage Z V) = 2) :
    ∃ n ∈ normalizer (fusionBlock (pairP Z ZS g) V D : Set G),
      n ∉ normalizer (V : Set G) :=
  fusionBlock_moving_normalizer_of_model_facts Z ZS T V g D eB hBT hZZS hZV hZ
    hU hUcard hcenter hkernel hVstar d.elementary_card_le_four d.fourGroupModelFacts

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers
