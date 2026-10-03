module

public import Stellmacher.Recognition.LyonsU3Four.NormalizerAction

/-!
# The two quotients of an involution centralizer

For z in the Sylow center, S is also Sylow in C = C_G(z). We first
factor C by its odd core. The second kernel is the normal closure of
the image of Z(S). Once Z-star proves that image central, this kernel
is just the image itself, giving precisely C/(O₂′(C) Z(S)). Taking
normal closure makes the quotient available before that centrality proof.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 1,
pp. 372–373, the paragraph beginning “Suppose |K| = 3”.
-/

namespace Stellmacher.Recognition.LyonsU3Four

public theorem sylow_le_involutionCentralizer {G : Type*} [Group G]
    (S : Sylow 2 G) {z : G} (hz : z ∈ centerImage S) :
    (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
  intro s hs
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact ((Subgroup.mem_centralizer_iff.mp
    (sylow_le_centralizer_centerImage S hs)) z hz).symm

/-- The supplied Sylow considered inside the involution centralizer. -/
@[expose] public def centralizerSylow {G : Type*} [Group G]
    (S : Sylow 2 G) {z : G} (hz : z ∈ centerImage S) :
    Sylow 2 (Subgroup.centralizer ({z} : Set G)) :=
  S.subtype (sylow_le_involutionCentralizer S hz)

/-- Image of Z(S) in C_G(z)/O₂′(C_G(z)). -/
@[expose] public def centralizerCenterModOddCore {G : Type*} [Group G]
    (S : Sylow 2 G) (z : G) :
    Subgroup (Subgroup.centralizer ({z} : Set G) ⧸
      pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))) :=
  ((centerImage S).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
    (QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))))

/-- The second kernel; centrality identifies it with the image of Z(S). -/
@[expose] public def centralizerCenterClosure {G : Type*} [Group G]
    (S : Sylow 2 G) (z : G) :
    Subgroup (Subgroup.centralizer ({z} : Set G) ⧸
      pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))) :=
  Subgroup.normalClosure (centralizerCenterModOddCore S z : Set _)

public instance centralizerCenterClosure_normal {G : Type*} [Group G]
    (S : Sylow 2 G) (z : G) : (centralizerCenterClosure S z).Normal := by
  dsimp [centralizerCenterClosure]
  infer_instance

/-- Under the Z-star conclusion the chosen kernel is exactly the center image. -/
public theorem centralizerCenterClosure_eq_of_le_center {G : Type*} [Group G]
    (S : Sylow 2 G) (z : G)
    (hcentral : centralizerCenterModOddCore S z ≤ Subgroup.center
      (Subgroup.centralizer ({z} : Set G) ⧸
        pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)))) :
    centralizerCenterClosure S z = centralizerCenterModOddCore S z := by
  let : (centralizerCenterModOddCore S z).Normal := by
    constructor
    intro x hx g
    have he : g * x * g⁻¹ = x := by
      rw [Subgroup.mem_center_iff.mp (hcentral hx) g]
      simp
    simpa only [he] using hx
  exact Subgroup.normalClosure_eq_self _

/-- The canonical composite quotient map from the involution centralizer. -/
@[expose] public def centralizerReductionMap {G : Type*} [Group G]
    (S : Sylow 2 G) (z : G) :
    Subgroup.centralizer ({z} : Set G) →*
      (Subgroup.centralizer ({z} : Set G) ⧸
        pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))) ⧸
          centralizerCenterClosure S z :=
  (QuotientGroup.mk' (centralizerCenterClosure S z)).comp
    (QuotientGroup.mk' (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))))

public theorem centralizerReductionMap_surjective {G : Type*} [Group G]
    (S : Sylow 2 G) (z : G) : Function.Surjective (centralizerReductionMap S z) :=
  (QuotientGroup.mk'_surjective (centralizerCenterClosure S z)).comp
    (QuotientGroup.mk'_surjective (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))))

/-- The Sylow subgroup in the further quotient of C_G(z). -/
@[expose] public noncomputable def centralizerReducedSylow
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {z : G} (hz : z ∈ centerImage S) :
    Sylow 2 ((Subgroup.centralizer ({z} : Set G) ⧸
      pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))) ⧸
        centralizerCenterClosure S z) :=
  (centralizerSylow S hz).mapSurjective
    (f := centralizerReductionMap S z) (centralizerReductionMap_surjective S z)

end Stellmacher.Recognition.LyonsU3Four
