module

public import Stellmacher.Recognition.Parrott.SecondNormalizer
public import Stellmacher.Recognition.Parrott.OuterOmegaLocalGeometry

/-!
# Outer fusion under the second self-normalizer assumption

Put H=C_G(z), J=O₂(H), and T=d.sylow for the supplied second elementary
data d. If z is weakly closed in the mapped core J, no involution in T
outside that core is conjugate to z. In particular this gives the outer
fusion exclusion in the branch N_G(d.F)=T, once core weak closure has
been established separately.

For each outer involution y, use the actual ambient image of Ω₁(C_T(y)).
The local geometry gives either order sixteen, or an elementary group of
order thirty-two with a core intersection of order sixteen and outer
suborbits of length eight or sixteen. The fusion reduction excludes the
first case by the order-sixteen argument and the second by normalizer
movement and binary hyperplane separation. No additional premise on the
location of core involutions is used. The supplied F and T are retained.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the first paragraph of p.676. The binary hyperplane argument
in `OuterFusionReduction` replaces the final two-core center contradiction.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- Core weak closure excludes fusion of every outer involution in the
supplied Sylow to the original central involution. -/
public theorem outer_not_isConj_of_core_weakClosure
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z)
    (hcore : ∀ t : G, t ∈ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype → IsConj z t → t = z) :
    ∀ y : G, y ∈ (d.sylow : Subgroup G) →
      y ∉ (pCore 2 (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype →
      orderOf y = 2 → ¬ IsConj z y := by
  intro y hyT hyJ hy
  exact d.outer_not_isConj_of_omega_geometry hN h hcore y hyT hyJ hy
    (d.outer_omega_local_geometry h y hyT hyJ hy)

/-- The outer-fusion exclusion in the self-normalizer branch of Parrott
Lemma 5, with core weak closure supplied by the separate core argument. -/
public theorem outer_not_isConj_under_selfNormalizer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {z : G}
    (d : ParrottSecondElementaryData z) (_hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (h : ParrottCentralizerHypotheses z)
    (_hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hcore : ∀ t : G, t ∈ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype → IsConj z t → t = z) :
    ∀ y : G, y ∈ (d.sylow : Subgroup G) →
      y ∉ (pCore 2 (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype →
      orderOf y = 2 → ¬ IsConj z y :=
  d.outer_not_isConj_of_core_weakClosure hN h hcore

end Stellmacher.Recognition.ParrottSecondElementaryData
