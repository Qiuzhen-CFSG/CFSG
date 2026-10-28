module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.ParabolicTransport
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Reduction

/-!
# Applying the parabolic transport in J.2.6

The transport theorem discharges the `htransport` premise of both outer
reductions on the literal local setup. The preceding parabolic results also
supply Q ≤ L, Q ≰ S, |Z| = 2 and Z ≤ V. The first application turns a
z-fused involution of Q outside H_C into an outer seed. The second leaves
the independent natural-head, conjugate-intersection, central-product and
outer-orbit inputs explicit for the final fusion assembly.

Source: Aschbacher–Smith, J.2.6, printed p.435 (PDF p.446 of
`refs/quasithin.pdf`, combined manuscript of 1 March 2004).
-/

public section
open Subgroup
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]

/-- The source Q-seed supplies an outer seed without an additional transport premise. -/
theorem exists_outer_seed_of_localSetup (d : LocalSetup G)
    (head : NaturalHead d.toTypeRuSetup)
    (hCS : d.toTypeRuSetup.HC ≤ d.toTypeRuSetup.S)
    {z : G} (hseed : ∃ x : G, x ∈ d.toTypeRuSetup.Q ∧ x ∉ d.toTypeRuSetup.HC ∧
      orderOf x = 2 ∧ IsConj x z) :
    ∃ j ∈ involutionsOutside d.toTypeRuSetup.H d.toTypeRuSetup.K, IsConj j z := by
  exact exists_outer_seed d.toTypeRuSetup head d.Q_le_L hCS d.not_Q_le_S
    hseed (transport_involutions d)

/-- The local J.2.6 reduction with parabolic transport fully discharged.
The central product, natural head, conjugate geometry and outer orbit remain
the independent inputs owned by the final fusion assembly. -/
theorem sourceJ26_of_localSetup_outer_orbit (d : LocalSetup G)
    (head : NaturalHead d.toTypeRuSetup)
    (B : Sylow 3 d.toTypeRuSetup.L₁) (cp : CentralProductData d.toTypeRuSetup B)
    (hCS : d.toTypeRuSetup.HC ≤ d.toTypeRuSetup.S)
    {z : G} (hz : z ∈ d.toTypeRuSetup.Z) (hz1 : z ≠ 1)
    (hconjugates : ∀ l : d.L, (l : G) ∉ d.toTypeRuSetup.H →
      (d.toTypeRuSetup.Q.subgroupOf
        (d.toTypeRuSetup.U.map (MulAut.conj (l : G)).toMonoidHom)).index = 2 ∧
        d.toTypeRuSetup.U.map (MulAut.conj (l : G)).toMonoidHom ⊓
          d.toTypeRuSetup.HC = d.V)
    (htrans : TransitiveOn d.toTypeRuSetup.H
      (involutionsOutside d.toTypeRuSetup.H d.toTypeRuSetup.K))
    (hcard : Nat.card (involutionsOutside d.toTypeRuSetup.H d.toTypeRuSetup.K) = 640) :
    SourceJ26 d.toTypeRuSetup z := by
  exact sourceJ26_of_outer_orbit d.toTypeRuSetup head B cp d.card_Z
    (d.center_eq.le.trans inf_le_left) d.Q_le_L hCS d.not_Q_le_S hz hz1
    hconjugates (transport_involutions d) htrans hcard

end CFSG.Quasithin.ChapterJ.Fusion.Outer
