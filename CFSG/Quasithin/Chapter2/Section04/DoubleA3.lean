module

public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.FactorGeometry
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Transport
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner

/-!
# The terminal counting obstruction in the two-A₃ branch

The source centralizer G₂ is literally C_G(z₂), and B is literally
C_G₂(K). Its normal A₆ component acts through the genuine conjugation
quotient. Every involution in the second dihedral factor belongs to the
ambient class of z₂ because that factor lies in the right conjugate Kˢ.
The marked quotient and the pure-factor fusion containment then give the
terminal contradiction. Both numerical counts and all equal-fiber claims
are proved, with the kernel involution included in the corrected count.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, §2.4,
printed pp.547–550. The centralizer recognition in 2.4.32–36 and the
pure-factor containment in 2.4.37 remain explicit source inputs here.
This module does not claim a proof of those preceding source assertions.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.DoubleA3
open Subgroup
open AlternatingSix.ShadowLocal

variable {G : Type*} [Group G]

/-- The original involution centralizer, retaining the ambient group. -/
abbrev involutionCentralizer (z : G) : Subgroup G := centralizer ({z} : Set G)

/-- The source's right conjugate Kˢ uses s⁻¹ks, not sks⁻¹. -/
def rightConjugateComponent (H : Subgroup G) (K : Subgroup H) (s : G) : Subgroup G :=
  (K.map H.subtype).map (MulAut.conj s⁻¹).toMonoidHom

/-- All involutions of a subgroup lying in an actual A₆ are ambiently
conjugate to any marked involution of that A₆. -/
theorem involution_fusion_of_alternating_six (J : Subgroup G) (e : J ≃* A6)
    (z : G) (hzJ : z ∈ J) (hz : z ^ 2 = 1) (hz1 : z ≠ 1)
    (a : G) (haJ : a ∈ J) (ha : a ^ 2 = 1) (ha1 : a ≠ 1) : IsConj z a := by
  let zJ : J := ⟨z, hzJ⟩
  let aJ : J := ⟨a, haJ⟩
  have hzord : orderOf zJ = 2 := orderOf_eq_prime
    (Subtype.ext hz) (fun h => hz1 (congrArg Subtype.val h))
  have haord : orderOf aJ = 2 := orderOf_eq_prime
    (Subtype.ext ha) (fun h => ha1 (congrArg Subtype.val h))
  have hc := involutions_isConj (e zJ) (e aJ)
    ((e.orderOf_eq zJ).trans hzord) ((e.orderOf_eq aJ).trans haord)
  have hc' : IsConj zJ aJ := by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      e.symm.toMonoidHom.map_isConj hc
  exact J.subtype.map_isConj hc'

private noncomputable def rightConjugateComponentEquiv (H : Subgroup G)
    (K : Subgroup H) (s : G) : K ≃* rightConjugateComponent H K s :=
  (K.equivMapOfInjective H.subtype H.subtype_injective).trans
    ((MulAut.conj s⁻¹).subgroupMap (K.map H.subtype))

private theorem centralizer_disjoint (H : Subgroup G) (K : Subgroup H)
    (e : K ≃* A6) : Disjoint (centralizer (K : Set H)) K := by
  apply disjoint_def.mpr
  intro a hc hk
  have haz : (⟨a, hk⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (hc k k.property)
  have hez := (Subgroup.centerCongr e ⟨⟨a, hk⟩, haz⟩).property
  change e ⟨a, hk⟩ ∈ center A6 at hez
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hez
  exact congrArg Subtype.val (e.injective (hez.trans e.map_one.symm))

/-- Apply the corrected terminal contradiction to the actual centralizer
and its actual A₆ conjugation action. The second factor's involution
fusion, centralizer disjointness, quotient marking of K, uniform fibers,
and both cardinalities are all discharged in this consumer. -/
theorem false_of_centralizer_geometry [Finite G] (z : G)
    (hz : z ^ 2 = 1) (hz1 : z ≠ 1)
    (K : Subgroup (involutionCentralizer z)) [K.Normal]
    (eK : K ≃* A6) (R E : Subgroup (involutionCentralizer z))
    (hBR : centralizer (K : Set (involutionCentralizer z)) ≤ R)
    (hER : E ≤ R) (hEK : Disjoint E K)
    (eB : centralizer (K : Set (involutionCentralizer z)) ≃* Multiplicative (ZMod 4))
    (eE : E ≃* DihedralGroup 4)
    (hsurj : Function.Surjective (conjugationAction K eK))
    (hnatural : R.map (conjugationAction K eK) ≤ natural)
    (eR : R.map (QuotientGroup.mk' (centralizer (K : Set (involutionCentralizer z)))) ≃*
      Multiplicative (ZMod 2) × DihedralGroup 4)
    (hmark : ∀ q : R.map (QuotientGroup.mk' (centralizer (K : Set (involutionCentralizer z)))),
      (q : involutionCentralizer z ⧸ centralizer (K : Set (involutionCentralizer z))) ∈
        K.map (QuotientGroup.mk' (centralizer (K : Set (involutionCentralizer z)))) ↔
          (eR q).1 = 1)
    (hpure : ∀ a : involutionCentralizer z, IsConj z (a : G) → a ∈ R → a ∈ K ∨ a ∈ E)
    (s : G)
    (hEconj : E.map (involutionCentralizer z).subtype ≤
      rightConjugateComponent (involutionCentralizer z) K s)
    (hzconj : z ∈ rightConjugateComponent (involutionCentralizer z) K s) : False := by
  let H := involutionCentralizer z
  let B := centralizer (K : Set H)
  let zH : H := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
  have hzB : zH ∈ B := by
    intro k hk
    exact Subtype.ext (mem_centralizer_singleton_iff.mp k.property)
  have hBK : Disjoint B K := centralizer_disjoint H K eK
  have hzH1 : zH ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzK : zH ∉ K := fun h => hzH1 (disjoint_def.mp hBK hzB h)
  let eQ := conjugationQuotientEquiv K eK hsurj
  have hcomp : eQ.toMonoidHom.comp (QuotientGroup.mk' B) = conjugationAction K eK := rfl
  have hinner : (K.map (QuotientGroup.mk' B)).map eQ.toMonoidHom =
      AlternatingSix.ShadowLocal.inner := by
    rw [map_map, hcomp, conjugationAction_map_inner]
  have hnat : (R.map (QuotientGroup.mk' B)).map eQ.toMonoidHom ≤ natural := by
    simpa only [map_map, hcomp] using hnatural
  let J := rightConjugateComponent H K s
  let eJ : J ≃* A6 := (rightConjugateComponentEquiv H K s).symm.trans eK
  apply false_of_terminal_geometry H B R K E le_rfl hBK hBR hER hEK zH
    (Subtype.ext hz) hzH1 hzB hzK eB eE eQ hinner hnat eR hmark hpure
  intro a ha ha1
  apply involution_fusion_of_alternating_six J eJ z hzconj hz hz1
    ((a : H) : G) (hEconj (mem_map_of_mem H.subtype a.property))
  · exact congrArg (fun x : E => ((x : H) : G)) ha
  · exact fun h => ha1 (Subtype.ext (Subtype.ext h))

end CFSG.Quasithin.Chapter2.DoubleA3
