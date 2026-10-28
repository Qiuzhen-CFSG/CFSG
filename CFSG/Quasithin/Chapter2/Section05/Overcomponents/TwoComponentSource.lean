module
public import CFSG.Quasithin.ChapterI.Section03.InvolutionSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingMarksSource

/-!
# The actual involution-centralizer pumpup for 2.5.19

A component of C_G(t) centralizing i restricts to a component of
C_{C_G(i)}(t). Apply the proved I.3.2 theorem there, keeping the actual
centralizer inclusion, odd-E orbit and both intrinsic quotient maps.
The earlier component assertion at t is precisely source 2.5.18; its
producer is the source persistence and M₁₁-exclusion argument. No
component of C_G(i), containing-model list or quotient equivalence is assumed.
Source: Aschbacher–Smith 2.5.19, printed pp.560–561.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
variable {G : Type*} [Group G] [Finite G]

/-- The original odd-E pumpup, with both involutions and all quotient maps retained. -/
@[expose] def TwoComponentPumpup (K : Subgroup G) (t i : G) : Prop :=
  ∃ htI : t ∈ centralizer ({i} : Set G),
    let Gi := centralizer ({i} : Set G)
    let tI : Gi := ⟨t, htI⟩
    let D := K.subgroupOf Gi
    let X := componentOrbit D (oddELayer Gi)
    K ≤ Gi ∧
    ((X.IsTwoComponent ∧ X.map (MulAut.conj tI).toMonoidHom = X) ∨
      ∃ J : Subgroup Gi, J.IsTwoComponent ∧ J ≠ J.map (MulAut.conj tI).toMonoidHom ∧
        X = J ⊔ J.map (MulAut.conj tI).toMonoidHom ∧
        Nonempty ((J ⧸ oddTwoCore J) ≃* (K ⧸ oddTwoCore K)))

/-- The actual component of C_G(t) is the seed in C_{C_G(i)}(t).
This is the literal initial I.3.2 application in the proof of 2.5.19. -/
theorem twoComponent_pumpup (K : Subgroup G) (t i : G) (ht : orderOf t = 2)
    (hti : Commute t i) (hKi : K ≤ centralizer ({i} : Set G))
    (hKt : IsComponentIn K (centralizer ({t} : Set G))) :
    TwoComponentPumpup K t i := by
  let Gi := centralizer ({i} : Set G)
  have htI : t ∈ Gi := mem_centralizer_singleton_iff.mpr hti.eq
  let tI : Gi := ⟨t,htI⟩
  let C := centralizer ({tI} : Set Gi)
  let Ct := centralizer ({t} : Set G)
  let D := K.subgroupOf Gi
  have hDC : D ≤ C := by
    intro k hk
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hKt.1 hk)
  let f : C →* Ct := ((Gi.subtype).comp C.subtype).codRestrict Ct (fun x => by
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))
  let L := D.subgroupOf C
  let e : L ≃* K := (subgroupOfEquivOfLe hDC).trans (subgroupOfEquivOfLe hKi)
  have hL : IsComponent C L := by
    refine ⟨hKt.2.1.comap f,?_⟩
    let : IsQuasisimple K := hKt.quasisimple
    exact IsQuasisimple.of_mulEquiv e.symm
  have htI2 : orderOf tI = 2 := (Subgroup.orderOf_coe tI).symm.trans ht
  have ha := ChapterI.lemma_I_3_2 tI htI2 L (ChapterI.Balance.ordinary_isTwoComponent hL)
  have hm : L.map C.subtype = D := map_subgroupOf_eq_of_le hDC
  change
    (componentOrbit (L.map C.subtype) (oddELayer Gi)).IsTwoComponent ∧
      (componentOrbit (L.map C.subtype) (oddELayer Gi)).map (MulAut.conj tI).toMonoidHom =
        componentOrbit (L.map C.subtype) (oddELayer Gi) ∨ _ at ha
  rw [hm] at ha
  refine ⟨htI,hKi,?_⟩
  rcases ha with ha | ⟨J,hJ,hne,hX,⟨eq⟩⟩
  · exact Or.inl ha
  · exact Or.inr ⟨J,hJ,hne,hX,⟨eq.trans (QuotientGroup.congr _ _ e (oddTwoCore_map_equiv e))⟩⟩
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
