module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.Recognition
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.QuotientGeometry.Descent
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.QuotientGeometry.CentralizerBounds
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.QuotientGeometry.SylowFusion

/-!
# Transport and assembly of the root-five quotient involution geometry

Calculations at the selected representative suffice for every member of the
ambient conjugacy family. Pull the five-subgroup back by a conjugator, transport
its full centralizer and marked involution, and apply central-five descent to
the literal quotient. Recognition and splitting then use that same quotient map.

The selected 47.1 geometry supplies the local centralizer calculation and the
Sylow/fusion argument. The concrete self-centralizing five-subgroup theorem in
A₅ discharges the latter's model premise. Thus
`quotientInvolutionFamily_of_selectedGeometry` proves the full quotient
involution family without further local assumptions. The ambient order is
needed only for the subsequent recognition and splitting application.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizer_map_eq (E : Subgroup G) (e : G ≃* G) :
    (centralizer (E : Set G)).map e.toMonoidHom =
      centralizer (E.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, ← map_mul] using congrArg e (hx y hy)
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) ⟨y, hy, rfl⟩

private def centralizerEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (t : A) (u : B) (h : e t = u) :
    centralizer ({t} : Set A) ≃* centralizer ({u} : Set B) where
  toFun x := ⟨e x, mem_centralizer_singleton_iff.mpr (by
    rw [← h]
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp x.property))⟩
  invFun x := ⟨e.symm x, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply, h] using
      mem_centralizer_singleton_iff.mp x.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (e.map_mul x y)

/-- Local calculations at the selected representative suffice for the entire
ambient conjugacy family. The conjugation equivalences retain the actual
centralizers and the root element; all quotient data then use the literal map. -/
theorem quotientInvolutionFamily_of_local (t : G) (ht : orderOf t = 2)
    (hC : LocalCentralizerBounds t) (hF : LocalInvolutionFusion t) :
    QuotientInvolutionFamily t := by
  rintro E ⟨hE, u, htu, hEu⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp htu
  let e : G ≃* G := MulAut.conj g
  have het : e t = u := hg
  let F := E.comap e.toMonoidHom
  have hFE : F.map e.toMonoidHom = E :=
    map_comap_eq_self_of_surjective e.surjective E
  have hFcard : Nat.card F = 5 := by
    rw [← hFE, card_map_of_injective e.injective] at hE
    exact hE
  have hFt : F ≤ involutionCentralizer t := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, het, MulEquiv.coe_toMonoidHom] using mem_centralizer_singleton_iff.mp (hEu hx)
  have hCE : (centralizer (F : Set G)).map e.toMonoidHom = centralizer (E : Set G) := by
    rw [centralizer_map_eq, hFE]
  let m : centralizer (F : Set G) ≃* centralizer (E : Set G) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr hCE)
  have hmt : m (rootInCentralizer F t hFt) = rootInCentralizer E u hEu :=
    Subtype.ext het
  let c := centralizerEquiv m (rootInCentralizer F t hFt)
    (rootInCentralizer E u hEu) hmt
  obtain ⟨hc, hp⟩ := hC F hFcard hFt
  have hu : orderOf u = 2 := by rw [← het, e.orderOf_eq, ht]
  refine ⟨u, htu, hEu, quotientInvolutionData_of_centralizer E hE u hu hEu ?_ ?_ ?_⟩
  · exact (Nat.card_congr c.symm.toEquiv).trans hc
  · intro x
    obtain ⟨y, rfl⟩ := c.surjective x
    rw [← map_pow, hp y, map_one]
  · intro x hx
    have hi := hF F hFcard hFt (m.symm x) ((m.symm.orderOf_eq x).trans hx)
    have hm := m.toMonoidHom.map_isConj hi
    simpa only [MulEquiv.coe_toMonoidHom, m.apply_symm_apply, hmt] using hm

/-- The transported family feeds the actual A₅ recognition and the section of
its central extension. The two local source calculations remain explicit here. -/
theorem centralizer_splits_of_local_geometry {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D) (hG : Nat.card G = 604800)
    (hC : LocalCentralizerBounds S.t) (hF : LocalInvolutionFusion S.t)
    (E : Subgroup G) (hE : FiveCentralizing S.t E) :
    ∃ e : Quotient E ≃* alternatingGroup (Fin 5),
      ∃ s : alternatingGroup (Fin 5) →* centralizer (E : Set G),
        (e.toMonoidHom.comp (QuotientGroup.mk' (kernel E))).comp s = MonoidHom.id _ ∧
          (kernel E).IsComplement' s.range := by
  obtain ⟨u, htu, hEu, ⟨I⟩⟩ := quotientInvolutionFamily_of_local S.t S.other.1 hC hF E hE
  have hu : orderOf u = 2 := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp htu
    exact ((MulAut.conj g).orderOf_eq S.t).trans S.other.1
  obtain ⟨e⟩ := quotient_equiv_of_involutionData hG E hE.1 u hu hEu I
  obtain ⟨s, hs, hc⟩ := exists_complement_of_quotient_equiv E hE.1 e
  exact ⟨e, s, hs, hc⟩

/-- The selected source geometry supplies all involution conjugacy and full
centralizer data for every literal five-centralizer quotient. Both local source
calculations and the concrete A₅ self-centralizing premise are discharged. -/
theorem quotientInvolutionFamily_of_selectedGeometry {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D) : QuotientInvolutionFamily S.t :=
  quotientInvolutionFamily_of_local S.t S.other.1 (localCentralizerBounds S)
    (SylowFusion.localInvolutionFusion S
      Theory.SpecificGroups.Alternating.centralizer_eq_of_card_five)

/-- The source geometry and ambient order yield a section and internal complement
for the literal quotient map, with no additional local-geometry premise. -/
theorem centralizer_splits_of_selectedGeometry {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D) (hG : Nat.card G = 604800)
    (E : Subgroup G) (hE : FiveCentralizing S.t E) :
    ∃ e : Quotient E ≃* alternatingGroup (Fin 5),
      ∃ s : alternatingGroup (Fin 5) →* centralizer (E : Set G),
        (e.toMonoidHom.comp (QuotientGroup.mk' (kernel E))).comp s = MonoidHom.id _ ∧
          (kernel E).IsComplement' s.range := by
  obtain ⟨u, htu, hEu, ⟨I⟩⟩ := quotientInvolutionFamily_of_selectedGeometry S E hE
  have hu : orderOf u = 2 := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp htu
    exact ((MulAut.conj g).orderOf_eq S.t).trans S.other.1
  obtain ⟨e⟩ := quotient_equiv_of_involutionData hG E hE.1 u hu hEu I
  obtain ⟨s, hs, hc⟩ := exists_complement_of_quotient_equiv E hE.1 e
  exact ⟨e, s, hs, hc⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent
