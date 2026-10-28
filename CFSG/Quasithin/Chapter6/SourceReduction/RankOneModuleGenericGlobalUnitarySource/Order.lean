module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ExtensionFusion
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourRootClasses
public import Theory.GroupTheory.InvolutionClassOrderComparison

/-!
# Thompson order equality on the marked full unitary-four extension

Choose the actual opposite-center long root and the specified short root in
O₂(L). The native two-orbit calculation and ambient nonfusion make these the
two classes in both groups. Both full centralizer isomorphisms preserve their
distinguished points and both ambient class predicates, so they identify the
actual Thompson fibers. The two-class formula gives equality with the full
extension order. Its odd outer degree remains the only extra source premise.

Source: Aschbacher--Smith F.4.42--43, pp.295--296, with F.4.38 parity.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion UnitaryFourFusion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

private theorem centralizerPoint_map {X Y : Type*} [Group X] [Group Y]
    (N : Subgroup X) (j : N →* Y) (u : N)
    (hN : centralizer ({u.val} : Set X) ≤ N)
    (e : centralizer ({u.val} : Set X) ≃* centralizer ({j u} : Set Y))
    (he : ∀ x, (e x).val = j (inclusion hN x)) :
    e (InvolutionClassOrderComparison.centralizerPoint u.val) =
      InvolutionClassOrderComparison.centralizerPoint (j u) := by
  apply Subtype.ext
  rw [InvolutionClassOrderComparison.centralizerPoint_coe,he]
  exact congrArg j (Subtype.ext (InvolutionClassOrderComparison.centralizerPoint_coe u.val))

/-- Thompson's two-class formula compares G with the same marked full
extension. The only remaining source premise is its odd outer degree. -/
theorem Preparation.unitaryFour_order_of_odd_outer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm)
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier) :
    Nat.card G = Nat.card r.extension.carrier := by
  obtain ⟨a,f,F,h0,h1,hD,hlong,hshort⟩ :=
    d.unitaryFour_ambient_centralizers_of_odd_outer h hH hp m hm hc r hodd
  have hm' : 1 < m := hc.elim
    (fun ho => (d.unitary_local_structure h hH.1.1.2 hp m hm ho).1)
    (fun he => (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm he).1)
  let : NeZero m := ⟨by omega⟩
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L)
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp
    (hc.elim (.unitary m hm) (.unitaryExtension m hm))
  obtain ⟨z,hzQ,hzC,hz2,hroots⟩ :=
    ChapterF.UnitarySource.FourRootClasses.marked_core_root_orbits m hm P L (residual H) hr hm' a.comparison
  let zL : normalizer (L : Set G) := ⟨z,L.le_normalizer (pCoreIn_le 2 L hzQ)⟩
  let t := inclusion r.left_le (inclusion inf_le_left
    (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm a.comparison))
  have htQ : t.val ∈ L.pCoreIn 2 :=
    ChapterF.UnitarySource.FourPlacement.plane_comparison_core_le_residual_core
      m hm (P 0) L a.comparison.left (hr 0)
      (ChapterF.UnitarySource.FourShortTransport.sourceShort_mem_core m hm a.comparison)
  obtain ⟨ht2,_,_,_,htN,eT,heT⟩ := hshort
  let j := markedLeftHom r F
  let k := markedRightHom r F
  have hj : Function.Injective j := (inclusion_injective r.extension.right_le).comp F.left.injective
  have hroot (x : normalizer (L : Set G)) (hxQ : x.val ∈ L.pCoreIn 2)
      (hx2 : orderOf x.val=2) : IsConj x.val z ∨ IsConj x.val t.val := by
    have hx1 : x.val ≠ 1 := by intro he; simp [he] at hx2
    obtain ⟨g,_,hgz | hgt⟩ := hroots x.val hxQ hx1
    · exact Or.inl (isConj_iff.mpr ⟨g,hgz⟩)
    · exact Or.inr (isConj_iff.mpr ⟨g,hgt⟩)
  obtain ⟨u,v,hu,hv,hu2,hv2,_,_,huv,_,hcover,hcoverE⟩ :=
    marked_two_classes_of_odd_outer d h hH hp m hm hc r a F h0 hodd
  have hzt : ¬ IsConj z t.val := by
    intro he
    have allz (x : normalizer (L : Set G)) (hxQ : x.val ∈ L.pCoreIn 2)
        (hx2 : orderOf x.val=2) : IsConj x.val z :=
      (hroot x hxQ hx2).elim id (fun hh => hh.trans he.symm)
    exact huv ((allz u hu hu2).trans (allz v hv hv2).symm)
  have hztE : ¬ IsConj (j zL) (j t) := fun he =>
    hzt ((marked_core_fusion d h hH hp m hm hc r a F h0 zL t hzQ htQ).mpr he)
  have rootE (x : normalizer (L : Set G)) (hxQ : x.val ∈ L.pCoreIn 2)
      (hx2 : orderOf x.val=2) : IsConj (j x) (j zL) ∨ IsConj (j x) (j t) := by
    rcases hroot x hxQ hx2 with he | he
    · exact Or.inl ((marked_core_fusion d h hH hp m hm hc r a F h0 x zL hxQ hzQ).mp he)
    · exact Or.inr ((marked_core_fusion d h hH hp m hm hc r a F h0 x t hxQ htQ).mp he)
  have hcovG : ∀ x : G, orderOf x=2 → IsConj z x ∨ IsConj t.val x := by
    intro x hx
    rcases hcover x hx with he | he
    · exact (hroot u hu hu2).elim (fun hh => Or.inl (he.trans hh).symm)
        (fun hh => Or.inr (he.trans hh).symm)
    · exact (hroot v hv hv2).elim (fun hh => Or.inl (he.trans hh).symm)
        (fun hh => Or.inr (he.trans hh).symm)
  have hcovE : ∀ x : r.extension.carrier, orderOf x=2 →
      IsConj (j zL) x ∨ IsConj (j t) x := by
    intro x hx
    rcases hcoverE x hx with he | he
    · exact (rootE u hu hu2).elim (fun hh => Or.inl (he.trans hh).symm)
        (fun hh => Or.inr (he.trans hh).symm)
    · exact (rootE v hv hv2).elim (fun hh => Or.inl (he.trans hh).symm)
        (fun hh => Or.inr (he.trans hh).symm)
  let zK : normalizer (residual H : Set G) :=
    ⟨z,(residual H).le_normalizer (map_subtype_le _ hzC)⟩
  have hjz : j zL = k zK := marked_overlap m hm r F
    ⟨z,zL.property,zK.property⟩
  obtain ⟨_,_,hzN,eZ,heZ⟩ := hlong zK hzC hz2
  have hzE2 : orderOf (k zK)=2 := by
    rw [←hjz,orderOf_injective j hj,←Subgroup.orderOf_coe zL]
    exact hz2
  have htE2 : orderOf (j t)=2 := by
    rw [orderOf_injective j hj,←Subgroup.orderOf_coe t]
    exact ht2
  rw [hjz] at hztE hcovE
  have hpointZ := centralizerPoint_map _ k zK hzN eZ heZ
  have hpointT := centralizerPoint_map _ j t htN eT heT
  have hzZ (x : centralizer ({z} : Set G)) :
      IsConj z x.val ↔ IsConj (k zK) (eZ x).val := by
    rw [heZ x,←hjz]
    exact marked_right_class_of_odd_outer d h hH hp m hm hc r a F h0 hodd zL hzQ hz2 (inclusion hzN x)
  have htZ (x : centralizer ({z} : Set G)) :
      IsConj t.val x.val ↔ IsConj (j t) (eZ x).val := by
    rw [heZ x]
    exact marked_right_class_of_odd_outer d h hH hp m hm hc r a F h0 hodd t htQ ht2 (inclusion hzN x)
  have hzT (x : centralizer ({t.val} : Set G)) :
      IsConj z x.val ↔ IsConj (k zK) (eT x).val := by
    rw [heT x,←hjz]
    exact marked_left_class_of_odd_outer d h hH hp m hm hc r a F h0 hodd zL hzQ hz2 (inclusion htN x)
  have htT (x : centralizer ({t.val} : Set G)) :
      IsConj t.val x.val ↔ IsConj (j t) (eT x).val := by
    rw [heT x]
    exact marked_left_class_of_odd_outer d h hH hp m hm hc r a F h0 hodd t htQ ht2 (inclusion htN x)
  have hkZ := InvolutionClassOrderComparison.kappa_eq z t.val z (k zK) (j t) (k zK)
    hz2 ht2 hzt hzE2 htE2 hztE eZ hpointZ hzZ htZ
  have hkT := InvolutionClassOrderComparison.kappa_eq z t.val t.val (k zK) (j t) (j t)
    hz2 ht2 hzt hzE2 htE2 hztE eT hpointT hzT htT
  have hcZ := Nat.card_congr eZ.toEquiv
  have hcT := Nat.card_congr eT.toEquiv
  rw [TwoInvolutionClassOrder.card_eq z t.val hz2 ht2 hzt hcovG,
    TwoInvolutionClassOrder.card_eq (k zK) (j t) hzE2 htE2 hztE hcovE,hkZ,hkT,hcZ,hcT]
  rfl

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
