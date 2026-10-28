module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointSections
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.GroupTheory.ReducedNormal.SectionClosureCore
public import Theory.GroupTheory.SylowNormalizerOvergroup

/-!
# The original point closure inside the centralizer core

For the original central involution z, the natural section V_z/⟨z⟩ is
irreducible under the actual local residual, and the original Sylow normalizes
V_z. Characteristic two in C_G(z), followed by the irreducible-section closure
theorem, places E=⟨V_z^{C_G(z)}⟩ in O₂(C_G(z)). Its commutators with that
whole core and its squares lie in the retained central line ⟨z⟩.
Consequently E/Z(E) is elementary abelian, supplying that input of the
extraspecial normal-closure criterion.
The whole centralizer core also lies in O₂(L_z T), with the actual Sylow T.

Source: Aschbacher–Smith 8.2.12, first paragraph, printed p.722,
refs/quasithin.pdf. The Chapter 12 consumer discharges these inputs for the
original half-field tensor action. The crossing, exact core equality,
extraspecial structure, and final exclusion remain subsequent steps.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

/-- The actual relative normal closure is central in the full two-core modulo
the original central involution, and its quotient has exponent two. -/
theorem point_closure_core
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G) (z : V)
    (hE : IsEvenCharacteristicAt T)
    (hLN : L ≤ normalizer (V : Set G)) (hVT : V ≤ T)
    (hz : orderOf (z : G) = 2) (hTC : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hZW : zpowers (z : G) < Centralizer.commutatorSpace L V z)
    (hNW : Centralizer.localResidual L z ⊔ (T : Subgroup G) ≤
      normalizer (Centralizer.commutatorSpace L V z : Set G))
    (hact : PointSectionActions V (Centralizer.commutatorSpace L V z) (zpowers (z : G))
      (Centralizer.localResidual L z)) :
    Centralizer.sourceClosure L V z ≤ pCore 2 (centralizer ({(z : G)} : Set G)) ∧
      ⁅Centralizer.sourceClosure L V z,pCore 2 (centralizer ({(z : G)} : Set G))⁆ ≤
        (zpowers (z : G)).subgroupOf (centralizer ({(z : G)} : Set G)) ∧
      ∀ x : Centralizer.sourceClosure L V z, ((x.val : G)^2) ∈ zpowers (z : G) := by
  let C := centralizer ({(z : G)} : Set G)
  let W := Centralizer.commutatorSpace L V z
  let Z := zpowers (z : G)
  let R := Centralizer.localResidual L z
  let A := R ⊔ (T : Subgroup G)
  have hWC : W ≤ C := Centralizer.commutatorSpace_le_centralizer L V z z.property hLN
  have hWV : W ≤ V := Centralizer.commutatorSpace_le L V z hLN
  have hZC : Z ≤ C := hZW.le.trans hWC
  have hRC : R ≤ C := (Centralizer.localResidual_le L z).trans inf_le_right
  have hAC : A ≤ C := sup_le hRC hTC
  have hCZ : C ≤ normalizer (Z : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer (Z : Set G))
    rw [show Z = zpowers (z : G) from rfl,zpowers_eq_closure,centralizer_closure]
  let Zc := Z.subgroupOf C
  let Wc := W.subgroupOf C
  let Ac := A.subgroupOf C
  let S := T.subtype hTC
  let : Zc.Normal := normal_subgroupOf_of_le_normalizer hCZ
  have hZWc : Zc < Wc := by
    apply lt_of_le_of_ne (subgroupOf_mono C hZW.le)
    intro he
    apply hZW.ne
    have hh := congrArg (Subgroup.map C.subtype) he
    exact (map_subgroupOf_eq_of_le hZC).symm.trans
      (hh.trans (map_subgroupOf_eq_of_le hWC))
  have hchar : centralizer (pCore 2 C : Set C) ≤ pCore 2 C :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T hE
      (isTwoLocal_involution_centralizer hz) hTC)
  have hWc : IsElementaryAbelian 2 Wc := by
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
    exact IsElementaryAbelian.subgroupOf hWC
  have hAW : Ac ≤ normalizer (Wc : Set C) := by
    rw [←subgroupOf_normalizer_eq hWC]
    exact subgroupOf_mono C hNW
  have hirr (U : Subgroup C) (hZU : Zc ≤ U) (hUW : U ≤ Wc)
      (hAU : Ac ≤ normalizer (U : Set C)) : U = Zc ∨ U = Wc := by
    have hZU' : Z ≤ U.map C.subtype := by
      simpa only [Zc,map_subgroupOf_eq_of_le hZC] using map_mono (f := C.subtype) hZU
    have hUW' : U.map C.subtype ≤ W := by
      simpa only [Wc,map_subgroupOf_eq_of_le hWC] using map_mono (f := C.subtype) hUW
    have hAU' : A ≤ normalizer (U.map C.subtype : Set G) := by
      have hh := (map_mono (f := C.subtype) hAU).trans (U.le_normalizer_map C.subtype)
      simpa only [Ac,map_subgroupOf_eq_of_le hAC] using hh
    rcases hact.natural_interval V W Z R (U.map C.subtype) hZU' hUW'
      (le_sup_left.trans hAU') with he|he
    · left
      apply map_injective C.subtype_injective
      simpa only [Zc,map_subgroupOf_eq_of_le hZC] using he
    · right
      apply map_injective C.subtype_injective
      simpa only [Wc,map_subgroupOf_eq_of_le hWC] using he
  have hh := normalClosure_core_of_irreducible_section Zc Wc Ac S hchar hWc hZWc
    (fun _ hx => hVT (hWV hx)) (fun _ ht => (show (T : Subgroup G) ≤ A from le_sup_right) ht) hAW hirr
  refine ⟨hh.2.1,hh.2.2,?_⟩
  let q := QuotientGroup.mk' Zc
  let E := Centralizer.sourceClosure L V z
  let : IsElementaryAbelian 2 (E.map q) := hh.1.elementary
  intro x
  have hp := elemPow_eq_one_of_isElementaryAbelian (p := 2) (q x.val)
    (mem_map_of_mem q x.property : q x.val ∈ E.map q)
  have hmem : x.val^2 ∈ Zc := (QuotientGroup.eq_one_iff _).mp (by change q (x.val^2)=1; rw [map_pow]; exact hp)
  exact hmem

omit [Finite G] in
/-- The full ambient centralizer core lies in the core of the actual local
residual with its original Sylow supplement. -/
theorem point_centralizer_core_le_local_core
    (L : Subgroup G) (T : Sylow 2 G) (z : G)
    (hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    (centralizer ({z} : Set G)).pCoreIn 2 ≤
      (Centralizer.localResidual L z ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let C := centralizer ({z} : Set G)
  let A := Centralizer.localResidual L z ⊔ (T : Subgroup G)
  have hCQ : C ≤ normalizer (C.pCoreIn 2 : Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hQT : C.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 C).le_sylow_of_normalized T (hTC.trans hCQ)
  have hAC : A ≤ C := sup_le ((Centralizer.localResidual_le L z).trans inf_le_right) hTC
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 C)
    (hQT.trans le_sup_right) (hAC.trans hCQ)

omit [Finite G] in
/-- The retained central line gives the elementary central quotient needed
by the extraspecial normal-closure criterion. -/
theorem point_closure_center_quotient
    (L V : Subgroup G) (z : G)
    (hcore : Centralizer.sourceClosure L V z ≤ pCore 2 (centralizer ({z} : Set G)))
    (hcomm : ⁅Centralizer.sourceClosure L V z,pCore 2 (centralizer ({z} : Set G))⁆ ≤
      (zpowers z).subgroupOf (centralizer ({z} : Set G)))
    (hsq : ∀ x : Centralizer.sourceClosure L V z, (x.val : G)^2 ∈ zpowers z) :
    IsElementaryAbelian 2 ((Centralizer.sourceClosure L V z) ⧸
      center (Centralizer.sourceClosure L V z)) := by
  let C := centralizer ({z} : Set G)
  let E := Centralizer.sourceClosure L V z
  have hZ : (zpowers z).subgroupOf C ≤ center C := by
    intro a ha
    apply mem_center_iff.mpr
    intro c
    apply Subtype.ext
    have hc : (c : G) ∈ centralizer (zpowers z : Set G) := by
      simpa only [zpowers_eq_closure,centralizer_closure] using c.property
    exact (hc a ha).symm
  let : IsMulCommutative (E ⧸ center E) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (by
      apply Subgroup.commutator_le.mpr
      intro x _ y _
      have hh : ⁅x.val,y.val⁆ ∈ center C := hZ
        (hcomm (commutator_mem_commutator x.property (hcore y.property)))
      apply mem_center_iff.mpr
      intro t
      exact Subtype.ext (mem_center_iff.mp hh t.val))
  refine { exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro a
  induction a using QuotientGroup.induction_on with
  | H x =>
    rw [←QuotientGroup.mk_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply mem_center_iff.mpr
    intro t
    exact Subtype.ext (mem_center_iff.mp (hZ (hsq x)) t.val)

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
