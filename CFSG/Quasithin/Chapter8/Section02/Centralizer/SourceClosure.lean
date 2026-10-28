module
public import CFSG.Quasithin.Chapter8.Section02.Centralizer.Definitions
public import Theory.GroupTheory.ReducedNormal.SectionClosureCore

/-!
# The source point closure from an irreducible central section

The source V_z=[V,O₂(L_z)] is restricted to C_G(z), and its normal closure
is formed there. The characteristic-two bound and irreducibility of
V_z/⟨z⟩ under the original point residual put this closure in O₂(C_G(z)).
It centralizes the whole core modulo the original central line, and its
squares lie in that line. The statement allows the different natural
point-section actions in the three source rows.

Source: Aschbacher--Smith 8.2.12, first paragraph, printed p.722,
refs/quasithin.pdf. The M22 source consumer must supply the interval from
the native hexad action; the later crossing and core-product conclusions
remain separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Centralizer
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

/-- The actual relative normal closure is central in the full two-core modulo
the original central involution, and its quotient has exponent two. -/
theorem sourceClosure_core_of_irreducible_section
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G) (z : V)
    (hchar : centralizer (pCore 2 (centralizer ({(z : G)} : Set G)) :
      Set (centralizer ({(z : G)} : Set G))) ≤
        pCore 2 (centralizer ({(z : G)} : Set G)))
    (hLN : L ≤ normalizer (V : Set G)) (hVT : V ≤ T)
    (hTC : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hZW : zpowers (z : G) < commutatorSpace L V z)
    (hNW : localResidual L z ⊔ (T : Subgroup G) ≤
      normalizer (commutatorSpace L V z : Set G))
    (hinterval : ∀ Y : Subgroup G, zpowers (z : G) ≤ Y →
      Y ≤ commutatorSpace L V z →
      localResidual L z ≤ normalizer (Y : Set G) →
      Y = zpowers (z : G) ∨ Y = commutatorSpace L V z) :
    sourceClosure L V z ≤ pCore 2 (centralizer ({(z : G)} : Set G)) ∧
      ⁅sourceClosure L V z,pCore 2 (centralizer ({(z : G)} : Set G))⁆ ≤
        (zpowers (z : G)).subgroupOf (centralizer ({(z : G)} : Set G)) ∧
      ∀ x : sourceClosure L V z, ((x.val : G)^2) ∈ zpowers (z : G) := by
  let C := centralizer ({(z : G)} : Set G)
  let W := commutatorSpace L V z
  let Z := zpowers (z : G)
  let R := localResidual L z
  let A := R ⊔ (T : Subgroup G)
  have hWC : W ≤ C := commutatorSpace_le_centralizer L V z z.property hLN
  have hWV : W ≤ V := commutatorSpace_le L V z hLN
  have hZC : Z ≤ C := hZW.le.trans hWC
  have hRC : R ≤ C := (localResidual_le L z).trans inf_le_right
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
    rcases hinterval (U.map C.subtype) hZU' hUW'
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
  let E := sourceClosure L V z
  let : IsElementaryAbelian 2 (E.map q) := hh.1.elementary
  intro x
  have hp := elemPow_eq_one_of_isElementaryAbelian (p := 2) (q x.val)
    (mem_map_of_mem q x.property : q x.val ∈ E.map q)
  have hmem : x.val^2 ∈ Zc := (QuotientGroup.eq_one_iff _).mp (by change q (x.val^2)=1; rw [map_pow]; exact hp)
  exact hmem

omit [Finite G] in
/-- The last paragraph of 8.2.12 identifies the full two-core directly
from its cover and intersection with the original local-join core. -/
theorem sourceClosure_eq_core_of_cover
    (L V : Subgroup G) (z : G)
    (Q : Subgroup (centralizer ({z} : Set G)))
    (hcore : sourceClosure L V z ≤ pCore 2 (centralizer ({z} : Set G)))
    (hcover : pCore 2 (centralizer ({z} : Set G)) ≤ sourceClosure L V z ⊔ Q)
    (hcap : pCore 2 (centralizer ({z} : Set G)) ⊓ Q ≤
      (commutatorSpace L V z).subgroupOf (centralizer ({z} : Set G))) :
    sourceClosure L V z = pCore 2 (centralizer ({z} : Set G)) := by
  apply le_antisymm hcore
  intro x hx
  obtain ⟨e,he,q,hq,rfl⟩ := mem_sup_of_normal_left.mp (hcover hx)
  have hqc : q ∈ pCore 2 (centralizer ({z} : Set G)) := by
    have hh := (pCore 2 (centralizer ({z} : Set G))).mul_mem
      ((pCore 2 (centralizer ({z} : Set G))).inv_mem (hcore he)) hx
    simpa only [inv_mul_cancel_left] using hh
  exact (sourceClosure L V z).mul_mem he (le_normalClosure (hcap ⟨hqc,hq⟩))

end CFSG.Quasithin.Chapter8.Section02.Centralizer
