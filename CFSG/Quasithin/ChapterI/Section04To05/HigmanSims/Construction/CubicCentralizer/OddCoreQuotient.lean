module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.AmbientSylow
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.OddCore
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import Theory.GroupTheory.CoprimeSubgroupCentralizer
public import Theory.GroupTheory.PrimeOrderLift

/-!
# The original cubic centralizer modulo its odd core

The quotient retains the marked involution. Its full centralizer is the
image of the original local centralizer, and is the image of an actual
original dihedral Sylow eight. The quotient map is injective on that eight.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

omit [Finite G] in
private theorem centralizer_powers {J : Type*} [Group J] (x : J) :
    centralizer (zpowers x : Set J) = centralizer ({x} : Set J) := by
  rw [zpowers_eq_closure, centralizer_closure]

/-- Quotienting the full original cubic centralizer by its actual odd core
retains the marked involution and its full dihedral Sylow centralizer. The
Sylow is the literal image of an original Sylow, with the quotient map
itself furnishing the equivalence. -/
theorem TypeAt.cubic_centralizer_oddCore_quotient (h : TypeAt z V) (t : G)
    (ht : t ∈ involutionCentralizer z) (ht3 : orderOf t = 3) :
    let C := centralizer ({t} : Set G)
    let O := pPrimeCore 2 C
    let X := C ⧸ O
    let q := QuotientGroup.mk' O
    ∃ zC : C, (zC : G) = z ∧ orderOf (q zC) = 2 ∧
      pPrimeCore 2 X = ⊥ ∧ O.map C.subtype = zpowers t ∧
      ((involutionCentralizer z).subgroupOf C).map q =
        centralizer ({q zC} : Set X) ∧
      Nat.card (centralizer ({q zC} : Set X)) = 8 ∧
      Nonempty ((centralizer ({q zC} : Set X)) ≃* DihedralGroup 4) ∧
      ∃ S : Sylow 2 C, Nat.card S = 8 ∧ Nonempty (S ≃* DihedralGroup 4) ∧
        let Sbar := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective O)
        (Sbar : Subgroup X) = centralizer ({q zC} : Set X) ∧
        ∃ e : S ≃* Sbar, ∀ s : S, (e s : X) = q (s : C) := by
  classical
  let C := centralizer ({t} : Set G)
  let O := pPrimeCore 2 C
  let X := C ⧸ O
  let q := QuotientGroup.mk' O
  let zC : C := ⟨z, mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp ht).symm⟩
  let L := (involutionCentralizer z).subgroupOf C
  have hO : O.map C.subtype = zpowers t := h.cubic_centralizer_oddCore t ht ht3
  have hO3 : Nat.card O = 3 := by
    rw [←card_map_of_injective C.subtype_injective, hO, Nat.card_zpowers, ht3]
  have hk3 : Nat.card q.ker = 3 := by rw [QuotientGroup.ker_mk']; exact hO3
  have hcop : Nat.Coprime 2 (Nat.card q.ker) := by rw [hk3]; decide
  have hz2 : orderOf zC = 2 := (orderOf_coe zC).symm.trans h.involution
  have hqz2 : orderOf (q zC) = 2 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker
      (IsPGroup.of_card (n := 1) (by simpa using hk3)) zC
      (by rw [hz2]; decide : Nat.Coprime 3 (orderOf zC))).trans hz2
  have hL : L = centralizer ({zC} : Set C) := by
    ext x
    constructor
    · intro hx
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hx))
    · intro hx
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))
  have himage : L.map q = centralizer ({q zC} : Set X) := by
    have hp : IsPGroup 2 (zpowers zC) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, hz2]; decide)
    have hh := map_centralizer_eq_of_isPGroup_of_surjective_coprime 2 (zpowers zC) hp q
      (QuotientGroup.mk'_surjective O) hcop
    rw [MonoidHom.map_zpowers, centralizer_powers, centralizer_powers] at hh
    exact hL ▸ hh
  have hOL : O ≤ L := by
    intro x hx
    have hxT : (x : G) ∈ zpowers t := hO ▸ mem_map_of_mem C.subtype hx
    exact zpowers_le.mpr ht hxT
  have hL24 : Nat.card L = 24 := by
    rw [←card_map_of_injective C.subtype_injective, subgroupOf_map_subtype]
    exact (h.cubic_point_centralizer_order t ht ht3).1
  let f : L →* X := q.comp L.subtype
  have hk : f.ker = O.subgroupOf L := by
    ext x
    change q (x : C) = 1 ↔ (x : C) ∈ O
    exact QuotientGroup.eq_one_iff _
  have hf3 : Nat.card f.ker = 3 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe hOL).toEquiv, hO3]
  have hr : f.range = L.map q := by rw [MonoidHom.range_comp, range_subtype]
  have hcentral8 : Nat.card (centralizer ({q zC} : Set X)) = 8 := by
    have hh := f.ker.card_mul_index
    rw [hf3, index_ker, hr, himage, hL24] at hh
    omega
  obtain ⟨S, hS8, ⟨eS⟩, hcenter⟩ := h.cubic_centralizer_ambient_sylow t ht ht3
  let D := (S : Subgroup C).map C.subtype
  have hzD : z ∈ (center D).map D.subtype := hcenter.symm ▸ mem_zpowers z
  obtain ⟨zD, hzD, hzval⟩ := hzD
  have hSL : (S : Subgroup C) ≤ L := by
    intro s hs
    have hsD : (s : G) ∈ D := mem_map_of_mem C.subtype hs
    have hh := congrArg Subtype.val (mem_center_iff.mp hzD (⟨s, hsD⟩ : D))
    apply mem_centralizer_singleton_iff.mpr
    change (s : G) * z = z * (s : G)
    change (s : G) * (zD : G) = (zD : G) * (s : G) at hh
    rw [show (zD : G) = z from hzval] at hh
    exact hh
  let Sbar : Sylow 2 X := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective O)
  let e : S ≃* Sbar := MulEquiv.ofBijective (q.subgroupMap (S : Subgroup C)) ⟨by
    intro x y hh
    exact injective_comp_subtype_of_coprime_ker q hcop (S : Subgroup C) S.isPGroup'
      (congrArg Subtype.val hh), q.subgroupMap_surjective (S : Subgroup C)⟩
  have hSbar8 : Nat.card Sbar = 8 := (Nat.card_congr e.toEquiv).symm.trans hS8
  have hSbar : (Sbar : Subgroup X) = centralizer ({q zC} : Set X) := by
    apply eq_of_le_of_card_ge ?_ (by rw [hcentral8, hSbar8])
    change (S : Subgroup C).map q ≤ centralizer ({q zC} : Set X)
    rw [←himage]
    exact map_mono hSL
  have hmodel : Nonempty ((centralizer ({q zC} : Set X)) ≃* DihedralGroup 4) :=
    ⟨(MulEquiv.subgroupCongr hSbar).symm.trans (e.symm.trans eS)⟩
  exact ⟨zC, rfl, hqz2, pPrimeCore_quotient_pPrimeCore_eq_bot 2, hO, himage,
    hcentral8, hmodel, S, hS8, ⟨eS⟩, hSbar, e, fun _ => rfl⟩

end CFSG.Quasithin.HigmanSims
