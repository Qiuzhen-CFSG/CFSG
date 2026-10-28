module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryModule
public import Theory.SpecificGroups.PSL3Four.CentralCover.FullPlaneNormalizer
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The full original point-residual core in the ordinary PSL3(4) closure

The unchanged elementary group U has order64 and contains the closure's
center of order4. Its full normalizer in that central PSL3(4) cover has
order3840. The original residual lies there and its A5 two-core quotient,
together with U in its two-core, gives the opposite order inequality.
Thus it is that full normalizer, its full two-core is U, and its center
is the original field point.

Source: Aschbacher--Smith 12.7.7, printed p.841, using I.2.2 and 12.7.4--5.
No block or core-identification premise is added.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original residual is the entire root-plane normalizer in its
ordinary closure, and its full core and center are the original U and Vt. -/
theorem tripleSixPointResidual_ordinary_block_core
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hcenter :
      let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      centerIn (conjugateSpanBy Lt H) = tripleSixPoint D a t)
    (eB :
      let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      let B := conjugateSpanBy Lt H
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    Lt = (normalizer (U.subgroupOf B : Set B)).map B.subtype ∧
      Lt.pCoreIn 2 = U ∧ centerIn Lt = tripleSixPoint D a t := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let Vt := tripleSixPoint D a t
  have hLK : Lt ≤ K := (map_subtype_le _).trans inf_le_left
  have hLB : Lt ≤ B := le_conjugateSpanBy Lt H
  have hUL : U ≤ Lt := (tripleSixPointCentralizerResidual_commutator D a t ht heven).2
  have hUB : U ≤ B := hUL.trans hLB
  have hV := tripleSixPoint_properties D a t ht
  have hVU : Vt ≤ U := hV.2.1
  have hVB : Vt ≤ B := hVU.trans hUB
  let : Group.IsPerfect Lt := tripleSixPointCentralizerResidual_perfect D a t ht heven
  let : Group.IsPerfect B := conjugateSpanBy_isPerfect Lt H
  let := D.elementary
  let Q := U.subgroupOf B
  let N := normalizer (Q : Set B)
  let f := eB.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hf : Function.Surjective f := eB.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = center B := by
    rw [MonoidHom.ker_comp_of_injective _ _ eB.injective,QuotientGroup.ker_mk']
  have hz : center B = Vt.subgroupOf B := by
    apply map_injective B.subtype_injective
    rw [map_subgroupOf_eq_of_le hVB,←centerIn_eq_map_center]
    exact hcenter
  have hUc : Nat.card U = 64 :=
    (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans Atlas.Codes.hexacode_card
  have hVc : Nat.card Vt = 4 := hV.2.2.1
  have hfc : Nat.card f.ker = 4 := by
    rw [hker,hz,Nat.card_congr (subgroupOfEquivOfLe hVB).toEquiv,hVc]
  have hkQ : f.ker ≤ Q := by rw [hker,hz]; exact subgroupOf_mono B hVU
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.subgroupOf hUB
  obtain ⟨_,hNc,hNz⟩ := Matrix.PSL3Four.FullPlaneNormalizer.full_plane_normalizer
    f hf (hker ▸ le_rfl) Q hkQ (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hUB).toEquiv,hUc,hfc])
  have hNcard : Nat.card N = 3840 := by simpa only [hfc] using hNc
  have hLN : Lt.subgroupOf B ≤ N := by
    intro l hl
    apply mem_normalizer_iff.mpr
    intro u
    exact mem_normalizer_iff.mp (D.normalizes (hLK hl)) (u : G)
  have hUcore : U ≤ Lt.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U) hUL
      (hLK.trans D.normalizes)
  have hcardcore : 64 ≤ Nat.card (pCore 2 Lt) := by
    have hh := card_le_of_le hUcore
    rwa [hUc,pCoreIn,card_map_of_injective Lt.subtype_injective] at hh
  have hquot : Nat.card (Lt ⧸ pCore 2 Lt) = 60 := by
    rw [Nat.card_congr (tripleSixPointResidualQuotientEquiv D a t ht heven).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hLtcard : Nat.card Lt = 60 * Nat.card (pCore 2 Lt) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 Lt),hquot]
  have hNL : Lt.subgroupOf B = N := eq_of_le_of_card_ge hLN (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hLB).toEquiv,hNcard,hLtcard]
    omega)
  have hcore64 : Nat.card (pCore 2 Lt) = 64 := by
    have hh := Nat.card_congr (subgroupOfEquivOfLe hLB).toEquiv
    rw [hNL,hNcard,hLtcard] at hh
    omega
  have hLNe : Lt = N.map B.subtype := by
    rw [←hNL,map_subgroupOf_eq_of_le hLB]
  have hcore : Lt.pCoreIn 2 = U := (eq_of_le_of_card_ge hUcore (by
    rw [pCoreIn,card_map_of_injective Lt.subtype_injective,hcore64,hUc])).symm
  have hcenterLt : centerIn Lt = Vt := by
    let d : N ≃* Lt := (MulEquiv.subgroupCongr hNL.symm).trans (subgroupOfEquivOfLe hLB)
    have hd (x : N) : (d x : G) = (x.val : G) := rfl
    have he : (center N).map d.toMonoidHom = center Lt := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩; exact (centerCongr d ⟨y,hy⟩).property
      · intro hx
        exact ⟨d.symm x,(centerCongr d.symm ⟨x,hx⟩).property,d.apply_symm_apply x⟩
    rw [centerIn_eq_map_center,←he,map_map]
    have heq : Lt.subtype.comp d.toMonoidHom = B.subtype.comp N.subtype := by ext x; exact hd x
    rw [heq,←map_map]
    change ((center N).map N.subtype).map B.subtype = Vt
    rw [hNz,hker,←centerIn_eq_map_center]
    exact hcenter
  exact ⟨hLNe,hcore,hcenterLt⟩

end CFSG.Quasithin.Chapter12.Section07
