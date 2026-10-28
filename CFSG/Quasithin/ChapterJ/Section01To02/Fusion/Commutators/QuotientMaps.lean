module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Statements
public import Theory.GroupAction.QuotientCommutatorPairing

/-!
# The actual quotient commutator row in J.2.4

The source quotient is H/Z. Images preserve the ambient cyclic subgroups
and commutators, and equal images of subgroups containing Z lift to equality.
For h in HC, the central commutator pairing gives a homomorphism Q → H/Z
whose range is exactly [h̃,Q̃]. The only commutator bounds used are the
preceding J.2.2 bounds [HC,Q] ≤ U and [U,Q] ≤ Z.

J.2.1 also gives |Ũ| = 16. Together these facts supply the exact kernel
count in the later centralizer proof, without identifying an abstract
quotient with the source quotient by cardinality alone.

Source: Aschbacher–Smith, Lemma J.2.4, printed p.434 (PDF p.445).
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterJ.Fusion
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem map_inclusion {A D H : Subgroup G} (hAD : A ≤ D) (hDH : D ≤ H) :
    (A.subgroupOf D).map (inclusion hDH) = A.subgroupOf H := by
  apply map_injective H.subtype_injective
  rw [map_map, show H.subtype.comp (inclusion hDH) = D.subtype from rfl,
    map_subgroupOf_eq_of_le hAD, map_subgroupOf_eq_of_le (hAD.trans hDH)]

/-- The actual quotient map preserves ambient commutators of subgroups of H. -/
theorem modZ_commutator (d : TypeRuSetup G) {A D : Subgroup G}
    (hA : A ≤ d.H) (hD : D ≤ d.H) :
    modZ d ⁅A,D⁆ = ⁅modZ d A,modZ d D⁆ := by
  have hpre : ⁅A,D⁆.subgroupOf d.H = ⁅A.subgroupOf d.H,D.subgroupOf d.H⁆ := by
    apply map_injective d.H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((commutator_le_sup A D).trans (sup_le hA hD)), map_commutator,
      map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hD]
  unfold modZ
  rw [hpre, map_commutator]

/-- Cyclic images use the literal representative in H. -/
theorem modZ_zpowers (d : TypeRuSetup G) (h : d.H) :
    modZ d (zpowers (h : G)) = zpowers (centerQuotientMap d h) := by
  have hp : (zpowers (h : G)).subgroupOf d.H = zpowers h := by
    apply map_injective d.H.subtype_injective
    rw [map_subgroupOf_eq_of_le (zpowers_le.mpr h.property), MonoidHom.map_zpowers]
    rfl
  unfold modZ
  rw [hp, MonoidHom.map_zpowers]

/-- Quotient images determine subgroups containing the actual kernel Z. -/
theorem eq_of_modZ_eq (d : TypeRuSetup G) {A D : Subgroup G}
    (hA : A ≤ d.H) (hD : D ≤ d.H) (hZA : d.Z ≤ A) (hZD : d.Z ≤ D)
    (he : modZ d A = modZ d D) : A = D := by
  have hker : (centerQuotientMap d).ker = d.Z.subgroupOf d.H := QuotientGroup.ker_mk' _
  have hh := congrArg (Subgroup.comap (centerQuotientMap d)) he
  change ((A.subgroupOf d.H).map _).comap _ = ((D.subgroupOf d.H).map _).comap _ at hh
  have hKA : (centerQuotientMap d).ker ≤ A.subgroupOf d.H := by
    rw [hker]
    exact fun _ hx => hZA hx
  have hKD : (centerQuotientMap d).ker ≤ D.subgroupOf d.H := by
    rw [hker]
    exact fun _ hx => hZD hx
  rw [comap_map_eq_self hKA, comap_map_eq_self hKD] at hh
  have hh' := congrArg (Subgroup.map d.H.subtype) hh
  simpa only [map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hD] using hh'

/-- The J.2.1 center order computes the size of the literal U-image. -/
theorem card_modZ_U (d : TypeRuSetup G) (hZ : Nat.card d.Z = 2) :
    Nat.card (modZ d d.U) = 16 := by
  have h := relIndex_mul_relIndex (⊥ : Subgroup G) d.Z d.U bot_le d.ru2.natural.kernel_le
  rw [relIndex_bot_left, relIndex_bot_left, hZ, d.ru2.card_U hZ] at h
  have hm : Nat.card (modZ d d.U) = d.Z.relIndex d.U := by
    unfold modZ
    rw [← relIndex_ker, show (centerQuotientMap d).ker = d.Z.subgroupOf d.H from
      QuotientGroup.ker_mk' _, relIndex_subgroupOf d.ru2.natural.section_le]
  omega

/-- The central commutator row, valued in the source's actual H/Z. -/
noncomputable def commutatorRow (d : TypeRuSetup G) [IsElementaryAbelian 2 d.U]
    (hUHC : d.U ≤ d.HC) (hCQ : ⁅d.HC,d.Q⁆ ≤ d.U) (hUQ : ⁅d.U,d.Q⁆ ≤ d.Z)
    (h : d.HC) : d.Q →* (d.H ⧸ d.Z.subgroupOf d.H) := by
  letI := d.ru2.natural.kernel_normal
  let m : d.U →* (d.H ⧸ d.Z.subgroupOf d.H) :=
    (centerQuotientMap d).comp (inclusion d.ru2.natural.section_le)
  let g := QuotientGroup.lift (d.Z.subgroupOf d.U) m (by
    intro z hz
    change centerQuotientMap d ⟨z,d.ru2.natural.section_le z.property⟩ = 1
    exact (QuotientGroup.eq_one_iff _).mpr hz)
  exact g.comp (centralQuotientCommutatorPairing d.HC d.Q d.U d.Z hUHC
    inf_le_right hCQ hUQ h)

theorem commutatorRow_apply (d : TypeRuSetup G) [IsElementaryAbelian 2 d.U]
    (hUHC : d.U ≤ d.HC) (hCQ : ⁅d.HC,d.Q⁆ ≤ d.U) (hUQ : ⁅d.U,d.Q⁆ ≤ d.Z)
    (h : d.HC) (q : d.Q) :
    commutatorRow d hUHC hCQ hUQ h q = centerQuotientMap d
      ⟨⁅(h : G),(q : G)⁆,d.ru2.natural.section_le
        (hCQ (commutator_mem_commutator h.property q.property))⟩ := by
  unfold commutatorRow
  rw [MonoidHom.comp_apply, centralQuotientCommutatorPairing_apply]
  rfl

theorem commutatorRow_range (d : TypeRuSetup G) [IsElementaryAbelian 2 d.U]
    (hUHC : d.U ≤ d.HC) (hCQ : ⁅d.HC,d.Q⁆ ≤ d.U) (hUQ : ⁅d.U,d.Q⁆ ≤ d.Z)
    (h : d.HC) :
    (commutatorRow d hUHC hCQ hUQ h).range =
      ⁅zpowers (centerQuotientMap d ⟨h,h.property.1⟩), modZ d d.Q⁆ := by
  let := d.ru2.natural.kernel_normal
  have hcomm : ⁅zpowers (h : G), d.Q⁆ ≤ d.U :=
    (commutator_mono (zpowers_le.mpr h.property) le_rfl).trans hCQ
  unfold commutatorRow
  rw [MonoidHom.range_comp, centralQuotientCommutatorPairing_range,
    map_map]
  change ((⁅zpowers (h : G),d.Q⁆.subgroupOf d.U).map
    ((centerQuotientMap d).comp (inclusion d.ru2.natural.section_le))) = _
  rw [← map_map, map_inclusion hcomm d.ru2.natural.section_le]
  change modZ d ⁅zpowers (h : G),d.Q⁆ = _
  rw [modZ_commutator d (zpowers_le.mpr h.property.1) (pCoreIn_le 2 d.H),
    modZ_zpowers d ⟨h,h.property.1⟩]
end CFSG.Quasithin.ChapterJ.Fusion
