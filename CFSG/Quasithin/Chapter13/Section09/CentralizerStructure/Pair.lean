module

public import CFSG.Quasithin.Chapter13.Section09.SourceSetup
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import Theory.GroupTheory.SylowCentralQuotientCore
public import Stellmacher.ElementaryAbelianMaxJ

/-!
# The common centralizer in 13.9.7

The marked inputs below are precisely the parts of the local geometry used
here: z is central in the original Sylow T, J(T) is Sylow in C_G(t), its
normalizer is T, and its derived subgroup lies in ⟨t,z⟩. The local-geometry
owner constructs these inputs; none is a conclusion of 13.9.7.

Even characteristic first gives characteristic two in C_G(z), and then
in C_G(z,t). Quotienting the latter by its actual central subgroup ⟨t,z⟩
makes the Sylow subgroup abelian. Self-centralization forces J(T) to be
the two-core. Its prescribed normalizer then gives C_G(z,t) = J(T).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.9.7, printed p.971 (PDF p.988).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
open Subgroup

variable {G : Type*} [Group G]

/-- The original elementary Thompson subgroup, with its maximum-order convention. -/
noncomputable abbrev thompson (d : Configuration G) : Subgroup G :=
  Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G)

/-- The marked part of 13.9.2 and its preceding setup needed for 13.9.7.
The Sylow assertion is inside C_G(t), and the normalizer is ambient. -/
structure PairData (d : Configuration G) where
  t : G
  z : G
  t_order : orderOf t = 2
  z_order : orderOf z = 2
  t_mem : t ∈ (d.T : Subgroup G)
  z_mem : z ∈ (d.T : Subgroup G)
  z_central : (d.T : Subgroup G) ≤ centralizer ({z} : Set G)
  thompson_normalizer : normalizer (thompson d : Set G) = d.T
  thompson_sylow : ∃ S : Sylow 2 (centralizer ({t} : Set G)),
    (S : Subgroup (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype = thompson d
  thompson_derived : ⁅thompson d, thompson d⁆ ≤ zpowers t ⊔ zpowers z

namespace PairData
variable {d : Configuration G} (m : PairData d)

abbrev C : Subgroup G := centralizer ({m.z} : Set G)
abbrev D : Subgroup G := m.C ⊓ centralizer ({m.t} : Set G)
abbrev Z : Subgroup G := zpowers m.z
abbrev V : Subgroup G := zpowers m.t ⊔ m.Z

theorem thompson_le_T : thompson d ≤ (d.T : Subgroup G) :=
  sSup_le (fun _ h => h.1)

theorem thompson_le_D : thompson d ≤ m.D := by
  obtain ⟨S, hS⟩ := m.thompson_sylow
  exact le_inf ((thompson_le_T (d := d)).trans m.z_central)
    (hS ▸ map_subtype_le (S : Subgroup (centralizer ({m.t} : Set G))))

theorem t_mem_C : m.t ∈ m.C := m.z_central m.t_mem

theorem V_le_D : m.V ≤ m.D := by
  apply sup_le <;> apply zpowers_le.mpr
  · exact ⟨m.t_mem_C, mem_centralizer_singleton_iff.mpr rfl⟩
  · exact ⟨mem_centralizer_singleton_iff.mpr rfl,
      mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp m.t_mem_C).symm⟩

theorem V_central : m.V.subgroupOf m.D ≤ center m.D := by
  intro v hv
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  have hV : m.V ≤ centralizer ({(x : G)} : Set G) := by
    apply sup_le <;> apply zpowers_le.mpr
    · exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp x.property.2).symm
    · exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp x.property.1).symm
  exact (mem_centralizer_singleton_iff.mp (hV hv)).symm

variable [Finite G]

/-- The z-centralizer has characteristic two by 1.1.4(6), using condition
(E) at the original T. -/
theorem centralizer_characteristic_two (hE : IsEvenCharacteristicAt d.T) :
    HasCharacteristicTwo m.C := by
  have hp : IsPGroup 2 m.Z :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, m.z_order, pow_one])
  have hZC : m.Z ≤ m.C := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCZ : m.C ≤ normalizer (m.Z : Set G) := by
    simpa only [zpowers_eq_closure, centralizer_closure] using centralizer_le_normalizer (m.Z : Set G)
  have hZcore := le_pCoreIn_of_normalizes hp hZC hCZ
  apply Chapter1.mem_He_iff.mp
  apply Chapter1.lemma_1_1_4_6 d.T hE
  refine ⟨?_, m.z_central⟩
  intro he
  have hz1 : m.z = 1 := (mem_bot.mp (he ▸ hZcore (mem_zpowers m.z)))
  have ho := m.z_order
  rw [hz1, orderOf_one] at ho
  omega

/-- The common centralizer inherits characteristic two by 1.1.3(2). -/
theorem pair_characteristic_two (hE : IsEvenCharacteristicAt d.T) :
    HasCharacteristicTwo m.D := by
  have hp : IsPGroup 2 (zpowers m.t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, m.t_order, pow_one])
  have hc := pCoreIn_selfCentralizing_centralizer
    (Chapter1.mem_He_iff.mpr (m.centralizer_characteristic_two hE)) hp
    (zpowers_le.mpr m.t_mem_C)
  apply Chapter1.mem_He_iff.mp
  change m.D ⊓ centralizer (m.D.pCoreIn 2 : Set G) ≤ m.D.pCoreIn 2
  simpa only [zpowers_eq_closure, centralizer_closure] using hc

/-- The actual denominator in the source quotient is central in the common centralizer. -/
instance pairDenominator_normal : (m.V.subgroupOf m.D).Normal :=
  ⟨fun n hn g => by
    have he := mem_center_iff.mp (m.V_central hn) g
    rwa [he, mul_inv_cancel_right]⟩

/-- Source 13.9.7 from its explicit earlier marked inputs. Only the (E)
part of the ambient QTKE hypothesis is used. -/
theorem source13_9_7 (hE : IsEvenCharacteristicAt d.T) : m.D = thompson d := by
  obtain ⟨S, hS⟩ := m.thompson_sylow
  let Ct := centralizer ({m.t} : Set G)
  have hSD : (S : Subgroup Ct) ≤ m.D.subgroupOf Ct := by
    intro x hx
    exact m.thompson_le_D (hS ▸ mem_map_of_mem Ct.subtype hx)
  let R₀ := S.subtype hSD
  let e : (m.D.subgroupOf Ct) ≃* m.D := subgroupOfEquivOfLe inf_le_right
  let R := R₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hR : (R : Subgroup m.D).map m.D.subtype = thompson d := by
    change (((S : Subgroup Ct).subgroupOf (m.D.subgroupOf Ct)).map e.toMonoidHom).map
      m.D.subtype = thompson d
    rw [map_map]
    have hf : m.D.subtype.comp e.toMonoidHom =
        Ct.subtype.comp (m.D.subgroupOf Ct).subtype := rfl
    rw [hf, ← map_map, map_subgroupOf_eq_of_le hSD]
    exact hS
  have hcomm : ⁅(R : Subgroup m.D), (R : Subgroup m.D)⁆ ≤ m.V.subgroupOf m.D := by
    rw [subgroupOf, ← map_le_iff_le_comap, map_commutator, hR]
    exact m.thompson_derived
  have hcore := R.eq_pCore_of_commutator_le_central (m.V.subgroupOf m.D)
    m.V_central (m.pair_characteristic_two hE) hcomm
  have hJcore : thompson d = m.D.pCoreIn 2 := by
    rw [← hR, hcore]
    rfl
  have hn : m.D ≤ normalizer (thompson d : Set G) := by
    rw [hJcore]
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 m.D).le_normalizer_map m.D.subtype
  have hDT : m.D ≤ (d.T : Subgroup G) := m.thompson_normalizer ▸ hn
  have hDp := d.T.isPGroup'.to_le hDT
  have hh := inf_eq_sylow_map S hDp (hS.symm ▸ m.thompson_le_D)
  rw [inf_eq_left.mpr (show m.D ≤ Ct from inf_le_right), hS] at hh
  exact hh

end PairData
end CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
