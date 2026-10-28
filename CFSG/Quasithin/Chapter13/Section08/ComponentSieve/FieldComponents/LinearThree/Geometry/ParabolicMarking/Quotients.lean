module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# Kernel-preserving source subgroup transport

The actual star map is H → H/O₂(H). Restriction to a subgroup X ≤ H
preserves its embedded two-core because the quotient kernel is a two-group.
The same quotient sends the source Sylow subgroup to a Sylow subgroup, and
its kernel is contained in L₁T. Thus L₁T ≤ M and H ≰ M imply properness of
(L₁T)*. Finally, if H* is the actual PSL₃(2), no subgroup of H has order
divisible by nine: |H| = 168·2ⁿ.

That order obstruction is needed when using Notation 13.2.1: R₁ is a
preimage in T, and may be larger than O₂(L₁T) in the covered-A₆ branch.
This module does not replace its definition by a two-core, or claim that the
source R₁ identification has already been assembled.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Notation
13.2.1 (printed p.877) and §13.8 (printed pp.946 and 953).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking
variable {G : Type*} [Group G] [Finite G]

/-- Local two-cores commute with the actual star quotient. The intersection
with H in starImage cannot be dropped without the containment X ≤ H. -/
theorem starImage_core (H X : Subgroup G) (hX : X ≤ H) :
    Source.starImage H (X.pCoreIn 2) = (Source.starImage H X).pCoreIn 2 := by
  have hsub : (X.pCoreIn 2).subgroupOf H = (X.subgroupOf H).pCoreIn 2 := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 X).trans hX),
      map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hX]
  unfold Source.starImage
  rw [hsub]
  apply map_pCoreIn_of_ker_isPGroup
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup


omit [Finite G] in
/-- The star-quotient kernel lies in every source parabolic over the Sylow. -/
theorem kernel_le_source_parabolic (H L₁ : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) :
    H.pCoreIn 2 ≤ L₁ ⊔ (T : Subgroup G) := by
  have hcore := pCoreIn_le_sylow H (T.subtype hTH)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at hcore
  exact hcore.trans le_sup_right

omit [Finite G] in
/-- Image containment keeps the intersection-with-H convention explicit. -/
theorem starImage_mono (H : Subgroup G) {X Y : Subgroup G} (hXY : X ≤ Y) :
    Source.starImage H X ≤ Source.starImage H Y :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono H hXY)

/-- The literal image of a Sylow subgroup is Sylow in H/O₂(H). -/
theorem starImage_sylow (H : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) :
    ∃ S : Sylow 2 (Source.Hstar H), (S : Subgroup (Source.Hstar H)) =
      Source.starImage H (T : Subgroup G) := by
  exact ⟨(T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)), rfl⟩

omit [Finite G] in
/-- Properness survives the star quotient when its actual kernel lies in X.
This is applied with X = L₁T ≤ M and H not contained in M. -/
theorem starImage_ne_top (H X M : Subgroup G) (hXM : X ≤ M)
    (hHM : ¬ H ≤ M) (hkernel : H.pCoreIn 2 ≤ X) : Source.starImage H X ≠ ⊤ := by
  intro he
  have hk : (QuotientGroup.mk' (pCore 2 H)).ker ≤ X.subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact hkernel ⟨x, hx, rfl⟩
  have hc := congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 H))) he
  rw [Source.starImage, Subgroup.comap_map_eq_self hk, Subgroup.comap_top] at hc
  apply hHM
  intro x hx
  exact hXM (show (⟨x, hx⟩ : H) ∈ X.subgroupOf H from hc ▸ Subgroup.mem_top _)

/-- Nine cannot divide the order of a source subgroup contained in H when
H/O₂(H) is the actual PSL₃(2). This excludes the covered-A₆ local order branch. -/
theorem not_nine_dvd_card (H X : Subgroup G) (hX : X ≤ H)
    (e : Source.Hstar H ≃* Matrix.PSL3Two.PSL) : ¬ 9 ∣ Nat.card X := by
  have hq : Nat.card (Source.Hstar H) = 168 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 H)
  change Nat.card H = Nat.card (Source.Hstar H) * Nat.card (pCore 2 H) at hcard
  rw [hq, hn] at hcard
  intro hd
  have hdiv : 9 ∣ Nat.card H := hd.trans (Subgroup.card_dvd_of_le hX)
  rw [hcard] at hdiv
  have hcop : Nat.Coprime 9 (2 ^ n) := (by decide : Nat.Coprime 9 2).pow_right n
  have : 9 ∣ 168 := hcop.dvd_of_dvd_mul_right hdiv
  norm_num at this

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking
