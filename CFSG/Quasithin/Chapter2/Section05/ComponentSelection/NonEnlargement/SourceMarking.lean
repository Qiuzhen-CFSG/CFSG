module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement.Ordinary
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ModelSource

/-!
# Retaining the original source marking on a containing component

The ambient subgroup T from SourceTuple is a full Sylow subgroup of G:
its order equals that of the fixed ambient Sylow inside M. Uniqueness of
its maximal two-local overgroup follows from the original fixed-Sylow
uniqueness. Thus every ordinary component of a Gamma-zero group whose
Sylow image is the original S receives the complete MathieuSourceSetup,
with exactly the original z. This is the source interface used to classify
the containing component in 2.5.6, printed p.554.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
open ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
variable {M H S T X L : Subgroup G} {z : G}

theorem exists_setup_of_same_sylow
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N=M)
    (d : SourceTuple M H S T z) (hX : X∈gammaZero (Chapter1.He G) M)
    (P : Sylow 2 X) (hP : (P:Subgroup X).map X.subtype=S)
    (hL : IsComponentIn L X) : Nonempty (MathieuSourceSetup X L M P z) := by
  classical
  obtain ⟨R₀,hR₀⟩ := d.sylow_maximal
  have hTcard : Nat.card T=2^(Nat.card G).factorization 2 := by
    rw [←hR₀,sylow_image_card,twoPart_eq_sylow_card T₀ hT₀M]
    exact T₀.card_eq_multiplicity
  let R : Sylow 2 G := Sylow.ofCard T hTcard
  have hRT : (R:Subgroup G)=T := Sylow.coe_ofCard T hTcard
  have hRM : (R:Subgroup G)≤M := by rw [hRT,←hR₀]; exact map_subtype_le _
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → (R:Subgroup G)≤N → N=M := by
    intro N hN hRN
    have hNM : N≤M := by
      apply core_overgroup_le_of_sylow T₀ hT₀M hunique
        (Chapter1.mem_H_of_isTwoLocal hN.1) (R.subtype hRM)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hRM] using hRN
    exact le_antisymm hNM (hN.2 hM.1 hNM)
  have hSM : S≤M := by
    obtain ⟨Q,hQ⟩ := d.sylow_intersection
    exact hQ ▸ (map_subtype_le (Q:Subgroup ↥(H⊓M))).trans inf_le_right
  obtain ⟨U,HU,hpair,hUS,_⟩ := exists_saturated_pair_aligned hX P (hP ▸ hSM)
  exact ⟨{
    T := R
    maximal := hM
    sylow_le := hRM
    unique := huniq
    gamma := hX
    U := U
    HU := HU
    pair := hpair
    base_le := hUS
    component_le := hL.1
    component := hL.2
    sylow_lt := by rw [hP,hRT]; exact d.lt
    center_le := by rw [hP,hRT]; exact d.center_le
    mem_center := by rw [hRT]; exact d.mem_center
    involution := d.involution }⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
