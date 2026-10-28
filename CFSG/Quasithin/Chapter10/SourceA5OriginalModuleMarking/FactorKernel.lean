module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.Recognition
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction
public import Theory.Representation.BinaryConjugationSection.ActionKernel
public import Theory.GroupTheory.Commutator.CentralQuotientKernel

/-!
# The original factor quotient has the full local action kernel

The original A₅ quotient acts faithfully on W/C_W(L), where W=[V,L], and
O₂(L) centralizes V. Full commutator generation therefore identifies the
kernel on this central quotient with the kernel on W for every actor
normalizing L and W.

The separate-factor hypothesis Wᵗ≤C_G(L) makes W and Wᵗ distinct. The actual
pair action then forces N_M(W)≤N_G(L). Consequently an element of M stabilizing
W and centralizing V/Wᵗ already centralizes W. This proves the source kernel
step directly in M, without conjugating the offender into T. The genuine
separate-factor premise remains explicit; it is not inferred from the pair
decomposition alone. No module irreducibility is needed for this kernel step.
Source: Aschbacher–Smith, 10.1.1 and 10.2.12, printed pp.741 and 754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))

local instance originalFactorKernelElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

theorem source_original_moved_fixed_normalizer :
    normalizer (L : Set G) ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤
      normalizer (sourceMovedFixed D : Set G) :=
  (le_inf inf_le_right (inf_le_left.trans (normalizer_le_normalizer_centralizer L))).trans
    inf_normalizer_le_normalizer_inf

include e in
theorem source_a5_original_moved_quotient_kernel :
    commutatorPreimage L ⁅D.fullModule,L⁆ (sourceMovedFixed D) = L.pCoreIn 2 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let ρ := originalMovedQuotientAction D e
  let c := originalMovedQuotientSection D e
  have hn : L ≤ normalizer (sourceMovedFixed D : Set G) :=
    (le_inf L.le_normalizer (normalizer_commutator_ge_right _ _)).trans
      (source_original_moved_fixed_normalizer D)
  have he := c.action_kernel_map hn
  change ((ρ.comp q).ker).map L.subtype = _ at he
  rw [MonoidHom.ker_comp_of_injective q ρ (originalMovedQuotientAction_faithful D e),
    MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (pCore 2 L)) e.toMonoidHom e.injective,
    QuotientGroup.ker_mk'] at he
  exact he.symm

include e in
theorem source_a5_original_moved_normalizer_quotient_kernel :
    commutatorPreimage
      (normalizer (L : Set G) ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
      ⁅D.fullModule,L⁆ (sourceMovedFixed D) =
    (normalizer (L : Set G) ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) ⊓
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let H := normalizer (L : Set G) ⊓ normalizer (W : Set G)
  have hAH : L ≤ H := le_inf L.le_normalizer (normalizer_commutator_ge_right _ _)
  have hker : commutatorPreimage L W (sourceMovedFixed D) ≤ centralizer (W : Set G) := by
    rw [source_a5_original_moved_quotient_kernel D e]
    have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    exact (source_component_core_centralizes_fullModule D).trans (centralizer_le hWV)
  apply le_antisymm
  · exact le_inf (commutatorPreimage_le _ _ _)
      (commutatorPreimage_le_centralizer_of_fully_moved H L W (sourceMovedFixed D)
        hAH inf_le_left inf_le_right (source_original_moved_fixed_normalizer D)
        inf_le_right (source_full_moved_eq_commutator D) hker)
  · apply le_commutatorPreimage inf_le_left
    exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le

include e in
theorem source_a5_original_moved_fixed_kernel_element
    {b : G} (hbL : b ∈ normalizer (L : Set G))
    (hbW : b ∈ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hcomm : ⁅zpowers b,⁅D.fullModule,L⁆⁆ ≤ sourceMovedFixed D) :
    b ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  have hH : zpowers b ≤ normalizer (L : Set G) ⊓
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := zpowers_le.mpr ⟨hbL,hbW⟩
  have hb := le_commutatorPreimage hH hcomm (mem_zpowers b)
  rw [source_a5_original_moved_normalizer_quotient_kernel D e] at hb
  exact hb.2


/-- With the actual separate-factor condition, every M-stabilizer of the
moved factor normalizes the corresponding original component. -/
theorem source_original_moved_stabilizer_le_component_normalizer
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G)) :
    D.maximalLocal ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤
      normalizer (L : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let U := W.map (MulAut.conj t).toMonoidHom
  have hne : W ≠ U := by
    intro he
    have hWC : W ≤ centralizer (L : Set G) := he.le.trans hcross
    have hz : ⁅W,L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hWC
    exact source_full_moved_ne_bot D ((source_full_moved_eq_commutator D).symm.trans hz)
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hmap (m : G) (hm : m ∈ D.maximalLocal) :
      D.fullModule.map (MulAut.conj m).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hm)
  intro b hb
  rcases source_nonnormal_maximal_pair D hn ht htn b hb.1 with he | he
  · exact mem_normalizer_iff_map_conj_eq.mpr he
  · have hw : W.map (MulAut.conj b).toMonoidHom = U := by
      change (⁅D.fullModule,L⁆).map (MulAut.conj b).toMonoidHom =
        (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
      rw [map_commutator,hmap b hb.1,he,map_commutator,
        hmap t (le_normalizer_componentOrbit L T ht)]
    exact (hne ((mem_normalizer_iff_map_conj_eq.mp hb.2).symm.trans hw)).elim

include e in
/-- The full M-stabilizer has no nontrivial action on W hidden in the partner
factor. This is the source equality C_T(V/V₂)=C_T(V₁), in the full M form. -/
theorem source_a5_original_partner_quotient_kernel_element
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G))
    {b : G} (hbM : b ∈ D.maximalLocal)
    (hbW : b ∈ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hcomm : ⁅zpowers b,D.fullModule⁆ ≤
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) :
    b ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  apply source_a5_original_moved_fixed_kernel_element D e
    (source_original_moved_stabilizer_le_component_normalizer D ht htn hcross ⟨hbM,hbW⟩) hbW
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  exact le_inf (le_normalizer_iff_commutator_le_right.mp (zpowers_le.mpr hbW))
    (((commutator_mono le_rfl hWV).trans hcomm).trans hcross)

include e in
/-- The literal local automizer has the same kernel on W and its original
central quotient, whenever its stabilizer normalizes the component. -/
theorem source_a5_original_local_quotient_kernel
    (hNL : D.maximalLocal ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) :
    commutatorPreimage
      (D.maximalLocal ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
      ⁅D.fullModule,L⁆ (sourceMovedFixed D) =
    (D.maximalLocal ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) ⊓
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let H := D.maximalLocal ⊓ normalizer (W : Set G)
  let N := normalizer (L : Set G) ⊓ normalizer (W : Set G)
  have hHN : H ≤ N := le_inf hNL inf_le_right
  have hHZ : H ≤ normalizer (sourceMovedFixed D : Set G) :=
    hHN.trans (source_original_moved_fixed_normalizer D)
  have hk : commutatorPreimage H W (sourceMovedFixed D) ≤
      commutatorPreimage N W (sourceMovedFixed D) :=
    le_commutatorPreimage ((commutatorPreimage_le _ _ _).trans hHN)
      (commutator_commutatorPreimage_le _ _ _ hHZ)
  rw [source_a5_original_moved_normalizer_quotient_kernel D e] at hk
  apply le_antisymm
  · exact le_inf (commutatorPreimage_le _ _ _) (hk.trans inf_le_right)
  · apply le_commutatorPreimage inf_le_left
    exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le

end CFSG.Quasithin.Chapter10
