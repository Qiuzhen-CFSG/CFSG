module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.CoreDihedral

/-!
# The displacement index of every moved paired-cubic core

Inside the original Sylow group, any element moving the core lies outside
its index-two subgroup. The core and its conjugate therefore generate the
actual Thompson subgroup. The core is self-centralizing there, so the
centralizer index in every moved conjugate is four. This supplies the
literal inner-component movers used in the odd-field rows of 2.4.32.

Source: Aschbacher–Smith 2.4.27–32, printed pp.547–549.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
namespace SourcePairCoordinates
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} (c : SourcePairCoordinates d T)

include c in
 theorem core_self_centralizing : sourceR d ⊓ centralizer (twoCore d.H : Set G) = twoCore d.H := by
  have hUR : c.U₁ ⊔ c.U₂ ≤ sourceR d :=
    sup_le (c.baumann ▸ c.first.module_le) (c.baumann ▸ c.second.module_le)
  have hQR : twoCore d.H ≤ sourceR d := by
    rw [c.product.1]
    exact sup_le hUR (c.product.2.1 ▸ le_sup_right)
  have hRS : sourceR d ≤ (d.S : Subgroup d.H).map d.H.subtype := sSup_le (fun _ h => h.1)
  have hUQ : c.U₁ ⊔ c.U₂ ≤ twoCore d.H := c.product.1 ▸ le_sup_left
  have hupper : sourceR d ⊓ centralizer (twoCore d.H : Set G) ≤ twoCore d.H := by
    apply (le_inf (inf_le_left.trans hRS) (inf_le_right.trans (centralizer_le hUQ))).trans
    exact c.core.le
  let : IsElementaryAbelian 2 c.U₁ := c.first.elementary
  let : IsElementaryAbelian 2 c.U₂ := c.second.elementary
  let : IsElementaryAbelian 2 c.D := c.product.2.2.2
  have hUC : c.U₂ ≤ centralizer (c.U₁ : Set G) :=
    (map_subtype_le _).trans (c.commute.trans (centralizer_le (map_subtype_le _)))
  let : IsElementaryAbelian 2 (c.U₁ ⊔ c.U₂ : Subgroup G) := IsElementaryAbelian.sup_of_le_centralizer hUC
  have hQD : IsElementaryAbelian 2 ((c.U₁ ⊔ c.U₂) ⊔ c.D : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (c.product.2.2.1.trans (centralizer_le hUR))
  let : IsElementaryAbelian 2 (twoCore d.H) := c.product.1.symm ▸ hQD
  exact le_antisymm hupper (le_inf hQR (le_centralizer _))

include c in
 theorem moved_core_centralizer_index
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block) (y : G) (hy : y ∈ (T : Subgroup G))
    (hmove : (twoCore d.H).map (MulAut.conj y⁻¹).toMonoidHom ≠ twoCore d.H) :
    (((twoCore d.H).map (MulAut.conj y⁻¹).toMonoidHom) ⊓
      centralizer (twoCore d.H : Set G)).relIndex
      ((twoCore d.H).map (MulAut.conj y⁻¹).toMonoidHom) = 4 := by
  let Q := twoCore d.H
  let V := Q.map (MulAut.conj y⁻¹).toMonoidHom
  have hnQ : d.H ≤ normalizer (Q : Set G) := le_normalizer_twoCore d.H
  have hyS : y ∉ (d.S : Subgroup d.H).map d.H.subtype := by
    intro hyS
    exact hmove (mem_normalizer_iff_map_conj_eq.mp
      (hnQ ((map_subtype_le _) (((d.S : Subgroup d.H).map d.H.subtype).inv_mem hyS))))
  have hg := d.paired_cubic_source_sylow_geometry hG T hM hTM hu hST hpair c.cubic_first
  have hspan : sourceR d = Q ⊔ V := hg.2.2.2.2.2.2.2.2 y hy hyS
  have hQR : Q ≤ sourceR d := hspan ▸ le_sup_left
  have hVR : V ≤ sourceR d := hspan ▸ le_sup_right
  have hRH : sourceR d ≤ d.H := (sSup_le (fun _ h => h.1)).trans (map_subtype_le _)
  have hVC : V ⊓ centralizer (Q : Set G) = Q ⊓ V := by
    apply le_antisymm
    · exact le_inf ((le_inf (inf_le_left.trans hVR) inf_le_right).trans c.core_self_centralizing.le) inf_le_left
    · have hQC : Q ≤ centralizer (Q : Set G) := c.core_self_centralizing.ge.trans inf_le_right
      exact le_inf inf_le_right (inf_le_left.trans hQC)
  have hcardV : Nat.card V = Nat.card Q := card_map_of_injective (MulAut.conj y⁻¹).injective
  have hmul := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q V (hVR.trans (hRH.trans hnQ))
  rw [←hspan,hcardV] at hmul
  have hRcard := relIndex_mul_relIndex (⊥ : Subgroup G) Q (sourceR d) bot_le hQR
  rw [relIndex_bot_left,relIndex_bot_left,c.core_index_thompson] at hRcard
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hIpos : 0 < Nat.card (Q ⊓ V : Subgroup G) := Nat.card_pos
  have hQI : Nat.card Q = 4 * Nat.card (Q ⊓ V : Subgroup G) := by nlinarith
  have hidx := relIndex_mul_relIndex (⊥ : Subgroup G) (Q ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,hcardV,hQI] at hidx
  change (V ⊓ centralizer (Q : Set G)).relIndex V = 4
  rw [hVC]
  nlinarith
end SourcePairCoordinates
end CFSG.Quasithin.Chapter2.DoubleA3
