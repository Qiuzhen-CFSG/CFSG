module
public import Theory.GroupTheory.TwoKernelCyclicLift
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.CentralLift
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.LinearCovered
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Reflected cyclic subgroups in the original parabolic

Use the original source comparison K/O₂→K* through the distinct full core
J. Its kernel is odd and central in the normal case, and trivial in the
exchanged case. The marked Borel is exactly the preimage of the original
maximal subgroup. Lift the reflected model torus through this central layer
and then through the actual two-core. Coprime normalizer lifting gives an
escaping normalizer for every odd-primary subgroup of the same lifted torus.

The internal Structure import only identifies its original core definition
with the source normal core; no private theorem substitutes for the argument.
Source: Aschbacher–Smith E.2.2 and E.6.27, pp.215–216,257.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted
open ChapterB DiagramHall
variable {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]

omit [Finite X] in
theorem comparison_kernel_image_le (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X) :
    (linearSourceComparison S hP K).ker.map (actorImage K).subtype ≤
      (sourceKernel (minimalParabolicMax S hP)).map (QuotientGroup.mk' (pCore 2 X)) := by
  rintro x ⟨a,ha,rfl⟩
  have he := congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
  change QuotientGroup.map (pCore 2 X) (sourceKernel (minimalParabolicMax S hP))
    (MonoidHom.id X) (twoCore_le_sourceKernel S hP) a = 1 at he
  obtain ⟨k,hk,hka⟩ := a.property
  refine ⟨k,?_,hka⟩
  apply (QuotientGroup.eq_one_iff _).mp
  rw [← hka] at he
  exact he

theorem comparison_kernel_odd (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X) :
    Odd (Nat.card (linearSourceComparison S hP K).ker) := by
  have hdiv := card_dvd_of_le (comparison_kernel_image_le S hP K)
  rw [card_map_of_injective (actorImage K).subtype_injective] at hdiv
  exact (minimalParabolic_coreImage_odd S hP).of_dvd_nat hdiv

omit [Finite X] [Finite Y] in
theorem comparison_borel_preimage (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Y) (B : Subgroup Y)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom = B) :
    B.comap (e.toMonoidHom.comp (linearSourceComparison S hP K)) =
      ((minimalParabolicMax S hP).map (QuotientGroup.mk' (pCore 2 X))).subgroupOf (actorImage K) := by
  ext x
  obtain ⟨k,hk,hkx⟩ := x.property
  have hx : (⟨QuotientGroup.mk' (pCore 2 X) k,k,hk,rfl⟩ : actorImage K) = x := Subtype.ext hkx
  rw [← hx]
  change e (linearSourceComparison S hP K ⟨QuotientGroup.mk' (pCore 2 X) k,k,hk,rfl⟩) ∈ B ↔
    QuotientGroup.mk' (pCore 2 X) k ∈ (minimalParabolicMax S hP).map (QuotientGroup.mk' (pCore 2 X))
  rw [← he,mem_map_equiv,e.symm_apply_apply]
  change QuotientGroup.mk' (sourceKernel (minimalParabolicMax S hP)) k ∈
      (minimalParabolicMax S hP ⊓ K).map (QuotientGroup.mk' (sourceKernel (minimalParabolicMax S hP))) ↔ _
  constructor
  · rintro ⟨m,hm,hmk⟩
    have hd := QuotientGroup.eq_iff_div_mem.mp hmk
    have hdM := (minimalParabolicMax S hP).normalCore_le hd
    have hkm := (minimalParabolicMax S hP).mul_mem
      ((minimalParabolicMax S hP).inv_mem hdM) hm.1
    have hkM : k ∈ minimalParabolicMax S hP := by
      simpa only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hkm
    exact mem_map_of_mem _ hkM
  · rintro ⟨m,hm,hmk⟩
    have hd := QuotientGroup.eq_iff_div_mem.mp hmk
    have hdM := ((twoCore_le_sourceKernel S hP).trans (minimalParabolicMax S hP).normalCore_le) hd
    have hkm := (minimalParabolicMax S hP).mul_mem
      ((minimalParabolicMax S hP).inv_mem hdM) hm
    have hkM : k ∈ minimalParabolicMax S hP := by
      simpa only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hkm
    exact ⟨k,⟨hkM,hk⟩,rfl⟩

omit [Finite Y] in
/-- The genuine source marking lifts an inverted model torus, preserving
its exact order and escaping normalizers of every odd-primary subgroup. -/
theorem source_cyclic_normalizer_escape_of_reflection
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hc : SingleClauses (minimalParabolicMax S hP) K S ∨
      ExchangedClauses (minimalParabolicMax S hP) K S)
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Y) (B : Subgroup Y)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom = B)
    (C : Subgroup Y) [IsCyclic C] (ho : Odd (Nat.card C)) (hCB : C ≤ B)
    (w : Y) (hout : w ∉ B) (hw : ∀ c ∈ C, w*c*w⁻¹=c⁻¹) :
    ∃ D : Subgroup X, D ≤ minimalParabolicMax S hP ∧ IsCyclic D ∧ Nat.card D=Nat.card C ∧
      ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup X), Odd p → A ≤ D → IsPGroup p A →
        ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP := by
  let M := minimalParabolicMax S hP
  let q := QuotientGroup.mk' (pCore 2 X)
  let L := actorImage K
  let r := e.toMonoidHom.comp (linearSourceComparison S hP K)
  have hr : Function.Surjective r := e.surjective.comp (linearSourceComparison_surjective S hP K)
  have hk : r.ker = (linearSourceComparison S hP K).ker :=
    MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective
  have hcent0 : (linearSourceComparison S hP K).ker ≤ center L := by
    rcases hc with hc|hc
    · exact linearSourceComparison_central S hP K hc
    · intro x hx
      have hxJ := comparison_kernel_image_le S hP K (mem_map_of_mem (actorImage K).subtype hx)
      obtain ⟨k,hk,hkx⟩ := hxJ
      have hx1 : (x : X ⧸ pCore 2 X) = 1 := by
        change (actorImage K).subtype x = 1
        rw [← hkx]
        exact (QuotientGroup.eq_one_iff _).mpr (hc.kernel_eq ▸ hk)
      have hxone : x = 1 := Subtype.ext hx1
      exact hxone ▸ (center L).one_mem
  have hcent : r.ker ≤ center L := hk ▸ hcent0
  have hodd : Odd (Nat.card r.ker) := hk ▸ comparison_kernel_odd S hP K
  obtain ⟨z,hz⟩ := hr w
  obtain ⟨D0,hD0,hcyc,hcard,hinv⟩ := cyclic_inverted_lift_of_central_odd_kernel r hr hcent hodd C z
    (by simpa only [hz] using hw)
  let Dq := D0.map L.subtype
  let : IsCyclic Dq := isCyclic_of_surjective _ (L.subtype.subgroupMap_surjective D0)
  have hDqcard : Nat.card Dq = Nat.card C := (card_map_of_injective L.subtype_injective).trans hcard
  have hDqM : Dq ≤ M.map q := by
    rintro _ ⟨a,ha,rfl⟩
    have hb : a ∈ B.comap r := hCB (hD0 ha)
    rw [comparison_borel_preimage S hP K e B he] at hb
    exact hb
  have hzM : (z : X ⧸ pCore 2 X) ∉ M.map q := by
    intro hzM
    have hzB : z ∈ B.comap r := by
      rw [comparison_borel_preimage S hP K e B he]
      exact hzM
    exact hout (hz ▸ hzB)
  have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  obtain ⟨D,hDc,hDm,hDcard⟩ := Theory.GroupTheory.exists_cyclic_lift_of_two_kernel q
    (QuotientGroup.mk'_surjective _) hq Dq (hDqcard.symm ▸ ho)
  have hDM : D ≤ M := by
    have hd := map_le_iff_le_comap.mp (hDm.symm ▸ hDqM)
    rwa [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr
      ((twoCore_le_sourceKernel S hP).trans M.normalCore_le)] at hd
  refine ⟨D,hDM,hDc,hDcard.trans hDqcard,?_⟩
  intro p hp A hop hAD hAp
  apply Theory.GroupTheory.normalizer_not_le_of_inverted_image q
    (QuotientGroup.mk'_surjective _) hq M A D hAD hop hAp z
  · intro x hx
    rw [hDm] at hx
    obtain ⟨a,ha,rfl⟩ := hx
    exact congrArg Subtype.val (hinv a ha)
  · exact hzM

omit [Finite Y] in
theorem source_cyclic_normalizer_escape_of_torus
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hc : SingleClauses (minimalParabolicMax S hP) K S ∨
      ExchangedClauses (minimalParabolicMax S hP) K S)
    (B : Subgroup Y) (he : ModelBorelPair (minimalParabolicMax S hP) K B)
    {C : Type*} [Group C] [IsCyclic C] (i : C →* B) (hi : Function.Injective i)
    (ho : Odd (Nat.card C)) (w : Y) (hout : w ∉ B)
    (hw : ∀ c, w*(i c : Y)*w⁻¹=(i c : Y)⁻¹) :
    ∃ D : Subgroup X, D ≤ minimalParabolicMax S hP ∧ IsCyclic D ∧ Nat.card D=Nat.card C ∧
      ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup X), Odd p → A ≤ D → IsPGroup p A →
        ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP := by
  obtain ⟨e,he⟩ := he
  let t := B.subtype.comp i
  have ht : Function.Injective t := B.subtype_injective.comp hi
  have hcard : Nat.card t.range = Nat.card C := (Nat.card_congr (MonoidHom.ofInjective ht).toEquiv).symm
  let : IsCyclic t.range := isCyclic_of_surjective t.rangeRestrict t.rangeRestrict_surjective
  have hle : t.range ≤ B := by rintro _ ⟨a,rfl⟩; exact (i a).property
  obtain ⟨D,hD,hcyc,hDc,hN⟩ := source_cyclic_normalizer_escape_of_reflection S hP K hc
    e B he t.range (hcard.symm ▸ ho) hle w hout (by rintro _ ⟨a,rfl⟩; exact hw a)
  exact ⟨D,hD,hcyc,hDc.trans hcard,hN⟩

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted
