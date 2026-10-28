module
public import Theory.GroupTheory.Fitting.Core
public import Theory.PGroup
public import Mathlib.GroupTheory.Frattini
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
/-!
# Frattini products and inversion on the Fitting quotient

Frattini subgroups commute with finite products of finite nilpotent groups,
including products involving different primes. More generally, a homomorphism
into a finite nilpotent group preserves Frattini elements: each maximal subgroup
of the target is normal, and the composite into its quotient has either trivial
image or a maximal kernel. The same maximal quotients show that the nilpotent
Frattini quotient is abelian.

For a finite group `K`, the canonical inclusions `Oₚ(K) → F(K)` therefore induce
maps on Frattini quotients. These maps intertwine the actual characteristic
restrictions of every automorphism of `K`, and their images generate the full
Fitting quotient. Consequently primewise inversion implies inversion on
`F(K)/Φ(F(K))`. Empty prime support and arbitrary prime-power exponents are
included.

This is the mixed-prime assembly underlying Aschbacher–Smith, combined
manuscript of 1 March 2004, the first paragraph of the proof of 13.1.9, printed
p.869, with the nilpotent structure of A.3.6, printed pp.43–45. The identification
of the relevant ambient element and the primewise action facts are separate
inputs to the source-theorem assembly.
-/

@[expose] public section
open Subgroup

private theorem frattini_le_kernel_of_nilpotent_coatom
    {F : Type*} [Group F] [Finite F] [Group.IsNilpotent F]
    {P : Type*} [Group P] (ι : P →* F) (M : Subgroup F)
    (hM : IsCoatom M) :
    frattini P ≤ Subgroup.comap ι M := by
  let : M.Normal := Subgroup.NormalizerCondition.normal_of_coatom M
    (Group.normalizerCondition_of_isNilpotent (G := F)) hM
  let Q := F ⧸ M
  let : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hM.1
  let qP : P →* Q := (QuotientGroup.mk' M).comp ι
  have hbot : IsCoatom (⊥ : Subgroup Q) := by
    refine ⟨bot_ne_top, fun H hH => ?_⟩
    exact (quotient_subgroup_eq_bot_or_top_of_coatom hM H).resolve_left hH.ne'
  rcases quotient_subgroup_eq_bot_or_top_of_coatom hM qP.range with hb | ht
  · intro x _
    apply (QuotientGroup.eq_one_iff (N := M) (ι x)).mp
    have hx : qP x ∈ qP.range := ⟨x, rfl⟩
    have hx1 : qP x = 1 := by simpa only [hb, Subgroup.mem_bot] using hx
    exact hx1
  · have hc := Subgroup.isCoatom_comap_of_surjective
      (MonoidHom.range_eq_top.mp ht) hbot
    intro x hx
    exact (QuotientGroup.eq_one_iff (N := M) (ι x)).mp (frattini_le_coatom hc hx)

/-- Homomorphisms into a finite nilpotent group preserve Frattini elements. -/
theorem frattini_map_le_of_nilpotent
    {G H : Type*} [Group G] [Group H] [Finite H] [Group.IsNilpotent H]
    (f : G →* H) : (frattini G).map f ≤ frattini H := by
  rw [Subgroup.map_le_iff_le_comap]
  simp only [frattini, Order.radical, Subgroup.comap_iInf, le_iInf_iff]
  intro M hM
  exact frattini_le_kernel_of_nilpotent_coatom f M hM

/-- Frattini quotients of finite nilpotent groups are commutative. -/
theorem commutator_le_frattini_of_nilpotent
    {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G] :
    _root_.commutator G ≤ frattini G := by
  simp only [frattini, Order.radical, le_iInf_iff]
  intro M hM
  let : M.Normal := Subgroup.NormalizerCondition.normal_of_coatom M
    (Group.normalizerCondition_of_isNilpotent (G := G)) hM
  let Q := G ⧸ M
  let : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hM.1
  let : IsSimpleGroup Q := {
    eq_bot_or_eq_top_of_normal := fun H _ =>
      quotient_subgroup_eq_bot_or_top_of_coatom hM H
  }
  let : CommGroup Q := inferInstance
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := M)).mp inferInstance


namespace Subgroup
/-- Frattini subgroups of finite nilpotent groups commute with binary products,
without requiring the factors to be groups for the same prime. -/
theorem frattini_prod_of_nilpotent {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] [Group.IsNilpotent A] [Group.IsNilpotent B] :
    frattini (A × B) = (frattini A).prod (frattini B) := by
  apply le_antisymm
  · intro x hx
    exact ⟨frattini_map_le_of_nilpotent (MonoidHom.fst A B) (mem_map_of_mem _ hx),
      frattini_map_le_of_nilpotent (MonoidHom.snd A B) (mem_map_of_mem _ hx)⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    have ha' : (a, 1) ∈ frattini (A × B) :=
      frattini_map_le_of_nilpotent (MonoidHom.inl A B) (mem_map_of_mem _ ha)
    have hb' : (1, b) ∈ frattini (A × B) :=
      frattini_map_le_of_nilpotent (MonoidHom.inr A B) (mem_map_of_mem _ hb)
    simpa only [Prod.mul_def, mul_one, one_mul] using (frattini (A × B)).mul_mem ha' hb'

/-- Frattini subgroups commute with arbitrary finite products of finite nilpotent groups. -/
theorem frattini_pi_of_nilpotent {ι : Type*} [Finite ι] (G : ι → Type*)
    [∀ i, Group (G i)] [∀ i, Finite (G i)] [∀ i, Group.IsNilpotent (G i)] :
    frattini (∀ i, G i) = Subgroup.pi Set.univ (fun i => frattini (G i)) := by
  classical
  apply le_antisymm
  · intro x hx i _
    exact frattini_map_le_of_nilpotent (Pi.evalMonoidHom G i) (mem_map_of_mem _ hx)
  · apply pi_le_iff.mpr
    intro i
    exact frattini_map_le_of_nilpotent (MonoidHom.mulSingle G i)
end Subgroup

namespace FittingFrattini
variable (K : Type*) [Group K] [Finite K]

/-- The canonical inclusion of the prime core in the Fitting subgroup. -/
def coreInclusion (p : ℕ) [Fact p.Prime] : pCore p K →* fittingSubgroup K :=
  Subgroup.inclusion (pCore_le_fitting K p)

/-- The actual inclusions carry core Frattini subgroups into the Fitting Frattini subgroup. -/
theorem core_frattini_le (p : ℕ) [Fact p.Prime] :
    (frattini (pCore p K)).map (coreInclusion K p) ≤ frattini (fittingSubgroup K) :=
  frattini_map_le_of_nilpotent _

/-- The quotient map induced by the canonical prime-core inclusion. -/
def coreQuotientMap (p : ℕ) [Fact p.Prime] :
    (pCore p K ⧸ frattini (pCore p K)) →*
      (fittingSubgroup K ⧸ frattini (fittingSubgroup K)) :=
  QuotientGroup.map _ _ (coreInclusion K p)
    (Subgroup.map_le_iff_le_comap.mp (core_frattini_le K p))

@[simp]
theorem coreQuotientMap_mk (p : ℕ) [Fact p.Prime] (x : pCore p K) :
    coreQuotientMap K p (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (coreInclusion K p x) := rfl

/-- These quotient maps intertwine the characteristic restrictions of every ambient automorphism. -/
theorem coreQuotientMap_equivariant (p : ℕ) [Fact p.Prime] (α : MulAut K)
    (z : pCore p K ⧸ frattini (pCore p K)) :
    coreQuotientMap K p
      (Subgroup.quotientAut _ (MulAut.characteristic (pCore p K) α) z) =
    Subgroup.quotientAut _ (MulAut.characteristic (fittingSubgroup K) α)
      (coreQuotientMap K p z) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
  rw [Subgroup.quotientAut_apply_mk, coreQuotientMap_mk,
    coreQuotientMap_mk, Subgroup.quotientAut_apply_mk]
  rfl

/-- The images of the canonical prime-core inclusions generate the Fitting subgroup. -/
theorem coreInclusions_generate :
    (⨆ p : (Nat.card K).primeFactors.attach, (coreInclusion K p.1.1).range) = ⊤ := by
  apply Subgroup.map_injective (fittingSubgroup K).subtype_injective
  rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  calc
    (⨆ p : (Nat.card K).primeFactors.attach,
        ((coreInclusion K p.1.1).range).map (fittingSubgroup K).subtype) =
      ⨆ p : (Nat.card K).primeFactors.attach, pCore p.1.1 K := by
        congr 1
        funext p
        rw [← MonoidHom.range_comp]
        exact Subgroup.range_subtype (pCore p.1.1 K)
    _ = fittingSubgroup K := (fitting_eq_sup_pCore K).symm

/-- The induced maps also generate the whole Fitting Frattini quotient. -/
theorem coreQuotientMaps_generate :
    (⨆ p : (Nat.card K).primeFactors.attach, (coreQuotientMap K p.1.1).range) = ⊤ := by
  let q := QuotientGroup.mk' (frattini (fittingSubgroup K))
  have hr (p : (Nat.card K).primeFactors.attach) :
      (coreQuotientMap K p.1.1).range = ((coreInclusion K p.1.1).range).map q := by
    rw [← MonoidHom.range_comp]
    have he : q.comp (coreInclusion K p.1.1) =
        (coreQuotientMap K p.1.1).comp (QuotientGroup.mk' _) := by ext x; rfl
    rw [he, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
      ← MonoidHom.range_eq_map]
  simp_rw [hr]
  rw [← Subgroup.map_iSup, coreInclusions_generate]
  exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)

open scoped IsMulCommutative
/-- Primewise inversion assembles on the actual mixed-prime Fitting Frattini quotient. -/
theorem quotientAut_inverts (α : MulAut K)
    (h : ∀ (p : ℕ) [Fact p.Prime], p ∣ Nat.card (fittingSubgroup K) →
      ∀ z : pCore p K ⧸ frattini (pCore p K),
        Subgroup.quotientAut _ (MulAut.characteristic (pCore p K) α) z = z⁻¹)
    (z : fittingSubgroup K ⧸ frattini (fittingSubgroup K)) :
    Subgroup.quotientAut _ (MulAut.characteristic (fittingSubgroup K) α) z = z⁻¹ := by
  let : IsMulCommutative (fittingSubgroup K ⧸ frattini (fittingSubgroup K)) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := frattini (fittingSubgroup K))).mpr
      commutator_le_frattini_of_nilpotent
  let β := Subgroup.quotientAut (frattini (fittingSubgroup K))
    (MulAut.characteristic (fittingSubgroup K) α)
  let D := β.toMonoidHom.eqLocus (MulEquiv.inv _).toMonoidHom
  have hD : (⊤ : Subgroup (fittingSubgroup K ⧸ frattini (fittingSubgroup K))) ≤ D := by
    rw [← coreQuotientMaps_generate K]
    apply iSup_le
    intro p
    rintro _ ⟨x, rfl⟩
    change β (coreQuotientMap K p.1.1 x) = (coreQuotientMap K p.1.1 x)⁻¹
    rw [← coreQuotientMap_equivariant]
    by_cases hd : p.1.1 ∣ Nat.card (fittingSubgroup K)
    · rw [h p.1.1 hd, map_inv]
    · have hc : Nat.card (pCore p.1.1 K) = 1 :=
        (pCore_isPGroup (p := p.1.1) (G := K)).card_eq_or_dvd.resolve_right
          (fun hp => hd (hp.trans (Subgroup.card_dvd_of_le (pCore_le_fitting K p.1.1))))
      have : Subsingleton (pCore p.1.1 K) := (Nat.card_eq_one_iff_unique.mp hc).1
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
      have hy : y = 1 := Subsingleton.elim _ _
      simp [hy]
  exact hD (Subgroup.mem_top z)

end FittingFrattini
