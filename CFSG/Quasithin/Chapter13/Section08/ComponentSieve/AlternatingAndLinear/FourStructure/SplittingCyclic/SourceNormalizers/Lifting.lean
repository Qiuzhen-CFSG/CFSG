module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.GroupTheory.IsPerfect

/-!
# Lifting derived line stabilizers through the actual central section

Fixation of the image of A does not imply fixation of A: its commutators
with lifted actors can lie nontrivially in V₁. The section's actual kernel
and equivariance show precisely that containment. Since H centralizes V₁,
the three-subgroup lemma makes the derived lifted stabilizer centralize A.
Surjectivity of H → H/O₂(H) then transports ambient actor normality to the
derived quotient stabilizer. For a perfect stabilizer this is the whole
stabilizer.

In the source application UH = Source.UH H V₃, Z = V₁, A = A₁ and Vg = Vγ.
The ambient normalizer inclusion is the genuine earlier conclusion from
H = G₁, not a premise about fixation in the quotient. Only A ≤ UH is needed
for the lifting, and neither A nor Vγ is required to be normal in G.

Source: Aschbacher–Smith 13.8.25, printed pp.961–962 (PDF pp.978–979).
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers
open CriticalTransfer Representation.BinaryOffender
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}
  (s : ConjugationSection H UH Z ρ)

/-- Derived lifts centralize A exactly, despite the possible nontrivial central error. -/
theorem commutator_preimage_centralizes
    (A : Subgroup G) (hAU : A ≤ UH) (P : Subgroup (Source.Hstar H))
    (hfix : ∀ k ∈ P, ∀ v ∈ s.image A, ρ k v = v) :
    ⁅P.comap (QuotientGroup.mk' (pCore 2 H)), P.comap (QuotientGroup.mk' (pCore 2 H))⁆ ≤
      centralizer (A.subgroupOf H : Set H) := by
  let R := P.comap (QuotientGroup.mk' (pCore 2 H))
  have hc : ⁅R, A.subgroupOf H⁆ ≤ Z.subgroupOf H := by
    apply commutator_le.mpr
    intro r hr a ha
    let u : UH := ⟨a, hAU ha⟩
    have hu : (s.quotient u).toAdd ∈ s.image A := ⟨u, ha, rfl⟩
    have hd := s.displacement r u
    rw [hfix _ hr _ hu, sub_self] at hd
    exact (s.quotient_eq_zero_iff _).mp hd.symm
  have hz : ⁅Z.subgroupOf H, R⁆ = ⊥ := by
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro r _
    rw [mem_centralizer_iff]
    intro z hz
    exact Subtype.ext (mem_centralizer_iff.mp (s.centralizes r.property) z hz)
  have hr : ⁅⁅R, A.subgroupOf H⁆, R⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono hc le_rfl).trans hz.le)
  exact commutator_eq_bot_iff_le_centralizer.mp
    (commutator_commutator_eq_bot_of_rotate hr (by rwa [commutator_comm (A.subgroupOf H) R]))

/-- Ambient normality gives normalization by the derived quotient-line stabilizer. -/
theorem derived_normalizes_starImage
    (A Vg : Subgroup G) (hAU : A ≤ UH)
    (hn : normalizer (A : Set G) ≤ normalizer (Vg : Set G))
    (P : Subgroup (Source.Hstar H))
    (hfix : ∀ k ∈ P, ∀ v ∈ s.image A, ρ k v = v) :
    ⁅P, P⁆ ≤ normalizer (Source.starImage H Vg : Set (Source.Hstar H)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let R := P.comap q
  have hmap : R.map q = P := Subgroup.map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]; exact le_top)
  have hnR : ⁅R,R⁆ ≤ normalizer (Vg.subgroupOf H : Set H) := by
    intro r hr
    have hc := commutator_preimage_centralizes s A hAU P hfix hr
    have ha : (r : G) ∈ centralizer (A : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      exact congrArg Subtype.val (mem_centralizer_iff.mp hc ⟨a, s.le (hAU ha)⟩ ha)
    apply Subgroup.le_normalizer_comap H.subtype
    exact hn (centralizer_le_normalizer _ ha)
  rw [← hmap, ← map_commutator]
  exact (Subgroup.map_mono hnR).trans (Subgroup.le_normalizer_map q)

/-- For a perfect quotient-line stabilizer, the lifting error disappears entirely. -/
theorem perfect_normalizes_starImage
    (A Vg : Subgroup G) (hAU : A ≤ UH)
    (hn : normalizer (A : Set G) ≤ normalizer (Vg : Set G))
    (P : Subgroup (Source.Hstar H)) [Group.IsPerfect P]
    (hfix : ∀ k ∈ P, ∀ v ∈ s.image A, ρ k v = v) :
    P ≤ normalizer (Source.starImage H Vg : Set (Source.Hstar H)) := by
  simpa only [Subgroup.commutator_eq_self] using derived_normalizes_starImage s A Vg hAU hn P hfix

/-- The same lifting after the specified γ-to-α conjugation; both the line and actor are transported. -/
theorem derived_normalizes_conjugate_starImage
    (A Vg : Subgroup G) (hAU : A ≤ UH)
    (hn : normalizer (A : Set G) ≤ normalizer (Vg : Set G))
    (g : Source.Hstar H) (P : Subgroup (Source.Hstar H))
    (hfix : ∀ k ∈ P, ∀ v ∈ (s.image A).map (ρ g), ρ k v = v) :
    ⁅P, P⁆ ≤ normalizer ((Source.starImage H Vg).map (MulAut.conj g).toMonoidHom :
      Set (Source.Hstar H)) := by
  let R := P.map (MulAut.conj g⁻¹).toMonoidHom
  have hrfix : ∀ k ∈ R, ∀ v ∈ s.image A, ρ k v = v := by
    rintro _ ⟨k, hk, rfl⟩ v hv
    have hh := hfix k hk (ρ g v) (Submodule.mem_map_of_mem hv)
    change ρ (g⁻¹ * k * (g⁻¹)⁻¹) v = v
    simp only [inv_inv, map_mul, Module.End.mul_apply]
    rw [hh]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  have hnR := derived_normalizes_starImage s A Vg hAU hn R hrfix
  have hm : R.map (MulAut.conj g).toMonoidHom = P := by
    rw [Subgroup.map_map]
    have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp
    rw [he, Subgroup.map_id]
  rw [← hm, ← Subgroup.map_commutator]
  exact (Subgroup.map_mono hnR).trans (Subgroup.le_normalizer_map _)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers
