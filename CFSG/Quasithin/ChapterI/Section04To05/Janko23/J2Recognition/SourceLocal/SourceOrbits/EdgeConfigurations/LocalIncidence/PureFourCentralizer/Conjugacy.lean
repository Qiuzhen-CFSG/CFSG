module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.LocalIncidence.RootReduction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.ReturningPair
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.LocalFusion

/-!
# Conjugacy and full centralizers of the pure four-groups

Core fusion puts a pure four-group containing z in Q. The transitivity of H
on the noncentral involutions of Q then conjugates it to the marked E from
a returning pair. An arbitrary pure four-group first acquires z by conjugation.
The full centralizer of that marked E normalizes both factors of the literal
root product R, so it lies in N_G(R). No root-normalizer recognition is used.

Source: Aschbacher, *Sporadic Groups* (1994), 46.1–46.3, 46.14(5)(b)
and the use of C_G(E) in 47.6(1), printed pp.251,257–258,264.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations.PureFourCentralizer
open InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

private theorem not_mem_line {t : G} (ht : orderOf t = 2) (hne : t ≠ D.z) :
    t ∉ zpowers D.z := by
  intro hm
  exact hne (congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨t, hm⟩ : zpowers D.z)) (y := (⟨D.z, mem_zpowers D.z⟩ : zpowers D.z))
    ((orderOf_coe _).symm.trans ht)
    ((orderOf_coe _).symm.trans D.localType.involution)))

private theorem noncentral_local {t : localCore D.z}
    (ht : ((t : involutionCentralizer D.z) : G) ∉ zpowers D.z) :
    t ∉ center (localCore D.z) := by
  intro hc
  let e : localCore D.z ≃* ambientCore D.z :=
    (localCore D.z).equivMapOfInjective _ (involutionCentralizer D.z).subtype_injective
  have he := (centerCongr e ⟨t, hc⟩).property
  exact ht (D.localType.core_center_image ▸ mem_map_of_mem (ambientCore D.z).subtype he)

/-- Pure four-groups through z lie in its literal ambient core. -/
theorem le_core_of_z_mem (E : Subgroup G) [IsKleinFour E]
    (hpure : ∀ t ∈ E, t ≠ 1 → IsConj D.z t) (hz : D.z ∈ E) :
    E ≤ ambientCore D.z := by
  intro t ht
  by_cases h1 : t = 1
  · simp [h1]
  have h2 : orderOf t = 2 := orderOf_eq_prime
    (by simpa [pow_two] using (congrArg Subtype.val
      (IsKleinFour.mul_self (⟨t, ht⟩ : E)))) h1
  have hH : t ∈ involutionCentralizer D.z := by
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := E)).is_comm.comm ⟨t, ht⟩ ⟨D.z, hz⟩)
  exact (InvolutionGeometry.core_fusion D hH h2).mp (hpure t ht h1)

/-- H conjugates every pure four-group through z to the chosen source E. -/
theorem conjugate_of_z_mem (P : ReturningPair D) (E : Subgroup G) [IsKleinFour E]
    (hpure : ∀ t ∈ E, t ≠ 1 → IsConj D.z t) (hz : D.z ∈ E) :
    ∃ h : involutionCentralizer D.z,
      E.map (MulAut.conj (h : G)).toMonoidHom = P.E := by
  have hnot : ¬ E ≤ zpowers D.z := by
    intro hle
    have hc := card_le_of_le hle
    rw [IsKleinFour.card_four, Nat.card_zpowers, D.localType.involution] at hc
    omega
  obtain ⟨u, hu, huline⟩ := SetLike.not_le_iff_exists.mp hnot
  have h1 : u ≠ 1 := fun h => huline (h ▸ (zpowers D.z).one_mem)
  have h2 : orderOf u = 2 := orderOf_eq_prime
    (by simpa [pow_two] using (congrArg Subtype.val
      (IsKleinFour.mul_self (⟨u, hu⟩ : E)))) h1
  obtain ⟨uH, huQ, rfl⟩ := le_core_of_z_mem E hpure hz hu
  obtain ⟨vH, hvQ, hv⟩ := P.mem_core
  let uQ : localCore D.z := ⟨uH, huQ⟩
  let vQ : localCore D.z := ⟨vH, hvQ⟩
  change (vH : G) = P.u at hv
  change orderOf (uH : G) = 2 at h2
  have hv2 : orderOf (vH : G) = 2 := by rw [hv]; exact P.u_order
  have hconj := D.localType.core_noncentral_involutions_isConj uQ vQ
    ((orderOf_coe uQ).symm.trans ((orderOf_coe uH).symm.trans h2)) (noncentral_local huline)
    ((orderOf_coe vQ).symm.trans ((orderOf_coe vH).symm.trans hv2))
    (noncentral_local (by
      change (vH : G) ∉ zpowers D.z
      rw [hv]
      exact not_mem_line P.u_order P.ne))
  obtain ⟨h, hh⟩ := isConj_iff.mp hconj
  refine ⟨h, (eq_of_le_of_card_ge ?_ ?_).symm⟩
  · apply sup_le
    · apply zpowers_le.mpr
      have hf : (MulAut.conj (h : G)) D.z = D.z :=
        mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp h.property)
      exact mem_map.mpr ⟨D.z, hz, hf⟩
    · apply zpowers_le.mpr
      have hf : (MulAut.conj (h : G)) (uH : G) = P.u :=
        (congrArg Subtype.val hh).trans hv
      exact mem_map.mpr ⟨uH, hu, hf⟩
  · rw [card_map_of_injective (MulAut.conj (h : G)).injective,
      IsKleinFour.card_four, P.E_card]

/-- All pure z-class four-groups are conjugate to one marked returning pair. -/
theorem conjugate (P : ReturningPair D) (E : Subgroup G) [IsKleinFour E]
    (hpure : ∀ t ∈ E, t ≠ 1 → IsConj D.z t) :
    ∃ g : G, E.map (MulAut.conj g).toMonoidHom = P.E := by
  classical
  have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [IsKleinFour.card_four]; decide)
  obtain ⟨t, ht⟩ := exists_ne (1 : E)
  have ht1 : (t : G) ≠ 1 := fun h => ht (Subtype.ext h)
  obtain ⟨a, ha⟩ := isConj_iff.mp (hpure t t.property ht1).symm
  let f := MulAut.conj a
  let E' := E.map f.toMonoidHom
  let e : E ≃* E' := f.subgroupMap E
  let : IsKleinFour E' := {
    card_four := (Nat.card_congr e.symm.toEquiv).trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e.symm).trans IsKleinFour.exponent_two }
  have hp' : ∀ t ∈ E', t ≠ 1 → IsConj D.z t := by
    rintro _ ⟨s, hs, rfl⟩ hne
    have hs1 : s ≠ 1 := fun h => hne (by simp [h])
    exact (hpure s hs hs1).trans (isConj_iff.mpr ⟨a, rfl⟩)
  have hz' : D.z ∈ E' := ha ▸ mem_map_of_mem f.toMonoidHom t.property
  obtain ⟨h, hh⟩ := conjugate_of_z_mem P E' hp' hz'
  refine ⟨(h : G) * a, ?_⟩
  have hf : (MulAut.conj ((h : G) * a)).toMonoidHom =
      (MulAut.conj (h : G)).toMonoidHom.comp f.toMonoidHom := by
    ext x
    simp [f, MulAut.conj_apply, mul_assoc]
  rw [hf, ← map_map]
  exact hh

/-- The literal full centralizer normalizes both factors in R. -/
theorem centralizer_le_normalizer (P : ReturningPair D) :
    centralizer (P.E : Set G) ≤ normalizer (P.R : Set G) := by
  have hH : centralizer (P.E : Set G) ≤ involutionCentralizer D.z := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hx D.z P.z_mem_E).symm
  have hU : centralizer (P.E : Set G) ≤ involutionCentralizer P.u := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hx P.u P.u_mem_E).symm
  have hQ : centralizer (P.E : Set G) ≤ normalizer (ambientCore D.z : Set G) := by
    rw [D.localType.normalizer_core]
    exact hH
  have hQg : centralizer (P.E : Set G) ≤ normalizer (P.conjugateCore : Set G) := by
    rw [P.normalizer_conjugateCore]
    exact hU
  exact (le_inf
    ((le_inf hQ (hU.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf)
    ((le_inf hQg (hH.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf)).trans
      (normalizer_inf_normalizer_le_normalizer_sup P.leftCore P.rightCore)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations.PureFourCentralizer
