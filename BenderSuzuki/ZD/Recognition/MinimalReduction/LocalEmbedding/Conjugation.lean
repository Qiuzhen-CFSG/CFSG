module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.CentralizerChoice
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.CosetIdentification
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Conjugate centralizer closures and the four-group obstruction

Conjugation carries the distinguished closure in one involution centralizer
onto that in a conjugate centralizer. Transporting the involution partition
of Lemma 4.7 therefore discharges both coset premises of the three-involution
argument in Lemma 4.8. The centralizer also normalizes the derived subgroup
of its distinguished closure, so its elements act on that subgroup.

Source: GLS, Volume 4, Chapter 2, (4F)--(4G) and Lemma 4.8.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1

/-- Conjugation transports the actual distinguished centralizer closure. -/
public theorem centralizerClosure_conj_mem
    {G : Type*} [Group G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (g u : G) {x : G}
    (hx : x ∈ centralizerClosure Z u) :
    MulAut.conj g x ∈ centralizerClosure Z (MulAut.conj g u) := by
  have hle : centralizerClosure Z u ≤
      (centralizerClosure Z (MulAut.conj g u)).comap (MulAut.conj g).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro z hz
    exact mem_centralizerClosure (h.invariant g z hz.1)
      ((show Commute z u from Subgroup.mem_centralizer_singleton_iff.mp hz.2).map
        (MulAut.conj g).toMonoidHom)
  exact hle hx

/-- The involution partition transfers to every conjugate centralizer. -/
public theorem centralizerClosure_partition_conj
    {G : Type*} [Group G] {Z : Set G} {M : Subgroup G} {u v : G}
    (h : IsProductDisconnected Z M) (huv : IsConj u v)
    (hpart : ∀ x ∈ centralizerClosure Z u, PFAppendixIII.IsInvolution x →
      x = u ∨ x ∈ Z ∨ ∃ a ∈ Z, ∃ b ∈ Z, x = a * b) :
    ∀ x ∈ centralizerClosure Z v, PFAppendixIII.IsInvolution x →
      x = v ∨ x ∈ Z ∨ ∃ a ∈ Z, ∃ b ∈ Z, x = a * b := by
  obtain ⟨g, hg⟩ := isConj_iff.mp huv
  have he : MulAut.conj g u = v := hg
  let e := MulAut.conj g
  have hei : MulAut.conj g⁻¹ v = u := by
    rw [← he]
    simp only [MulAut.conj_apply, inv_inv]
    group
  intro x hx hxi
  have hxL := centralizerClosure_conj_mem h g⁻¹ v hx
  rw [hei] at hxL
  have hxi' := BenderSuzuki.IsInvolution.map_of_injective hxi (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective
  have heix : e (MulAut.conj g⁻¹ x) = x := by
    simp only [e, MulAut.conj_apply, inv_inv]
    group
  rcases hpart _ hxL hxi' with hx' | hx' | ⟨a, ha, b, hb, hx'⟩
  · left
    exact heix.symm.trans ((congrArg e hx').trans he)
  · right; left
    exact heix ▸ h.invariant g _ hx'
  · right; right
    refine ⟨e a, h.invariant g a ha, e b, h.invariant g b hb, ?_⟩
    rw [← map_mul, ← hx', heix]

/-- A centralizer preserves the distinguished closure and its derived subgroup. -/
public theorem centralizer_le_local_derived_normalizer
    {G : Type*} [Group G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (u : G) :
    Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer (((commutator (centralizerClosure Z u)).map
        (centralizerClosure Z u).subtype : Subgroup G) : Set G) := by
  apply le_trans _ (Subgroup.normalizer_le_normalizer_characteristic_image
    (centralizerClosure Z u) (commutator (centralizerClosure Z u)))
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hgu : MulAut.conj g u = u := by
    change g * u * g⁻¹ = u
    rw [Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  have hgiu : MulAut.conj g⁻¹ u = u := by
    change g⁻¹ * u * (g⁻¹)⁻¹ = u
    rw [inv_inv, (show Commute g u from Subgroup.mem_centralizer_singleton_iff.mp hg).inv_left.eq,
      mul_assoc, inv_mul_cancel, mul_one]
  constructor
  · intro hx
    have hh := centralizerClosure_conj_mem h g u hx
    rwa [hgu] at hh
  · intro hx
    have hh := centralizerClosure_conj_mem h g⁻¹ u hx
    rw [hgiu] at hh
    simpa only [MulAut.conj_apply, inv_inv, inv_mul_cancel_left,
      mul_inv_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using hh

/-- GLS Lemma 4.8 with both involution-coset inputs discharged. -/
public theorem local_centralizer_not_twoRank_of_structure
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G} {u v : G}
    (h : IsProductDisconnected Z M) (hu : PFAppendixIII.IsInvolution u) (huM : u ∈ M)
    (hC : ¬ Subgroup.centralizer ({u} : Set G) ≤ M)
    (hne : ∃ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G) ∧ z ∈ M)
    (huL : u ∈ centralizerClosure Z u)
    (hs : StructureConclusion ((Subgroup.centralizer ({u} : Set G)).subtype ⁻¹' Z)
      (M.comap (Subgroup.centralizer ({u} : Set G)).subtype))
    (huv : u ≠ v) (hconj : IsConj u v) (hcomm : Commute u v) :
    ¬ TwoRankAtLeastTwo ↥(((commutator (centralizerClosure Z u)).map
      (centralizerClosure Z u).subtype) ⊓ Subgroup.centralizer ({v} : Set G)) := by
  obtain ⟨hcoset, hpart⟩ := LocalCosetIdentification.local_obstruction_inputs_of_structure
    h hu huM hC hne huL hs
  apply local_centralizer_not_twoRank h hu huM hC huv hcomm _ hcoset
    (centralizerClosure_partition_conj h hconj hpart)
  rintro x ⟨y, _, rfl⟩
  exact centralizerClosure_le Z u y.property

end BenderSuzuki.ZD
