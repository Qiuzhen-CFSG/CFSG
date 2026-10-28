module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.Elementary
public import Theory.SpecificGroups.Suzuki.StronglyEmbeddedBorel
public import Theory.SpecificGroups.Suzuki.BorelInvolutionCore
public import Theory.SpecificGroups.Suzuki.BorelPairGeometry

/-!
# The actual Suzuki Borel in a proper residual subgroup

For proper L, local strong embedding identifies M ∩ L with a Borel of the
actual Suzuki matrix model. The distinguished closure is the ambient image
of that Borel's involution core, hence is elementary abelian of order q.
The two-core of M ∩ L is its Sylow root group, distinct from the elementary
center. All identifications use the literal subgroup inclusions in G.

The same marking preserves the original outside involution t and identifies
D ∩ L with the literal intersection of the marked Borel and its right
conjugate by t. Transport of the intrinsic pair geometry gives the carrier
product, cyclic order q − 1, inversion and outside-involution conjugacy.
These are the Suzuki local calculations used in GLS, Volume 4, Chapter 2,
Lemma 12.2(b,d,f), from Chapter 4, Lemma 3.2(b–e,i). The ambient normalizer
and residual-commutator identifications belong to the source assembly.
Sources: `refs/KGroup/GLS4/Chapter2.tex`, lines 2007–2032, and
`refs/KGroup/GLS4/Chapter4.tex`, Lemma 3.2.
-/

noncomputable section
open BenderSuzuki Subgroup PFAppendixIII PFchapter1section1
open scoped Pointwise

namespace BenderSuzuki.ZD
open BenderSuzuki.MatrixGroups Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Identify the original local intersection with a concrete Suzuki Borel. -/
public theorem residualGenerated_suzuki_borel_marking
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {m : ℕ} (hm : 0 < m)
    (e : residualGenerated M z t ≃* SuzukiMatrixGroup m) :
    ∃ f : SuzukiMatrixGroup m ≃* residualGenerated M z t,
      (SuzukiBorelSubgroup m).map ((residualGenerated M z t).subtype.comp f.toMonoidHom) =
        M ⊓ residualGenerated M z t := by
  obtain ⟨f, hf⟩ := suzuki_stronglyEmbedded_eq_borel_map hm e (M.comap (residualGenerated M z t).subtype)
    (stronglyEmbedded_in_proper_residualGenerated h r hz hzM ht htM hL)
  refine ⟨f, ?_⟩
  rw [← map_map, hf]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property⟩
  · rintro ⟨hxM, hxL⟩
    exact ⟨⟨x, hxL⟩, hxM, rfl⟩

/-- The distinguished closure is elementary abelian of field order q. -/
public theorem residualGenerated_suzuki_distinguishedClosure
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    {m : ℕ} (hm : 0 < m) (e : residualGenerated M z t ≃* SuzukiMatrixGroup m) :
    IsElementaryAbelian 2 (closure (Z ∩ (M : Set G))) ∧
      Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ (2 * m + 1) := by
  obtain ⟨f, hf⟩ := residualGenerated_suzuki_borel_marking h r hz hzM ht htM hL hm e
  let φ := (residualGenerated M z t).subtype.comp f.toMonoidHom
  have hi : Function.Injective φ := Subtype.val_injective.comp f.injective
  have hcore := suzukiBorel_involutionCore_map hm φ hi _ hf
  rw [distinguishedClosure_eq_involutionCore_local h r hz hzM ht htM hL hAL] at hcore
  rw [hcore]
  let := suzukiRootSubgroup_omega_elementary m hm
  exact ⟨IsElementaryAbelian.map φ, by
    rw [card_map_of_injective hi, suzukiRootSubgroup_omega_card m hm]⟩

/-- The actual two-core of the local intersection is Sylow in that intersection. -/
public theorem residualGenerated_suzuki_pCore_isSylow
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {m : ℕ} (hm : 0 < m)
    (e : residualGenerated M z t ≃* SuzukiMatrixGroup m) :
    ∃ S : Sylow 2 (M ⊓ residualGenerated M z t : Subgroup G),
      (S : Subgroup (M ⊓ residualGenerated M z t : Subgroup G)) =
        pCore 2 (M ⊓ residualGenerated M z t : Subgroup G) := by
  obtain ⟨f, hf⟩ := residualGenerated_suzuki_borel_marking h r hz hzM ht htM hL hm e
  exact suzukiBorel_pCore_isSylow_of_map hm _ (Subtype.val_injective.comp f.injective) _ hf

private theorem map_rightConjugate {G H : Type*} [Group G] [Group H]
    (f : G →* H) (B : Subgroup G) (t : G) :
    (rightConjugate B t).map f = rightConjugate (B.map f) (f t) := by
  simp only [rightConjugate, Subgroup.conjBy, map_map]
  congr 1
  ext x
  simp

private theorem local_pair_map {G H : Type*} [Group G] [Group H]
    (f : H →* G) (hf : Function.Injective f) (C : Subgroup H)
    (M L : Subgroup G) (t : H) (htL : f t ∈ L) (hC : C.map f = M ⊓ L) :
    (C ⊓ rightConjugate C t).map f = residualPairStabilizer M (f t) ⊓ L := by
  rw [Subgroup.map_inf _ _ f hf, map_rightConjugate, hC]
  have hconj : rightConjugate (M ⊓ L) (f t) =
      rightConjugate M (f t) ⊓ rightConjugate L (f t) := by
    exact Subgroup.map_inf _ _ _ (MulAut.conj (f t)⁻¹).injective
  have hL : rightConjugate L (f t) = L := by
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer (L.inv_mem htL))
  rw [hconj, hL, residualPairStabilizer]
  exact inf_inf_inf_comm M L (rightConjugate M (f t)) L |>.trans (by rw [inf_idem])

/-- A single actual model marking identifies the local Borel, its two-core and
the specified pair stabilizer, and preserves the original outside involution. -/
public theorem residualGenerated_suzuki_pair_marking
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {m : ℕ} (hm : 0 < m)
    (e : residualGenerated M z t ≃* SuzukiMatrixGroup m) :
    ∃ (f : SuzukiMatrixGroup m ≃* residualGenerated M z t) (u : SuzukiMatrixGroup m),
      let φ := (residualGenerated M z t).subtype.comp f.toMonoidHom
      φ u = t ∧ PFAppendixIII.IsInvolution u ∧ u ∉ SuzukiBorelSubgroup m ∧
      (SuzukiBorelSubgroup m).map φ = M ⊓ residualGenerated M z t ∧
      (SuzukiRootSubgroup m).map φ =
        (pCore 2 (M ⊓ residualGenerated M z t : Subgroup G)).map
          (M ⊓ residualGenerated M z t).subtype ∧
      (SuzukiBorelSubgroup m ⊓ rightConjugate (SuzukiBorelSubgroup m) u).map φ =
        residualPairStabilizer M t ⊓ residualGenerated M z t := by
  let L := residualGenerated M z t
  obtain ⟨f, hf⟩ := residualGenerated_suzuki_borel_marking h r hz hzM ht htM hL hm e
  let φ := L.subtype.comp f.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp f.injective
  have htL : t ∈ L :=
    (show Subgroup.zpowers t ≤ L from le_sup_right.trans le_sup_left) (mem_zpowers t)
  let u := f.symm ⟨t, htL⟩
  have hu : φ u = t := congrArg Subtype.val (f.apply_symm_apply ⟨t, htL⟩)
  refine ⟨f, u, hu, ?_, ?_, hf, ?_, ?_⟩
  · exact BenderSuzuki.IsInvolution.map_of_injective
      (BenderSuzuki.IsInvolution.subtype (h.involutions t ht) htL) f.symm.toMonoidHom f.symm.injective
  · intro huB
    have hh : φ u ∈ M ⊓ L := hf ▸ mem_map_of_mem φ huB
    exact htM (hu ▸ hh.1)
  · exact (suzukiBorel_pCore_map hm φ hφ _ hf).symm
  · simpa only [hu] using local_pair_map φ hφ (SuzukiBorelSubgroup m) M L u
      (hu.symm ▸ htL) hf

/-- The actual local Borel is the carrier product of its two-core and pair stabilizer. -/
public theorem residualGenerated_suzuki_borel_product
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {m : ℕ} (hm : 0 < m)
    (e : residualGenerated M z t ≃* SuzukiMatrixGroup m) :
    ((M ⊓ residualGenerated M z t : Subgroup G) : Set G) =
      (((pCore 2 (M ⊓ residualGenerated M z t : Subgroup G)).map
        (M ⊓ residualGenerated M z t).subtype) : Set G) *
      ((residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) : Set G) := by
  obtain ⟨f, u, hft, hu, huB, hB, hU, hE⟩ :=
    residualGenerated_suzuki_pair_marking h r hz hzM ht htM hL hm e
  let φ := (residualGenerated M z t).subtype.comp f.toMonoidHom
  have himage := congrArg (Set.image φ) (suzukiBorel_pair_product m hm u hu huB)
  rw [Set.image_mul, ← Subgroup.coe_map, ← Subgroup.coe_map, ← Subgroup.coe_map,
    hB, hU, hE] at himage
  exact himage

/-- The actual local pair stabilizer is cyclic of order `q - 1`. -/
public theorem residualGenerated_suzuki_pair_cyclic_card
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {m : ℕ} (hm : 0 < m)
    (e : residualGenerated M z t ≃* SuzukiMatrixGroup m) :
    IsCyclic (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) ∧
      Nat.card (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) =
        2 ^ (2 * m + 1) - 1 := by
  obtain ⟨f, u, hft, hu, huB, hB, hU, hE⟩ :=
    residualGenerated_suzuki_pair_marking h r hz hzM ht htM hL hm e
  let φ := (residualGenerated M z t).subtype.comp f.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp f.injective
  rw [← hE]
  exact ⟨((SuzukiBorelSubgroup m ⊓ rightConjugate (SuzukiBorelSubgroup m) u).equivMapOfInjective φ hφ).isCyclic.mp (suzukiBorel_pair_isCyclic m hm u hu huB), by
    rw [card_map_of_injective hφ, suzukiBorel_pair_card m hm u hu huB]⟩

/-- The original involution inverts every element of the actual local pair stabilizer. -/
public theorem residualGenerated_suzuki_pair_inverted
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {m : ℕ} (hm : 0 < m)
    (e : residualGenerated M z t ≃* SuzukiMatrixGroup m)
    {d : G} (hd : d ∈ residualPairStabilizer M t ⊓ residualGenerated M z t) :
    rightConjugateElem d t = d⁻¹ := by
  obtain ⟨f, u, hft, hu, huB, hB, hU, hE⟩ :=
    residualGenerated_suzuki_pair_marking h r hz hzM ht htM hL hm e
  let φ := (residualGenerated M z t).subtype.comp f.toMonoidHom
  change φ u = t at hft
  rw [← hE] at hd
  obtain ⟨x, hx, rfl⟩ := hd
  have hi := congrArg φ (suzukiBorel_pair_inverted m hm u hu huB x hx)
  simpa only [rightConjugateElem, map_mul, map_inv, hft] using hi

/-- The actual local Borel conjugates the source involution to every involution
of the residual subgroup outside `M`. -/
public theorem residualGenerated_suzuki_outside_involutions_conjugate
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {m : ℕ} (hm : 0 < m)
    (e : residualGenerated M z t ≃* SuzukiMatrixGroup m)
    {v : G} (hvL : v ∈ residualGenerated M z t)
    (hv : PFAppendixIII.IsInvolution v) (hvM : v ∉ M) :
    ∃ b ∈ M ⊓ residualGenerated M z t, MulAut.conj b t = v := by
  obtain ⟨f, u, hft, hu, huB, hB, hU, hE⟩ :=
    residualGenerated_suzuki_pair_marking h r hz hzM ht htM hL hm e
  let φ := (residualGenerated M z t).subtype.comp f.toMonoidHom
  change φ u = t at hft
  let w := f.symm ⟨v, hvL⟩
  have hw : φ w = v := congrArg Subtype.val (f.apply_symm_apply ⟨v, hvL⟩)
  have hwI : PFAppendixIII.IsInvolution w :=
    BenderSuzuki.IsInvolution.map_of_injective (BenderSuzuki.IsInvolution.subtype hv hvL)
      f.symm.toMonoidHom f.symm.injective
  have hwB : w ∉ SuzukiBorelSubgroup m := by
    intro hwB
    have hh : φ w ∈ M ⊓ residualGenerated M z t := hB ▸ mem_map_of_mem φ hwB
    exact hvM (hw ▸ hh.1)
  obtain ⟨b, hb, hbconj⟩ := suzukiBorel_outside_involutions_conjugate m hm u hu huB w hwI hwB
  refine ⟨φ b, hB ▸ mem_map_of_mem φ hb, ?_⟩
  have hh := congrArg φ hbconj
  simpa only [MulAut.conj_apply, map_mul, map_inv, hft, hw] using hh

/-- The Suzuki local calculations needed by the assembly of Lemma 12.2(b,d,f),
with the actual model witness and the previously established containment `A ≤ L`.
No permutation-action, pair-parity or pair-normalizer hypothesis is needed for
these conclusions. -/
public theorem residualGenerated_suzuki_local_structure
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    {m : ℕ} (hm : 0 < m)
    (he : Nonempty (residualGenerated M z t ≃* SuzukiMatrixGroup m)) :
    let L := residualGenerated M z t
    let A := closure (Z ∩ (M : Set G))
    let B := M ⊓ L
    let E := residualPairStabilizer M t ⊓ L
    let T := (pCore 2 B).map B.subtype
    IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ (2 * m + 1) ∧
      (∃ S : Sylow 2 B, (S : Subgroup B) = pCore 2 B) ∧
      (B : Set G) = (T : Set G) * (E : Set G) ∧
      IsCyclic E ∧ Nat.card E = 2 ^ (2 * m + 1) - 1 ∧
      (∀ d ∈ E, rightConjugateElem d t = d⁻¹) ∧
      (∀ v ∈ L, PFAppendixIII.IsInvolution v → v ∉ M →
        ∃ b ∈ B, MulAut.conj b t = v) := by
  obtain ⟨e⟩ := he
  obtain ⟨hA, hAc⟩ :=
    residualGenerated_suzuki_distinguishedClosure h.disconnected r hz hzM ht htM hL hAL hm e
  obtain ⟨hE, hEc⟩ := residualGenerated_suzuki_pair_cyclic_card h.disconnected r hz hzM ht htM hL hm e
  exact ⟨hA, hAc, residualGenerated_suzuki_pCore_isSylow h.disconnected r hz hzM ht htM hL hm e,
    residualGenerated_suzuki_borel_product h.disconnected r hz hzM ht htM hL hm e,
    hE, hEc,
    fun _ hd => residualGenerated_suzuki_pair_inverted h.disconnected r hz hzM ht htM hL hm e hd,
    fun _ hvL hv hvM => residualGenerated_suzuki_outside_involutions_conjugate
      h.disconnected r hz hzM ht htM hL hm e hvL hv hvM⟩

end BenderSuzuki.ZD
