module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.Sylow
public import Theory.Mathieu.M22.ChapterHLocalClassification.Sylow.Inner
public import Theory.ElementaryAbelian.Injective

/-!
# Native M22 elementary image containers

A fixed Sylow conjugation aligns the literal embedding M22 → M23 with the
checked order-128 permutation subgroup. Pulling its six elementary containers
back gives actual subgroups of M22. The established E16 classification identifies
the two large rows with the native hexad kernel and sextet translations.
Sylow conjugacy then covers every elementary subgroup, without a normality
or size premise, retaining the ambient M22 conjugator.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Lemma 2.2.1,
pp.489--490. This supplies exhaustive subgroup placement for the inner quotient.
The E8 normalizer identification and the subsequent lifted J4 geometry are
separate obligations. `Residual` applies these actual subgroups to the native
second-centralizer quotient, rather than treating the M22 carrier as embedded
in J4.
-/

public noncomputable section
open Subgroup Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
open M22ChapterH M22ChapterH.CompatibleSylow

private theorem embedding_injective : Function.Injective m22InM23 :=
  fun _ _ h => m22Embedding_injective (congrArg pointEmbedding h)

private def imageSylow : Sylow 2 M23 :=
  Sylow.ofCard (inner.toSubgroup.map m22InM23) (by
    rw [card_map_of_injective embedding_injective]
    change Nat.card innerGroup = _
    rw [innerGroup_card,m23_order]
    decide +kernel)

private def alignment : M23 :=
  (MulAction.exists_smul_eq M23 imageSylow M23Geometry.FusionCertificate.sylow).choose

/-- A fixed native embedding aligning the actual M22 Sylow with the checked
128-element M23 permutation subgroup. -/
def alignedEmbedding : M22 →* M23 :=
  (MulAut.conj alignment).toMonoidHom.comp m22InM23

theorem alignedEmbedding_injective : Function.Injective alignedEmbedding :=
  (MulAut.conj alignment).injective.comp embedding_injective

/-- The aligned embedding differs from the original native inclusion by
an actual M23 conjugator. This retains the quotient marking when lifting
the elementary-image calculations to the J4 Mathieu local. -/
theorem alignedEmbedding_conjugator : ∃ c : M23,
    alignedEmbedding = (MulAut.conj c).toMonoidHom.comp m22InM23 :=
  ⟨alignment,rfl⟩

theorem alignedEmbedding_sylow : inner.toSubgroup.map alignedEmbedding =
    M23Geometry.FusionCertificate.subgroup := by
  rw [alignedEmbedding,← map_map]
  exact congrArg Sylow.toSubgroup
    (MulAction.exists_smul_eq M23 imageSylow M23Geometry.FusionCertificate.sylow).choose_spec

/-- The four additional native M22 elementary containers. They are literal
preimages through the fixed injective permutation marking. -/
@[expose] def smallContainer (k : Fin 4) : Subgroup M22 :=
  (small k).comap alignedEmbedding

private theorem mapped_comap (B : Subgroup M23)
    (hB : B ≤ M23Geometry.FusionCertificate.subgroup) :
    (B.comap alignedEmbedding).map alignedEmbedding = B := by
  rw [map_comap_eq,inf_eq_right]
  rw [← alignedEmbedding_sylow] at hB
  exact hB.trans (map_le_range _ _)

private theorem comap_le_inner (B : Subgroup M23)
    (hB : B ≤ M23Geometry.FusionCertificate.subgroup) :
    B.comap alignedEmbedding ≤ inner.toSubgroup := by
  have h := comap_mono (f := alignedEmbedding) hB
  rw [← alignedEmbedding_sylow,comap_map_eq_self_of_injective alignedEmbedding_injective] at h
  exact h

private theorem elementary_comap (B : Subgroup M23) [IsElementaryAbelian 2 B] :
    IsElementaryAbelian 2 (B.comap alignedEmbedding) := by
  let f : B.comap alignedEmbedding →* B :=
    (alignedEmbedding.comp (B.comap alignedEmbedding).subtype).codRestrict B (fun x => x.property)
  exact IsElementaryAbelian.of_injective f
    (fun _ _ h => Subtype.ext (alignedEmbedding_injective (congrArg Subtype.val h)))

theorem smallContainer_le_inner (k : Fin 4) : smallContainer k ≤ inner.toSubgroup :=
  comap_le_inner _ (small_le_sylow k)

theorem smallContainer_map (k : Fin 4) :
    (smallContainer k).map alignedEmbedding = small k :=
  mapped_comap _ (small_le_sylow k)

theorem smallContainer_card (k : Fin 4) : Nat.card (smallContainer k) = 8 := by
  rw [← card_map_of_injective alignedEmbedding_injective,smallContainer_map,small_card]

theorem smallContainer_elementary (k : Fin 4) : IsElementaryAbelian 2 (smallContainer k) := by
  let := small_elementary k
  exact elementary_comap _

/-- The order-sixteen rows are the actual source hexad and sextet cores. -/
theorem elementary_inner_cover (A : Subgroup M22) [IsElementaryAbelian 2 A]
    (hAS : A ≤ inner.toSubgroup) :
    A ≤ m22InnerHexadKernel m22SourceOctad ∨ A ≤ Sextet.innerTranslations ∨
      ∃ k : Fin 4, A ≤ smallContainer k := by
  let : IsElementaryAbelian 2 (A.map alignedEmbedding) := IsElementaryAbelian.map _
  have hA : A.map alignedEmbedding ≤ M23Geometry.FusionCertificate.subgroup :=
    alignedEmbedding_sylow ▸ map_mono hAS
  rcases elementary_sylow_cover (A.map alignedEmbedding) hA with ⟨b,hb⟩ | ⟨k,hk⟩
  · let B := (M23Geometry.ElementarySylow.candidate b).comap alignedEmbedding
    let := M23Geometry.ElementarySylow.candidate_elementary b
    have hBe : IsElementaryAbelian 2 B := elementary_comap _
    have hBc : Nat.card B = 16 := by
      rw [← card_map_of_injective alignedEmbedding_injective,
        mapped_comap _ (M23Geometry.ElementarySylow.candidate_le_sylow b),
        M23Geometry.ElementarySylow.candidate_card]
    have hAB : A ≤ B := (map_le_iff_le_comap).mp hb
    rcases inner_card16 B hBe hBc
      (comap_le_inner _ (M23Geometry.ElementarySylow.candidate_le_sylow b)) with he | he
    · exact Or.inl (he ▸ hAB)
    · exact Or.inr (Or.inl (he ▸ hAB))
  · exact Or.inr (Or.inr ⟨k,(map_le_iff_le_comap).mp hk⟩)

/-- Arbitrary native M22 elementary subgroups have literal conjugate placement
in the two source E16 kernels or the four checked E8 containers. -/
theorem elementary_native_cover (A : Subgroup M22) [IsElementaryAbelian 2 A] :
    ∃ g : M22,
      A ≤ (m22InnerHexadKernel m22SourceOctad).map (MulAut.conj g).toMonoidHom ∨
      A ≤ Sextet.innerTranslations.map (MulAut.conj g).toMonoidHom ∨
      ∃ k : Fin 4, A ≤ (smallContainer k).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M22 CompatibleSylow.inner S
  let B := A.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBS : B ≤ inner.toSubgroup := by
    rintro _ ⟨x,hx,rfl⟩
    have hxS := hAS hx
    rw [← hg] at hxS
    obtain ⟨y,hy,he⟩ := hxS
    have he' : (MulAut.conj g⁻¹) x = y := by
      rw [← he]
      simp [mul_assoc]
    exact he' ▸ hy
  have hback : B.map (MulAut.conj g).toMonoidHom = A := by
    rw [map_map]
    have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id M22 := by ext x; simp [mul_assoc]
    rw [he,map_id]
  have transfer (C : Subgroup M22) (h : B ≤ C) :
      A ≤ C.map (MulAut.conj g).toMonoidHom := hback ▸ map_mono h
  refine ⟨g,?_⟩
  rcases elementary_inner_cover B hBS with h | h | ⟨k,h⟩
  · exact Or.inl (transfer _ h)
  · exact Or.inr (Or.inl (transfer _ h))
  · exact Or.inr (Or.inr ⟨k,transfer _ h⟩)


/-- The aligned native M22 image is the full stabilizer of the unique point
fixed by the certified Sylow subgroup. This permits literal lifting of the
finite permutation conjugators, not merely abstract M22 conjugacy. -/
theorem alignedEmbedding_range : alignedEmbedding.range =
    MulAction.stabilizer M23 (0 : Fin 23) := by
  have hfixed : ∀ (i : Fin 128),
      M23Geometry.FusionCertificate.perm i ((alignment : Equiv.Perm (Fin 23)) 9) =
        (alignment : Equiv.Perm (Fin 23)) 9 := by
    intro i
    let p : M23 := ⟨M23Geometry.FusionCertificate.perm i,
      M23Geometry.FusionCertificate.rawSubgroup_le (M23Geometry.FusionCertificate.perm_mem i)⟩
    have hp : p ∈ inner.toSubgroup.map alignedEmbedding := by
      rw [alignedEmbedding_sylow]
      exact M23Geometry.FusionCertificate.perm_mem i
    obtain ⟨u,_,hu⟩ := hp
    have h9 := (m23EquivM22PointStabilizer u).property
    change (m22InM23 u : Equiv.Perm (Fin 23)) 9 = 9 at h9
    have hperm := congrArg (fun v : M23 => (v : Equiv.Perm (Fin 23))
      ((alignment : Equiv.Perm (Fin 23)) 9)) hu
    simpa [alignedEmbedding, MulAut.conj_apply, h9] using hperm.symm
  have hpoint : (alignment : Equiv.Perm (Fin 23)) 9 = 0 := by
    have hc : ∀ x : Fin 23,
        M23Geometry.FusionCertificate.pointTable 2 x = x →
        M23Geometry.FusionCertificate.pointTable 8 x = x → x = 0 := by decide +kernel
    exact hc _ (hfixed 2) (hfixed 8)
  ext v
  constructor
  · rintro ⟨u,rfl⟩
    change (alignedEmbedding u : Equiv.Perm (Fin 23)) 0 = 0
    rw [← hpoint]
    have h9 := (m23EquivM22PointStabilizer u).property
    change (m22InM23 u : Equiv.Perm (Fin 23)) 9 = 9 at h9
    simp [alignedEmbedding, MulAut.conj_apply, h9]
  · intro hv
    let w : M23 := alignment⁻¹ * v * alignment
    have hw : w ∈ MulAction.stabilizer M23 (9 : Fin 23) := by
      change (alignment : Equiv.Perm (Fin 23)).symm
        ((v : Equiv.Perm (Fin 23)) ((alignment : Equiv.Perm (Fin 23)) 9)) = 9
      change (v : Equiv.Perm (Fin 23)) 0 = 0 at hv
      rw [hpoint,hv,← hpoint,Equiv.symm_apply_apply]
    obtain ⟨u,hu⟩ := m23EquivM22PointStabilizer.surjective ⟨w,hw⟩
    have hu' : m22InM23 u = w := congrArg Subtype.val hu
    refine ⟨u,?_⟩
    change alignment * m22InM23 u * alignment⁻¹ = v
    rw [hu']
    simp [w,mul_assoc]

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
