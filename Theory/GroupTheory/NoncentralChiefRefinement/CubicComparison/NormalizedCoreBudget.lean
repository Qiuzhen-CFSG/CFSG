module

public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.NormalizedModule
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Displacement
public import Theory.GroupAction.NoncentralTwoChiefLength.SectionMaps
public import Theory.GroupTheory.TwoPerfectCubicKernel
public import Theory.GroupTheory.CentralizerModulo
public import Theory.GroupTheory.PCoreImage

/-!
# Exhausting a cubic chief budget through the original action image

A normalized two-group Q is adjoined to the two-core of a cubic
two-perfect actor J. Mutual normalization bounds the cubic length of
this actual join by the chief budget of J. Two layers in its image and
one moved layer in W leave no movement on Q/W. The cubic kernel theorem
extends this bound from the chosen cubic subgroup to all of J.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup
namespace NoncentralChiefRefinement.CubicComparison
variable {G F : Type*} [Group G] [Finite G] [Group F]

/-- The literal image contributes no more cubic length than the section
above any subgroup killed by the same map. -/
theorem image_length_le_section (f : G →* F) (A Q P : Subgroup G)
    (hA : IsPGroup 3 A) (hP : IsPGroup 2 P) (hQP : Q≤P)
    (hAP : A≤normalizer (P : Set G)) (hQker : Q≤f.ker) :
    conjugationCubicLength (A.map f) (P.map f)≤sectionCubicLength A Q P := by
  let N := P ⊓ f.ker
  have hn : A.map f≤normalizer (P.map f : Set F) :=
    (map_mono hAP).trans (le_normalizer_map f)
  let := conjMulDistribMulActionOfLeNormalizer (A.map f) (P.map f) hn
  let s : ConjugationSection (Y:=P.map f) A N P (f.subgroupMap A) := {
    le := inf_le_left
    normalizes := hAP
    projection := f.subgroupMap P
    onto := f.subgroupMap_surjective P
    kernel := by
      ext p
      change (f.subgroupMap P) p=1 ↔ p.val∈P ⊓ f.ker
      rw [←Subtype.coe_inj]
      change f p=1 ↔ p.val∈P ∧ f p=1
      exact ⟨fun hh=>⟨p.property,hh⟩,And.right⟩
    equivariant := by
      intro a p
      apply Subtype.ext
      change f ((a:G)*(p:G)*(a:G)⁻¹)=f a*f p*(f a)⁻¹
      simp only [map_mul,map_inv] }
  have he := (s.length_eq hA hP (f.subgroupMap_surjective A)).trans
    (conjugationCubicLength_eq _ _ hn).symm
  exact he.symm.le.trans (sectionCubicLength_mono A (le_inf hQP hQker) le_rfl)

/-- Two outer cubic layers and one genuinely moved normal layer exhaust
the original three-factor budget, forcing the whole cubic residual to
centralize the intervening quotient. -/
theorem normalized_core_commutator_le_of_three_layer_budget
    (J Q W A : Subgroup G) [Q.Normal] [W.Normal]
    (hJ : IsPPerfect 2 J) (hc : Nat.card (J ⧸ pCore 2 J)=3)
    (hQ : IsPGroup 2 Q) (hQJ : Q≤normalizer (J : Set G))
    (hWQ : W≤Q) (hA : Nat.card A=3) (hAJ : A≤J)
    (hmove : ⁅W,A⁆≠⊥)
    (hbudget : ∀ s : ChiefSeries J, s.head=⊥ → s.last=⊤ → s.noncentralTwoCount≤3)
    (f : G →* F) (hQker : Q≤f.ker)
    (houter : 2≤conjugationCubicLength (A.map f) ((Q ⊔ J.pCoreIn 2).map f)) :
    ⁅Q,J⁆≤W := by
  let P := Q ⊔ J.pCoreIn 2
  have hP : IsPGroup 2 P := hQ.to_sup_of_normal_left (isPGroup_pCoreIn 2 J)
  have hPJ : P≤normalizer (J : Set G) :=
    sup_le hQJ ((pCoreIn_le 2 J).trans J.le_normalizer)
  have hJP : J≤normalizer (P : Set G) :=
    (le_inf le_normalizer_of_normal
      (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n:=1) (by simpa using hA)
  obtain ⟨s,hs0,hs1⟩ := exists_chiefSeries (⊥ : NormalNode J) ⊤ bot_le
  have hbound : conjugationCubicLength A P≤3 :=
    (count_ge_of_normalized_module J P A hc hP hA hAJ hPJ hJP le_rfl s hs0 hs1).trans
      (hbudget s hs0 hs1)
  have hWpos : 1≤conjugationCubicLength A W := by
    by_contra hn
    have hz : conjugationCubicLength A W=0 := by omega
    have hh := commutator_le_of_length_eq A W ⊥ hA3 (hQ.to_le hWQ) bot_le
      le_normalizer_of_normal le_normalizer_of_normal (by simpa using hz.symm)
    exact hmove (le_bot_iff.mp hh)
  have hsection : 2≤sectionCubicLength A Q P :=
    houter.trans (image_length_le_section f A Q P hA3 hP le_sup_left (hAJ.trans hJP) hQker)
  have hcomm : ⁅Q,A⁆≤W := commutator_le_of_length_budget A P Q W hA3 hQ hWQ le_sup_left
    le_normalizer_of_normal le_normalizer_of_normal 1 2 hbound hWpos hsection
  let C := centralizerModulo ⊤ Q W
  let q := QuotientGroup.mk' W
  let : (Q.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective W)
  let : C.Normal := by
    change (⊤ ⊓ (centralizer (Q.map q : Set (G ⧸ W))).comap q : Subgroup G).Normal
    infer_instance
  have hAC : A≤C := fun a ha=>mem_centralizerModulo_iff.mpr
    ⟨mem_top _,fun x hx=>hcomm (commutator_mem_commutator hx ha)⟩
  let π := (QuotientGroup.mk' C).comp J.subtype
  have hπ : π=1 := by
    by_contra hn
    have hp := π.kernel_isTwoGroup_of_twoPerfect_cubic hJ hc hn
    have hk : A.subgroupOf J≤π.ker := by
      intro a ha
      exact (QuotientGroup.eq_one_iff (a:G)).mpr (hAC ha)
    obtain ⟨n,hn⟩ := (hp.to_le hk).exists_card_eq
    rw [Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv,hA] at hn
    have hd : 3∣2^n := by rw [←hn]
    exact (by decide : ¬3∣2) (Nat.prime_three.dvd_of_dvd_pow hd)
  apply commutator_le.mpr
  intro x hx j hj
  have hjC : j∈C := (QuotientGroup.eq_one_iff j).mp
    (congrArg (fun k : J →* (G ⧸ C)=>k ⟨j,hj⟩) hπ)
  exact (mem_centralizerModulo_iff.mp hjC).2 x hx

end NoncentralChiefRefinement.CubicComparison
