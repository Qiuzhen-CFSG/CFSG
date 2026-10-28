module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Defs
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Literal sections in the terminal orthogonal argument

The quotient written K₀D/UD on printed p.1010 is not defined: the fixed-line
calculation implies UD is not contained in K₀D. The available actor is
K₀UD/UD. Moreover, a local C-component B normalizing a solvable subgroup Q
in its Sylow overgroup must satisfy [B,Q] ≤ B. This gives a check on any
proposed choice of the smaller component before an embedding list is used.

The actual image of UD modulo O₂(N_G(D)) has kernel D. The first isomorphism
theorem identifies this image with UD/D, and p-core image functoriality
identifies the core of the image of K₀UD with that section. Core escape
also makes any containing ambient C-component strictly larger.

These are deductions for the source assembly, not the component placement
or the A.3.14 classification. In particular no assertion here identifies
K₀ with the solvable residual of K₀UD.

Source: Aschbacher–Smith, combined manuscript, Lemma 14.4.9, p.1010;
Definition 1.2.3, p.505, and A.3.3(3), p.42.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- The literal diagonal residual centralizes the selected involution. -/
theorem diagonalResidual_le_involution_centralizer (H : Subgroup G) (i : G) :
    diagonalResidual H i ≤ centralizer ({i} : Set G) :=
  (map_subtype_le _).trans inf_le_right

omit [Finite G] in
/-- The source fixed line rules out the denominator containment in K₀D/UD. -/
theorem lift_join_not_le_diagonal_join (U : Subgroup G) (z i : G)
    (hD : IsElementaryAbelian 2 (centralizerLift U z i))
    (hCU : centralizerLift U z i ⊓ centralizer (U : Set G) = zpowers z)
    (hi : i ∉ zpowers z) :
    ¬ U ⊔ centralizerLift U z i ≤
      diagonalResidual (centralizer ({z} : Set G)) i ⊔ centralizerLift U z i := by
  intro h
  let D := centralizerLift U z i
  have hiD : i ∈ D := (show zpowers i ≤ D from le_sup_right.trans le_sup_left) (mem_zpowers i)
  have hDC : D ≤ centralizer ({i} : Set G) := by
    let : IsElementaryAbelian 2 D := hD
    let : CommGroup D := IsMulCommutative.instCommGroup
    intro d hd
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨d, hd⟩ : D) ⟨i, hiD⟩)
  have hUC : U ≤ centralizer ({i} : Set G) :=
    le_sup_left.trans (h.trans (sup_le ((map_subtype_le _).trans inf_le_right) hDC))
  apply hi
  rw [← hCU]
  exact ⟨hiD, fun u hu => mem_centralizer_singleton_iff.mp (hUC hu)⟩

/-- A necessary test for the proposed smaller local C-component. -/
theorem localComponent_commutator_le {B S Q : Subgroup G} (hB : B ∈ Chapter1.L G S)
    (hQ : Q ≤ B ⊔ S) (hp : IsPGroup 2 Q)
    (hn : B ≤ normalizer (Q : Set G)) : ⁅B, Q⁆ ≤ B := by
  let J := B ⊔ S
  have hBJ : B ≤ J := le_sup_left
  have hQJ : Q ≤ J := hQ
  have hp' : IsPGroup 2 (Q.subgroupOf J) := hp.comap_subtype
  let : Group.IsNilpotent (Q.subgroupOf J) := hp'.isNilpotent
  have hn' : B.subgroupOf J ≤ normalizer (Q.subgroupOf J : Set J) := by
    intro b hb
    apply mem_normalizer_iff.mpr
    intro q
    exact mem_normalizer_iff.mp (hn hb) q
  have hc := hB.1.commutator_le_of_solvable (Q.subgroupOf J) hn'
  have hm := map_mono (f := J.subtype) hc
  change (⁅B.subgroupOf J, Q.subgroupOf J⁆).map J.subtype ≤
    (B.subgroupOf J).map J.subtype at hm
  simpa only [map_commutator, map_subgroupOf_eq_of_le hBJ,
    map_subgroupOf_eq_of_le hQJ] using hm


/-- A subgroup acting nontrivially on Q/D cannot be the local component
when its intersection with Q lies in D. This diagnoses a proposed local
interface, without asserting a counterexample to the ambient source theorem. -/
theorem not_mem_localFamily_of_section_action {B S Q D : Subgroup G}
    (hQ : Q ≤ B ⊔ S) (hp : IsPGroup 2 Q)
    (hn : B ≤ normalizer (Q : Set G)) (hinter : B ⊓ Q ≤ D)
    (hmoves : ¬ ⁅B, Q⁆ ≤ D) : B ∉ Chapter1.L G S := by
  intro hB
  exact hmoves ((le_inf (localComponent_commutator_le hB hQ hp hn)
    (le_normalizer_iff_commutator_le_right.mp hn)).trans hinter)

omit [Finite G] in
/-- The preceding literal core equalities force the diagonal intersection
with UD into D. They also give normalization of UD by the diagonal. -/
theorem diagonal_normalizes_and_intersection_le (H U D : Subgroup G) (i : G)
    (hU : U = H.pCoreIn 2)
    (hD : D = (H ⊓ centralizer ({i} : Set G)).pCoreIn 2)
    (hp : IsPGroup 2 (U ⊔ D : Subgroup G)) :
    diagonalResidual H i ≤ normalizer (U ⊔ D : Subgroup G) ∧
      diagonalResidual H i ⊓ (U ⊔ D) ≤ D := by
  let C := H ⊓ centralizer ({i} : Set G)
  have hCU : C ≤ normalizer (U : Set G) := by
    rw [hU]
    exact inf_le_left.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hCD : C ≤ normalizer (D : Set G) := by
    rw [hD]
    exact C.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hCQ : C ≤ normalizer (U ⊔ D : Subgroup G) :=
    (le_inf hCU hCD).trans (normalizer_inf_normalizer_le_normalizer_sup U D)
  have hnormal : C ≤ normalizer (C ⊓ (U ⊔ D) : Subgroup G) :=
    (le_inf C.le_normalizer hCQ).trans inf_normalizer_le_normalizer_inf
  have hcore : C ⊓ (U ⊔ D) ≤ C.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (hp.to_le inf_le_right) inf_le_left hnormal
  have hKC : diagonalResidual H i ≤ C := map_subtype_le _
  exact ⟨hKC.trans hCQ, (inf_le_inf_right _ hKC).trans (hcore.trans hD.ge)⟩

/-- The literal K₀ fails the proposed local-family interface when its
prescribed action on UD/D is nontrivial. This does not refute the ambient
source theorem: its smaller local subgroup still needs to be constructed. -/
theorem diagonal_not_mem_localFamily (H U D S : Subgroup G) (i : G)
    (hU : U = H.pCoreIn 2)
    (hD : D = (H ⊓ centralizer ({i} : Set G)).pCoreIn 2)
    (hp : IsPGroup 2 (U ⊔ D : Subgroup G)) (hQS : U ⊔ D ≤ S)
    (hmoves : ¬ ⁅diagonalResidual H i, U ⊔ D⁆ ≤ D) :
    diagonalResidual H i ∉ Chapter1.L G S := by
  obtain ⟨hn, hinter⟩ := diagonal_normalizes_and_intersection_le H U D i hU hD hp
  exact not_mem_localFamily_of_section_action (hQS.trans le_sup_right) hp hn hinter hmoves

/-- A local core escaping the ambient core forces proper component inclusion. -/
theorem lt_containing_component_of_core_escape {B K V D : Subgroup G} (hK : K.IsCComponent) (hBK : B ≤ K)
    (hVB : V ≤ B.pCoreIn 2) (hVD : ¬ V ≤ D)
    (hinter : V ⊓ pCore 2 G ≤ D) : B < K := by
  refine lt_of_le_of_ne hBK ?_
  intro he
  subst B
  have hv := hVB.trans (pCoreIn_le_of_subnormal 2 hK.subnormal)
  exact hVD ((le_inf le_rfl hv).trans hinter)

omit [Finite G] in
/-- The section isomorphism retains the literal ambient two-core quotient map. -/
noncomputable def coreSectionEquiv (V D : Subgroup G)
    [(D.subgroupOf V).Normal] (h : V ⊓ pCore 2 G = D) :
    (V ⧸ D.subgroupOf V) ≃* V.map (QuotientGroup.mk' (pCore 2 G)) := by
  let f := (QuotientGroup.mk' (pCore 2 G)).subgroupMap V
  have hk : f.ker = D.subgroupOf V := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    ext x
    change (x : G) ∈ pCore 2 G ↔ (x : G) ∈ D
    rw [← h]
    exact (and_iff_right x.property).symm
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk' (pCore 2 G)).subgroupMap_surjective V))

omit [Finite G] in
/-- The section isomorphism agrees on every element with the original quotient. -/
@[simp] theorem coreSectionEquiv_mk (V D : Subgroup G) [(D.subgroupOf V).Normal]
    (h : V ⊓ pCore 2 G = D) (v : V) :
    (coreSectionEquiv V D h (QuotientGroup.mk' (D.subgroupOf V) v) :
      G ⧸ pCore 2 G) = QuotientGroup.mk' (pCore 2 G) (v : G) := by rfl

/-- Applied to A = K₀UD and V = UD, this identifies the actual image core. -/
theorem image_core_eq (A V : Subgroup G) (hcore : A.pCoreIn 2 = V) :
    (A.map (QuotientGroup.mk' (pCore 2 G))).pCoreIn 2 =
      V.map (QuotientGroup.mk' (pCore 2 G)) := by
  have hk : IsPGroup 2 (QuotientGroup.mk' (pCore 2 G)).ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  rw [← map_pCoreIn_of_ker_isPGroup _ hk, hcore]

omit [Finite G] in
/-- The map UD → N_G(D)/O₂(N_G(D)), expressed for any local overgroup. -/
noncomputable def localSectionMap (N V : Subgroup G) (hVN : V ≤ N) :
    V →* (N ⧸ pCore 2 N) :=
  (QuotientGroup.mk' (pCore 2 N)).comp (inclusion hVN)

omit [Finite G] in
/-- The intersection deduction of `lift_normalizer_core` computes the exact kernel. -/
theorem localSectionMap_ker (N V D : Subgroup G) (hVN : V ≤ N)
    (h : V ⊓ N.pCoreIn 2 = D) :
    (localSectionMap N V hVN).ker = D.subgroupOf V := by
  unfold localSectionMap
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  ext v
  change (inclusion hVN v ∈ pCore 2 N) ↔ (v : G) ∈ D
  rw [← h]
  constructor
  · intro hv
    exact ⟨v.property, mem_map.mpr ⟨inclusion hVN v, hv, rfl⟩⟩
  · rintro ⟨_, w, hw, he⟩
    have he' : w = inclusion hVN v := Subtype.ext he
    exact he' ▸ hw

omit [Finite G] in
/-- The range is the image of the literal restricted subgroup. -/
theorem localSectionMap_range (N V : Subgroup G) (hVN : V ≤ N) :
    (localSectionMap N V hVN).range =
      (V.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)) := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact mem_map.mpr ⟨inclusion hVN v, v.property, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

omit [Finite G] in
/-- In the source take N = N_G(D), V = UD. The denominator is the
literal restriction of D to V, justified by the computed kernel. -/
noncomputable def normalizerSectionEquiv (N V D : Subgroup G) (hVN : V ≤ N)
    [(D.subgroupOf V).Normal] (h : V ⊓ N.pCoreIn 2 = D) :
    (V ⧸ D.subgroupOf V) ≃* (localSectionMap N V hVN).range :=
  (QuotientGroup.quotientMulEquivOfEq (localSectionMap_ker N V D hVN h).symm).trans
    (QuotientGroup.quotientKerEquivRange (localSectionMap N V hVN))

omit [Finite G] in
/-- Each class maps to its actual normalizer-quotient image. -/
@[simp] theorem normalizerSectionEquiv_mk (N V D : Subgroup G) (hVN : V ≤ N)
    [(D.subgroupOf V).Normal] (h : V ⊓ N.pCoreIn 2 = D) (v : V) :
    (normalizerSectionEquiv N V D hVN h (QuotientGroup.mk' (D.subgroupOf V) v) :
      N ⧸ pCore 2 N) = localSectionMap N V hVN v := by rfl

/-- The actor A/O₂(A) is unchanged on mapping A into the ambient core
quotient. For A = K₀UD and O₂(A) = UD this is the corrected K₀UD/UD actor. -/
noncomputable def imageActorEquiv (A V : Subgroup G) [(V.subgroupOf A).Normal]
    (hcore : A.pCoreIn 2 = V) :
    (A ⧸ V.subgroupOf A) ≃*
      ((A.map (QuotientGroup.mk' (pCore 2 G))) ⧸
        pCore 2 (A.map (QuotientGroup.mk' (pCore 2 G)))) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let f := q.subgroupMap A
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hV : V ≤ A := hcore ▸ pCoreIn_le 2 A
  have he : V.subgroupOf A = pCore 2 A := by
    apply map_injective A.subtype_injective
    rw [map_subgroupOf_eq_of_le hV]
    exact hcore.symm
  exact (QuotientGroup.quotientMulEquivOfEq he).trans
    (f.pCoreQuotientEquiv (q.subgroupMap_surjective A) hk)

/-- The actor comparison commutes with both literal quotient projections. -/
@[simp] theorem imageActorEquiv_mk (A V : Subgroup G) [(V.subgroupOf A).Normal]
    (hcore : A.pCoreIn 2 = V) (a : A) :
    imageActorEquiv A V hcore (QuotientGroup.mk' (V.subgroupOf A) a) =
      QuotientGroup.mk' (pCore 2 (A.map (QuotientGroup.mk' (pCore 2 G))))
        (((QuotientGroup.mk' (pCore 2 G)).subgroupMap A) a) := by rfl

/-- The strict inclusion required by A.3.14 is in the core quotient itself.
A nontrivial image of the smaller intrinsic core prevents equality there. -/
theorem strict_image_in_containing_component {B K : Subgroup G}
    (hK : K.IsCComponent) (hBK : B ≤ K)
    (hcore : ¬ B.pCoreIn 2 ≤ pCore 2 G) :
    B.map (QuotientGroup.mk' (pCore 2 G)) <
      K.map (QuotientGroup.mk' (pCore 2 G)) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  refine lt_of_le_of_ne (map_mono hBK) ?_
  intro he
  let := pCore_isNilpotent (p := 2) (G := G)
  have hKq := hK.map_quotient (pCore 2 G)
  have hle := pCoreIn_le_of_subnormal 2 hKq.subnormal
  rw [pCore_quotient_pCore_eq_bot] at hle
  have hm : (B.pCoreIn 2).map q = ⊥ := by
    rw [map_pCoreIn_of_ker_isPGroup q hk, he]
    exact le_bot_iff.mp hle
  have hh : B.pCoreIn 2 ≤ q.ker := (Subgroup.map_eq_bot_iff _).mp hm
  rw [QuotientGroup.ker_mk'] at hh
  exact hcore hh

/-- Application of the genuine universal 1.2.4 inputs with properness
proved in the quotient where the embedding classification is applied.
Local-family placement and core escape remain explicit earlier obligations. -/
theorem proper_embedding_of_local_source
    {𝒦 : GroupClass.{u}}
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents T → Chapter1.Section02.A312Conclusion B)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ K : Subgroup X, K.IsCComponent →
      K.Normal ∨ (normalizer (K : Set X)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel K)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ Chapter1.L G S)
    (hcore : ¬ B.pCoreIn 2 ≤ pCore 2 G) :
    ∃ K : Subgroup G, K.IsCComponent ∧ B < K ∧
      (∀ C : Subgroup G, C.IsCComponent → B ≤ C → C = K) ∧
      B.map (QuotientGroup.mk' (pCore 2 G)) <
        K.map (QuotientGroup.mk' (pCore 2 G)) ∧
      Chapter1.Section02.A312Embedding (B.map (QuotientGroup.mk' (pCore 2 G)))
        (K.map (QuotientGroup.mk' (pCore 2 G))) := by
  obtain ⟨K, hK, hBK, hu, hemb, _⟩ :=
    Chapter1.Section02.lemma_1_2_4_of_A_3_12_A_3_8 hA312 hA38 hQ S hB
  have hlt := strict_image_in_containing_component hK hBK hcore
  refine ⟨K, hK, lt_of_le_of_ne hBK ?_, hu, hlt, hemb⟩
  intro he
  exact hlt.ne (congrArg (map (QuotientGroup.mk' (pCore 2 G))) he)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve
