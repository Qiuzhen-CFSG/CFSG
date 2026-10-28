module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.ThompsonImage
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.LocalSylow
public import Stellmacher.ElementaryAbelianMaxJWeakClosure
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.AlternatingSylowNormalizer
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# The actual point-line intersection and its two-core

Let U be the common Sylow, A=J(U), and N=N_G(Z). Suppose R lies in U,
A lies in S, and K normalizes A, as proved for the original Mathieu
application. The image of A in the original S/R marking is the alternating
Sylow four-group P. An element normalizing that image sends A into AR,
which lies in U; Thompson weak closure therefore lifts its normalizer.
Consequently N intersect N_G(A), modulo R, is Aut(Z) times N_S5(P).
The latter normalizer is S4 with two-core P and quotient S3.

Thus the literal intersection has index five in N; its two-core is AR,
of order 2^17, and its quotient is L3(2) times S3. Both original factor
markings are retained by a representative formula before removing the
four-group. K lies normally in the intersection. The original-input
Mathieu application in MathieuJ4RecognitionApplication.PointLine discharges
every displayed premise; no PointData or splitting is assumed.

This constructs the core and quotient clauses of the point-line overlap.
The split extension by A asserted in the remainder of (4.7), Todd splitting,
compatible plane overlaps and final recognition remain separate obligations.
Source: Aschbacher--Segev, *The uniqueness of groups of type J4*, Invent.
Math. 105 (1991), (4.7), printed p.598, DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup Stellmacher
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)
attribute [local instance] R_normal_in_K R_normal_in_S_intrinsic R_normal_in_normalizer

noncomputable def lineProjection (h : IsTypeJ4 z) : normalizer (d.space : Set G) →* Equiv.Perm (Fin 5) :=
  (MonoidHom.snd _ _).comp ((d.markedNormalizerQuotientEquiv h).toMonoidHom.comp (QuotientGroup.mk' _))

theorem lineProjection_product (h : IsTypeJ4 z) (k : d.K) (s : d.S)
    (n : normalizer (d.space : Set G)) (hn : (n : G) = (k : G) * (s : G)) :
    d.lineProjection h n = d.symmetricProjection h s := by
  change (d.markedNormalizerQuotientEquiv h (QuotientGroup.mk' _ n)).2 = _
  have he : n = (⟨(k : G)*(s : G), (normalizer (d.space : Set G)).mul_mem
      (d.K_le_normalizer k.property) ((Subgroup.centralizer_le_normalizer _) s.property)⟩ :
      normalizer (d.space : Set G)) := Subtype.ext hn
  rw [he,d.markedNormalizerQuotientEquiv_product]
  rfl

theorem lineProjection_surjective (h : IsTypeJ4 z) : Function.Surjective (d.lineProjection h) :=
  (fun b => by
    obtain ⟨n,hn⟩ := ((d.markedNormalizerQuotientEquiv h).surjective.comp
      (QuotientGroup.mk'_surjective _)) (1,b)
    exact ⟨n,congrArg Prod.snd hn⟩)

theorem symmetricProjection_surjective (h : IsTypeJ4 z) : Function.Surjective (d.symmetricProjection h) :=
  (d.SQuotientEquiv h).surjective.comp (QuotientGroup.mk'_surjective _)

theorem thompson_symmetric_normalizer (h : IsTypeJ4 z) (U : Subgroup G)
    (hR : d.R ≤ U) (hAS : elementaryAbelianMaxJ U ≤ d.S) :
    (normalizer (elementaryAbelianMaxJ U : Set G)).subgroupOf d.S =
      (normalizer (d.symmetricImage h (elementaryAbelianMaxJ U) : Set (Equiv.Perm (Fin 5)))).comap
        (d.symmetricProjection h) := by
  let A := elementaryAbelianMaxJ U
  let f := d.symmetricProjection h
  have hAU : A ≤ U := sSup_le fun _ hB => hB.1
  have hpre : (d.symmetricImage h A).comap f ≤ U.subgroupOf d.S := by
    rw [symmetricImage,comap_map_eq,d.symmetricProjection_ker]
    exact sup_le (fun x hx => hAU hx) (fun x hx => hR hx)
  apply le_antisymm
  · rw [subgroupOf_normalizer_eq hAS]
    exact map_le_iff_le_comap.mp ((A.subgroupOf d.S).le_normalizer_map f)
  · intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply elementaryAbelianMaxJ_map_eq_of_le U (MulAut.conj s.val)
    rintro _ ⟨a,ha,rfl⟩
    let a' : d.S := ⟨a,hAS ha⟩
    have hh : s*a'*s⁻¹ ∈ (d.symmetricImage h A).comap f := by
      change f (s*a'*s⁻¹) ∈ d.symmetricImage h A
      rw [map_mul,map_mul,map_inv]
      exact (mem_normalizer_iff.mp hs (f a')).mp (mem_map_of_mem f ha)
    exact hpre hh

/-- The actual point-line intersection before any splitting is chosen. -/
def pointLineGroup (U : Subgroup G) : Subgroup G :=
  normalizer (d.space : Set G) ⊓ normalizer (elementaryAbelianMaxJ U : Set G)

theorem thompson_pointLineGroup_preimage (h : IsTypeJ4 z) (U : Subgroup G)
    (hR : d.R ≤ U) (hAS : elementaryAbelianMaxJ U ≤ d.S)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G)) :
    (d.pointLineGroup U).subgroupOf (normalizer (d.space : Set G)) =
      (normalizer (d.symmetricImage h (elementaryAbelianMaxJ U) : Set (Equiv.Perm (Fin 5)))).comap
        (d.lineProjection h) := by
  ext n
  obtain ⟨k,hk,s,hs,he⟩ := d.normalizer_product h n.val n.property
  have hp := d.lineProjection_product h ⟨k,hk⟩ ⟨s,hs⟩ n he.symm
  change (n.val ∈ normalizer (d.space : Set G) ∧ n.val ∈ normalizer (elementaryAbelianMaxJ U : Set G)) ↔ _
  rw [and_iff_right n.property]
  change n.val ∈ normalizer (elementaryAbelianMaxJ U : Set G) ↔ d.lineProjection h n ∈ normalizer (d.symmetricImage h (elementaryAbelianMaxJ U) : Set (Equiv.Perm (Fin 5)))
  rw [hp,←show (⟨s,hs⟩ : d.S) ∈ (normalizer (elementaryAbelianMaxJ U : Set G)).subgroupOf d.S ↔
      d.symmetricProjection h ⟨s,hs⟩ ∈ normalizer
        (d.symmetricImage h (elementaryAbelianMaxJ U) : Set (Equiv.Perm (Fin 5))) from
      by rw [d.thompson_symmetric_normalizer h U hR hAS]; rfl]
  change n.val ∈ normalizer (elementaryAbelianMaxJ U : Set G) ↔ s ∈ normalizer (elementaryAbelianMaxJ U : Set G)
  rw [←he]
  exact mul_mem_cancel_left (hK hk)

/-- Both original factors are retained on the actual point-line intersection. -/
noncomputable def pointLineProjection (h : IsTypeJ4 z) (U : Subgroup G) :
    d.pointLineGroup U →* MulAut d.space × Equiv.Perm (Fin 5) :=
  ((d.markedNormalizerQuotientEquiv h).toMonoidHom.comp (QuotientGroup.mk' _)).comp
    (inclusion inf_le_left)

theorem pointLineProjection_ker (h : IsTypeJ4 z) (U : Subgroup G) :
    (d.pointLineProjection h U).ker = d.R.subgroupOf (d.pointLineGroup U) := by
  ext n
  change d.markedNormalizerQuotientEquiv h (QuotientGroup.mk' _ (inclusion inf_le_left n)) = 1 ↔ _
  rw [map_eq_one_iff _ (d.markedNormalizerQuotientEquiv h).injective]
  exact QuotientGroup.eq_one_iff _

theorem pointLineProjection_range (h : IsTypeJ4 z) (U : Subgroup G)
    (hR : d.R ≤ U) (hAS : elementaryAbelianMaxJ U ≤ d.S)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G)) :
    (d.pointLineProjection h U).range = (⊤ : Subgroup (MulAut d.space)).prod
      (normalizer (d.symmetricImage h (elementaryAbelianMaxJ U) : Set (Equiv.Perm (Fin 5)))) := by
  let q := (d.markedNormalizerQuotientEquiv h).toMonoidHom.comp (QuotientGroup.mk' _)
  have hq : Function.Surjective q := (d.markedNormalizerQuotientEquiv h).surjective.comp
    (QuotientGroup.mk'_surjective _)
  ext b
  constructor
  · rintro ⟨n,rfl⟩
    refine ⟨mem_top _,?_⟩
    have hh : inclusion (show d.pointLineGroup U ≤ normalizer (d.space : Set G) from inf_le_left) n ∈
        (d.pointLineGroup U).subgroupOf (normalizer (d.space : Set G)) := n.property
    rw [d.thompson_pointLineGroup_preimage h U hR hAS hK] at hh
    exact hh
  · intro hb
    obtain ⟨n,hn⟩ := hq b
    have hm : n ∈ (d.pointLineGroup U).subgroupOf (normalizer (d.space : Set G)) := by
      rw [d.thompson_pointLineGroup_preimage h U hR hAS hK]
      change (q n).2 ∈ normalizer (d.symmetricImage h (elementaryAbelianMaxJ U) : Set (Equiv.Perm (Fin 5)))
      rw [hn]
      exact hb.2
    exact ⟨⟨n.val,hm⟩,hn⟩

theorem R_le_pointLineGroup (U : Subgroup G)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G)) : d.R ≤ d.pointLineGroup U :=
  le_inf d.R_le_normalizer (inf_le_left.trans hK)

theorem pointLineGroup_R_normal (U : Subgroup G) :
    (d.R.subgroupOf (d.pointLineGroup U)).Normal :=
  (d.R_normal_in_normalizer).comap (inclusion (show d.pointLineGroup U ≤
    normalizer (d.space : Set G) from inf_le_left))

attribute [local instance] pointLineGroup_R_normal

/-- Quotienting the literal overlap by R gives the full original linear factor
and the normalizer of the original marked four-group. -/
noncomputable def pointLineGroupQuotientEquiv (h : IsTypeJ4 z) (U : Subgroup G)
    (hR : d.R ≤ U) (hAS : elementaryAbelianMaxJ U ≤ d.S)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G)) :
    (d.pointLineGroup U ⧸ d.R.subgroupOf (d.pointLineGroup U)) ≃*
      MulAut d.space × normalizer (d.symmetricImage h (elementaryAbelianMaxJ U) : Set (Equiv.Perm (Fin 5))) :=
  (QuotientGroup.quotientMulEquivOfEq (d.pointLineProjection_ker h U).symm).trans
    ((QuotientGroup.quotientKerEquivRange (d.pointLineProjection h U)).trans
      ((MulEquiv.subgroupCongr (d.pointLineProjection_range h U hR hAS hK)).trans
        ((prodEquiv _ _).trans ((topEquiv : (⊤ : Subgroup (MulAut d.space)) ≃* _).prodCongr
          (MulEquiv.refl _)))))

theorem pointLineGroupQuotientEquiv_mk (h : IsTypeJ4 z) (U : Subgroup G)
    (hR : d.R ≤ U) (hAS : elementaryAbelianMaxJ U ≤ d.S)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G)) (n : d.pointLineGroup U) :
    let b := d.pointLineGroupQuotientEquiv h U hR hAS hK (QuotientGroup.mk' _ n)
    (b.1,b.2.val) = d.pointLineProjection h U n := rfl


theorem linearAut_twoCore (h : IsTypeJ4 z) : pCore 2 (MulAut d.space) = ⊥ := by
  let f := (QuotientGroup.quotientMulEquivOfEq (d.R_subgroupOf_K_eq_twoCore h)).symm.trans
    (d.KQuotientEquivAut h)
  rw [←pCore_map_iso 2 f,pCore_quotient_pCore_eq_bot]
  exact Subgroup.map_bot f.toMonoidHom

theorem pointLineGroup_index (h : IsTypeJ4 z) (U : Subgroup G)
    (hR : d.R ≤ U) (hAS : elementaryAbelianMaxJ U ≤ d.S)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G))
    (P : Sylow 2 (alternatingGroup (Fin 5)))
    (hP : d.symmetricImage h (elementaryAbelianMaxJ U) = AlternatingSylowNormalizer.image P) :
    (d.pointLineGroup U).relIndex (normalizer (d.space : Set G)) = 5 := by
  change ((d.pointLineGroup U).subgroupOf (normalizer (d.space : Set G))).index = 5
  rw [d.thompson_pointLineGroup_preimage h U hR hAS hK,
    index_comap_of_surjective _ (d.lineProjection_surjective h),hP]
  exact AlternatingSylowNormalizer.index P

theorem pointLineGroup_card (h : IsTypeJ4 z) (U : Subgroup G)
    (hR : d.R ≤ U) (hAS : elementaryAbelianMaxJ U ≤ d.S)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G))
    (P : Sylow 2 (alternatingGroup (Fin 5)))
    (hP : d.symmetricImage h (elementaryAbelianMaxJ U) = AlternatingSylowNormalizer.image P) :
    Nat.card (d.pointLineGroup U) = 132120576 := by
  have hh := ((d.pointLineGroup U).subgroupOf (normalizer (d.space : Set G))).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show d.pointLineGroup U ≤
    normalizer (d.space : Set G) from inf_le_left)).toEquiv] at hh
  change Nat.card (d.pointLineGroup U) * (d.pointLineGroup U).relIndex _ = _ at hh
  rw [d.pointLineGroup_index h U hR hAS hK P hP,d.normalizer_card h] at hh
  omega

theorem pointLineGroup_twoCore_card (h : IsTypeJ4 z) (U : Subgroup G)
    (hR : d.R ≤ U) (hAS : elementaryAbelianMaxJ U ≤ d.S)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G))
    (P : Sylow 2 (alternatingGroup (Fin 5)))
    (hP : d.symmetricImage h (elementaryAbelianMaxJ U) = AlternatingSylowNormalizer.image P) :
    Nat.card (pCore 2 (d.pointLineGroup U)) = 2^17 := by
  let f := (d.pointLineGroupQuotientEquiv h U hR hAS hK).toMonoidHom.comp
    (QuotientGroup.mk' (d.R.subgroupOf (d.pointLineGroup U)))
  have hf : Function.Surjective f := (d.pointLineGroupQuotientEquiv h U hR hAS hK).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = d.R.subgroupOf (d.pointLineGroup U) := by
    rw [MonoidHom.ker_comp_of_injective _ _ (d.pointLineGroupQuotientEquiv h U hR hAS hK).injective,
      QuotientGroup.ker_mk']
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    apply IsPGroup.comap_subtype
    rw [d.R_eq_K_twoCore h]
    exact isPGroup_pCoreIn 2 d.K
  have hc : Nat.card (pCore 2 (MulAut d.space × normalizer
      (d.symmetricImage h (elementaryAbelianMaxJ U) : Set (Equiv.Perm (Fin 5))))) = 4 := by
    rw [pCore_prod,d.linearAut_twoCore h,Nat.card_congr (prodEquiv _ _).toEquiv,
      Nat.card_prod,card_bot,one_mul,hP,AlternatingSylowNormalizer.twoCore_card]
  rw [f.card_pCore_of_ker_isPGroup hf hp,hk,
    Nat.card_congr (subgroupOfEquivOfLe (d.R_le_pointLineGroup U hK)).toEquiv,d.R_card h,hc]
  norm_num

theorem thompson_radical_join_card (h : IsTypeJ4 z) (U : Subgroup G)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G))
    (hc : Nat.card (elementaryAbelianMaxJ U) = 2048)
    (hi : Nat.card (elementaryAbelianMaxJ U ⊓ d.R : Subgroup G) = 512) :
    Nat.card (elementaryAbelianMaxJ U ⊔ d.R : Subgroup G) = 2^17 := by
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes (elementaryAbelianMaxJ U) d.R
    (inf_le_left.trans hK)
  rw [hc,hi,d.R_card h] at hh
  norm_num at hh ⊢
  omega

/-- The literal point-line two-core is J(U)R, with relative normality retained. -/
theorem pointLineGroup_twoCore (h : IsTypeJ4 z) (U : Sylow 2 G)
    (hR : d.R ≤ (U : Subgroup G)) (hAS : elementaryAbelianMaxJ (U : Subgroup G) ≤ d.S)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G))
    (hc : Nat.card (elementaryAbelianMaxJ (U : Subgroup G)) = 2048)
    (hi : Nat.card (elementaryAbelianMaxJ (U : Subgroup G) ⊓ d.R : Subgroup G) = 512)
    (P : Sylow 2 (alternatingGroup (Fin 5)))
    (hP : d.symmetricImage h (elementaryAbelianMaxJ (U : Subgroup G)) = AlternatingSylowNormalizer.image P) :
    pCore 2 (d.pointLineGroup (U : Subgroup G)) =
      (elementaryAbelianMaxJ (U : Subgroup G) ⊔ d.R).subgroupOf (d.pointLineGroup (U : Subgroup G)) := by
  let A := elementaryAbelianMaxJ (U : Subgroup G)
  let B := A ⊔ d.R
  let J := d.pointLineGroup (U : Subgroup G)
  have hAJ : A ≤ J := le_inf (hAS.trans (Subgroup.centralizer_le_normalizer _)) A.le_normalizer
  have hBJ : B ≤ J := sup_le hAJ (d.R_le_pointLineGroup _ hK)
  have hn : J ≤ normalizer (B : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans d.R_normalized)).trans
      (normalizer_inf_normalizer_le_normalizer_sup A d.R)
  let : (B.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hBJ).mpr hn
  have hBU : B ≤ (U : Subgroup G) := sup_le (sSup_le fun _ hA => hA.1) hR
  have hpB : IsPGroup 2 B := U.isPGroup'.of_injective (inclusion hBU) (inclusion_injective hBU)
  have hp : IsPGroup 2 (B.subgroupOf J) := hpB.comap_subtype
  have hl : B.subgroupOf J ≤ pCore 2 J := le_sSup ⟨inferInstance,hp⟩
  apply Eq.symm
  apply eq_of_le_of_card_ge hl
  change Nat.card (pCore 2 (d.pointLineGroup (U : Subgroup G))) ≤ Nat.card (B.subgroupOf J)
  rw [Nat.card_congr (subgroupOfEquivOfLe hBJ).toEquiv,
    d.thompson_radical_join_card h _ hK hc hi,d.pointLineGroup_twoCore_card h _ hR hAS hK P hP]


/-- The actual point-line quotient by its two-core, retaining the original K-action factor. -/
noncomputable def pointLineGroupCoreQuotientEquiv (h : IsTypeJ4 z) (U : Subgroup G)
    (hR : d.R ≤ U) (hAS : elementaryAbelianMaxJ U ≤ d.S)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G))
    (P : Sylow 2 (alternatingGroup (Fin 5)))
    (hP : d.symmetricImage h (elementaryAbelianMaxJ U) = AlternatingSylowNormalizer.image P) :
    (d.pointLineGroup U ⧸ pCore 2 (d.pointLineGroup U)) ≃*
      MulAut d.space × Equiv.Perm (Fin 3) := by
  let eP := (d.pointLineGroupQuotientEquiv h U hR hAS hK).trans
    ((MulEquiv.refl (MulAut d.space)).prodCongr (MulEquiv.subgroupCongr
      (congrArg (fun B : Subgroup (Equiv.Perm (Fin 5)) => normalizer (B : Set (Equiv.Perm (Fin 5)))) hP)))
  let f := eP.toMonoidHom.comp (QuotientGroup.mk' (d.R.subgroupOf (d.pointLineGroup U)))
  have hf : Function.Surjective f := eP.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = d.R.subgroupOf (d.pointLineGroup U) := by
    rw [MonoidHom.ker_comp_of_injective _ _ eP.injective,QuotientGroup.ker_mk']
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    apply IsPGroup.comap_subtype
    rw [d.R_eq_K_twoCore h]
    exact isPGroup_pCoreIn 2 d.K
  have ht : pCore 2 (MulAut d.space × normalizer (AlternatingSylowNormalizer.image P : Set (Equiv.Perm (Fin 5)))) =
      (⊥ : Subgroup (MulAut d.space)).prod ((AlternatingSylowNormalizer.image P).subgroupOf
        (normalizer (AlternatingSylowNormalizer.image P : Set (Equiv.Perm (Fin 5))))) := by
    rw [pCore_prod,d.linearAut_twoCore h,AlternatingSylowNormalizer.twoCore]
  exact (f.quotientPCoreEquivOfSurjective hf hp).trans
    ((QuotientGroup.quotientMulEquivOfEq ht).trans
      ((QuotientGroup.prodMulEquiv _ _).trans
        (QuotientGroup.quotientBot.prodCongr (AlternatingSylowNormalizer.quotientEquiv P))))

/-- The L3(2) times S3 quotient in the point-line output uses the same original K/R. -/
theorem pointLineGroup_core_quotient (h : IsTypeJ4 z) (U : Subgroup G)
    (hR : d.R ≤ U) (hAS : elementaryAbelianMaxJ U ≤ d.S)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G))
    (P : Sylow 2 (alternatingGroup (Fin 5)))
    (hP : d.symmetricImage h (elementaryAbelianMaxJ U) = AlternatingSylowNormalizer.image P) :
    Nonempty ((d.pointLineGroup U ⧸ pCore 2 (d.pointLineGroup U)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) × Equiv.Perm (Fin 3)) := by
  obtain ⟨k⟩ := d.K_quotient_PSL3 h
  exact ⟨(d.pointLineGroupCoreQuotientEquiv h U hR hAS hK P hP).trans
    (((d.KQuotientEquivAut h).symm.trans k).prodCongr (MulEquiv.refl _))⟩

theorem K_le_pointLineGroup (U : Subgroup G)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ U : Set G)) : d.K ≤ d.pointLineGroup U :=
  le_inf d.K_le_normalizer hK

theorem K_normal_in_pointLineGroup (U : Subgroup G) : (d.K.subgroupOf (d.pointLineGroup U)).Normal :=
  d.K_normal.comap (inclusion (show d.pointLineGroup U ≤ normalizer (d.space : Set G) from inf_le_left))


/-- The two-core equality in the ambient group, as required by LineData. -/
theorem pointLineGroup_twoCore_ambient (h : IsTypeJ4 z) (U : Sylow 2 G)
    (hR : d.R ≤ (U : Subgroup G)) (hAS : elementaryAbelianMaxJ (U : Subgroup G) ≤ d.S)
    (hK : d.K ≤ normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G))
    (hc : Nat.card (elementaryAbelianMaxJ (U : Subgroup G)) = 2048)
    (hi : Nat.card (elementaryAbelianMaxJ (U : Subgroup G) ⊓ d.R : Subgroup G) = 512)
    (P : Sylow 2 (alternatingGroup (Fin 5)))
    (hP : d.symmetricImage h (elementaryAbelianMaxJ (U : Subgroup G)) = AlternatingSylowNormalizer.image P) :
    (pCore 2 (d.pointLineGroup (U : Subgroup G))).map (d.pointLineGroup (U : Subgroup G)).subtype =
      elementaryAbelianMaxJ (U : Subgroup G) ⊔ d.R := by
  rw [d.pointLineGroup_twoCore h U hR hAS hK hc hi P hP]
  exact map_subgroupOf_eq_of_le (sup_le
    (le_inf (hAS.trans (Subgroup.centralizer_le_normalizer _)) (elementaryAbelianMaxJ (U : Subgroup G)).le_normalizer)
    (d.R_le_pointLineGroup _ hK))

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
