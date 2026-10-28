module
public import Theory.Mathieu.M24.LocalGeometry.TrioNormalizerControl
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Geometry
public import Theory.GroupTheory.PCoreSurjective
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport

/-!
# Native markings of the point-line and point-plane overlaps

The literal image of a point-line overlap in its marked M24 quotient has
order 64512 and two-core of order 64. It contains the image of the original
ambient Sylow two-subgroup. The native trio recognition theorem therefore
identifies it with the stabilizer of an actual trio, without changing the
quotient marking. Since the overlap contains the whole kernel, its inverse
image is exactly the original subgroup.

For the point-plane overlap, equivariance identifies centralizing the
original marker with fixing its cocode vector. When that vector is the
common tetrad class of a sextet, the overlap is exactly the inverse image
of its native stabilizer. Surjectivity gives equality of the images too, and counting the retained
kernel gives the full overlap order 283115520.

The application in MathieuJ4RecognitionApplication.MarkedOverlaps supplies
all hypotheses from the original Mathieu inputs, preserving its Sylow and
conjugator. These results construct the native overlap markings needed in
LocalData. Todd splitting and the hexad overlap in the plane quotient
remain separate source obligations.

Source: Aschbacher--Segev, The uniqueness of groups of type J4, Invent.
Math. 105 (1991), (4.6)--(4.8), printed pp.598--599,
DOI 10.1007/BF01232280; native trio recognition as cited in
Theory.Mathieu.M24.LocalGeometry.TrioNormalizerControl.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode M24LocalGeometry M24LocalGeometry.PairOvergroups
open scoped Pointwise IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
noncomputable section
variable {G : Type*} [Group G] [Finite G]

private def overlapTrioTranslate (T : Trio) (g : M24) : Trio where
  parts := g • T.parts
  card := by rw [Finset.card_smul_finset,T.card]
  octad A hA := by
    obtain ⟨B,hB,rfl⟩ := Finset.mem_smul_finset.mp hA
    have hm : B ∈ (m24Blocks : Set (Finset (Fin 24))) := T.octad B hB
    have him := Set.smul_mem_smul_set (a := (g : Equiv.Perm (Fin 24))) hm
    rw [(mem_M24_iff _).mp g.property] at him
    exact him
  disjoint A hA B hB hne := by
    obtain ⟨C,hC,rfl⟩ := Finset.mem_smul_finset.mp hA
    obtain ⟨D,hD,rfl⟩ := Finset.mem_smul_finset.mp hB
    have hd := T.disjoint C hC D hD (fun he => hne (congrArg (g • ·) he))
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨c,hc,hec⟩ := Finset.mem_smul_finset.mp ha
    obtain ⟨d,hdm,hed⟩ := Finset.mem_smul_finset.mp hb
    have he : c = d := smul_left_cancel g (hec.trans hed.symm)
    exact Finset.disjoint_left.mp hd hc (he ▸ hdm)
  cover := by
    have he : (g • T.parts).biUnion id = g • (T.parts.biUnion id) := by
      simp only [Finset.smul_finset_def,Finset.image_biUnion,Finset.biUnion_image,id_eq]
    rw [he,T.cover,Finset.smul_finset_univ]

/-- Recognize the literal image of a point-line overlap in the original M24 marking. -/
theorem marked_overlap_trio (W J : Subgroup G)
    (hWJ : W ≤ J) (hJN : J ≤ normalizer (W : Set G))
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (hW : IsPGroup 2 W) (hWc : Nat.card W = 2048)
    (U : Sylow 2 G) (hUJ : (U : Subgroup G) ≤ J)
    (hJc : Nat.card J = 132120576) (hQc : Nat.card (pCore 2 J) = 2^17) :
    ∃ T : Trio, (J.subgroupOf (normalizer (W : Set G))).map f = trioStabilizer T ∧
      (trioStabilizer T).comap f = J.subgroupOf (normalizer (W : Set G)) := by
  let q := f.comp (inclusion hJN)
  have hqk : q.ker = W.subgroupOf J := by
    ext j
    change f (inclusion hJN j) = 1 ↔ j.val ∈ W
    change inclusion hJN j ∈ f.ker ↔ _
    rw [hk]
    rfl
  have hkc : Nat.card q.ker = 2048 := by
    rw [hqk,Nat.card_congr (subgroupOfEquivOfLe hWJ).toEquiv,hWc]
  have hc : Nat.card q.range = 64512 := by
    have hh := q.ker.card_mul_index
    rw [index_ker,hkc,hJc] at hh
    omega
  have hqrk : q.rangeRestrict.ker = q.ker := MonoidHom.ker_rangeRestrict q
  have hqc : Nat.card (pCore 2 q.range) = 64 := by
    have hh := q.rangeRestrict.card_pCore_of_ker_isPGroup q.rangeRestrict_surjective
      (show IsPGroup 2 q.rangeRestrict.ker from by rw [hqrk,hqk]; exact hW.comap_subtype)
    rw [hqrk,hkc,hQc] at hh
    norm_num at hh
    omega
  let S := (U.subtype (hUJ.trans hJN)).mapSurjective hf
  have hS : (S : Subgroup M24) ≤ q.range := by
    rintro b ⟨n,hn,rfl⟩
    exact ⟨⟨n.val,hUJ hn⟩,rfl⟩
  have hSc : Nat.card S = 1024 := by
    rw [S.card_eq_multiplicity,m24_order]
    decide +kernel
  have hi : (S : Subgroup M24).relIndex q.range = 63 := by
    have hh := ((S : Subgroup M24).subgroupOf q.range).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hS).toEquiv,hSc,hc] at hh
    change 1024 * (S : Subgroup M24).relIndex q.range = 64512 at hh
    omega
  obtain ⟨g,hg⟩ := TrioRecognition.exists_conjugate_trio S q.range hS
    (by intro he; rw [he,card_bot] at hqc; contradiction) hi
  have ht : q.range = trioStabilizer (overlapTrioTranslate standardTrio g⁻¹) := by
    have hh := congrArg (map (MulAut.conj g⁻¹).toMonoidHom) hg
    rw [map_map] at hh
    have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id M24 := by
      ext x
      simp
    rw [he,map_id] at hh
    exact hh.trans (MulAction.stabilizer_smul_eq_stabilizer_map_conj g⁻¹ standardTrio.parts).symm
  have hr : q.range = (J.subgroupOf (normalizer (W : Set G))).map f := by
    ext b
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨inclusion hJN j,j.property,rfl⟩
    · rintro ⟨n,hn,rfl⟩
      exact ⟨⟨n.val,hn⟩,rfl⟩
  refine ⟨overlapTrioTranslate standardTrio g⁻¹,hr.symm.trans ht,?_⟩
  rw [←ht,hr,comap_map_eq,hk,sup_eq_left]
  exact fun n hn => hWJ hn

omit [Finite G] in
/-- The literal point-plane overlap is the preimage of the native sextet stabilizer. -/
theorem marked_cocode_plane_preimage (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (z : W) (S : Sextet) (hS : E (Additive.ofMul z) = sextetVector S) :
    (Subgroup.centralizer ({(z : G)} : Set G)).subgroupOf (normalizer (W : Set G)) =
      (sextetStabilizer S).comap f := by
  ext n
  change n.val ∈ Subgroup.centralizer ({(z : G)} : Set G) ↔ f n ∈ sextetStabilizer S
  rw [←sextetVector_stabilizer]
  change _ ↔ cocodeRepresentation (f n) (sextetVector S) = sextetVector S
  rw [←hS,←hE,E.injective.eq_iff,Additive.ofMul.injective.eq_iff]
  rw [Subtype.ext_iff]
  change n.val ∈ Subgroup.centralizer ({(z : G)} : Set G) ↔ n.val*z.val*n.val⁻¹=z.val
  rw [mem_centralizer_singleton_iff,mul_inv_eq_iff_eq_mul]

omit [Finite G] in
theorem marked_cocode_plane_image (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (z : W) (S : Sextet) (hS : E (Additive.ofMul z) = sextetVector S) :
    ((Subgroup.centralizer ({(z : G)} : Set G)).subgroupOf (normalizer (W : Set G))).map f =
      sextetStabilizer S := by
  rw [marked_cocode_plane_preimage W f E hE z S hS,map_comap_eq_self]
  rw [f.range_eq_top_of_surjective hf]
  exact le_top

omit [Finite G] in
/-- The actual point-plane overlap has the full sextet-stabilizer order,
retaining the elementary kernel rather than discarding it. -/
theorem marked_cocode_plane_card (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (hWc : Nat.card W = 2048) (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (z : W) (S : Sextet) (hS : E (Additive.ofMul z) = sextetVector S) :
    Nat.card (normalizer (W : Set G) ⊓ Subgroup.centralizer ({(z : G)} : Set G) : Subgroup G) =
      283115520 := by
  let H := normalizer (W : Set G) ⊓ Subgroup.centralizer ({(z : G)} : Set G)
  let q := f.comp (inclusion (show H ≤ normalizer (W : Set G) from inf_le_left))
  have hWH : W ≤ H := by
    refine le_inf W.le_normalizer ?_
    intro w hw
    exact mem_centralizer_singleton_iff.mpr
      (((Commute.all (⟨w,hw⟩ : W) z).map W.subtype).eq)
  have hqk : q.ker = W.subgroupOf H := by
    ext x
    change f (inclusion inf_le_left x) = 1 ↔ x.val ∈ W
    change inclusion inf_le_left x ∈ f.ker ↔ _
    rw [hk]
    rfl
  have hr : q.range =
      ((Subgroup.centralizer ({(z : G)} : Set G)).subgroupOf (normalizer (W : Set G))).map f := by
    ext b
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨inclusion inf_le_left x,x.property.2,rfl⟩
    · rintro ⟨n,hn,rfl⟩
      exact ⟨⟨n.val,n.property,hn⟩,rfl⟩
  have hc : Nat.card (sextetStabilizer S) = 138240 :=
    (Nat.card_congr (SextetLayers.CoordinateTransport.nativeStabilizerEquiv S).toEquiv).symm.trans
      Atlas.Codes.sextetStabilizer_card
  have hh := q.ker.card_mul_index
  rw [index_ker,hr,marked_cocode_plane_image W f hf E hE z S hS,hc,hqk,
    Nat.card_congr (subgroupOfEquivOfLe hWH).toEquiv,hWc] at hh
  exact hh.symm

end
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
