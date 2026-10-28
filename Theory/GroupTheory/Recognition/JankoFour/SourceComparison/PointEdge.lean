module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.EdgeTwist
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PointFlags
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PlaneFlags

/-!
# Comparing the full original pointwise edge fixers

The point-line flag and its marked involution recover the original
three-space as the marker orbit. The intrinsic commutator description of Q
then transports all seven centralizer cores and their join K. Centralizing
the same space transports the actual S∩M. Sylow conjugacy there aligns the
cubics in B=K N_(S∩M)(Y), producing the full embedded edge-fixer image.

The final theorem constructs the independent point and plane comparisons
for one edge, taking the target reversal to be the image of the original t.
Both central attachments and the six-cover and M24 markings are retained.
Simultaneous agreement of these edge-preserving maps and the full reversal
equation remain further steps; neither is assumed here.

Source: Aschbacher--Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), (8.3)--(8.4), pp.606--607,
DOI 10.1007/BF01232280.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu MathieuCode
open scoped Pointwise

private theorem radical_map_le {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) : (solvableRadical A).map e.toMonoidHom ≤ solvableRadical B := by
  let : ((solvableRadical A).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ e.surjective
  let : Group.IsSolvable ((solvableRadical A).map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective _)
  exact le_solvableRadical _ inferInstance inferInstance

private theorem radical_map_equiv {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) : (solvableRadical A).map e.toMonoidHom=solvableRadical B := by
  refine le_antisymm (radical_map_le e) ?_
  intro b hb
  have he := radical_map_le e.symm (mem_map_of_mem e.symm.toMonoidHom hb)
  exact ⟨e.symm b,he,e.apply_symm_apply b⟩

private theorem core_conjugate {A : Type*} [Group A] (M : Subgroup A) (k : M) (q : A) :
    ((ambientCore q).subgroupOf M).map (MulAut.conj k).toMonoidHom =
      (ambientCore ((k : A)*q*(k : A)⁻¹)).subgroupOf M := by
  ext m
  constructor
  · rintro ⟨u,hu,rfl⟩
    have he := mem_map_of_mem (MulAut.conj (k : A)).toMonoidHom
      (show (u : A) ∈ ambientCore q from hu)
    rw [ambientCore_map] at he
    exact he
  · intro hm
    refine ⟨k⁻¹*m*k,?_,?_⟩
    · have he := mem_map_of_mem (MulAut.conj (k : A)⁻¹).toMonoidHom
        (show (m : A) ∈ ambientCore ((k : A)*q*(k : A)⁻¹) from hm)
      rw [ambientCore_map] at he
      change (k : A)⁻¹*(m : A)*((k : A)⁻¹)⁻¹ ∈
        ambientCore ((k : A)⁻¹*((k : A)*q*(k : A)⁻¹)*((k : A)⁻¹)⁻¹) at he
      have hc : (k : A)⁻¹*((k : A)*q*(k : A)⁻¹)*((k : A)⁻¹)⁻¹=q := by group
      rw [hc,inv_inv] at he
      exact he
    · change k*(k⁻¹*m*k)*k⁻¹=m
      group

variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
variable {z : G} {z' : G'} {h : IsTypeJ4 z} {h' : IsTypeJ4 z'}
variable (a : SourceIncidence.LocalData h) (a' : SourceIncidence.LocalData h')

private noncomputable def pointOverlapEquiv (φ : a.P.M ≃* a'.P.M)
    (hz : (φ ⟨z,marker_mem_point a⟩ : G')=z') : PlaneOverlap a ≃* PlaneOverlap a' :=
  (overlapPlacement a).symm.trans (((φ.subgroupMap (pointOverlap a)).trans
    (MulEquiv.subgroupCongr (pointEquiv_overlap a a' φ hz))).trans (overlapPlacement a'))

/-- Marker-preserving point maps carry the actual extraspecial core. -/
theorem pointMap_core (φ : a.P.M ≃* a'.P.M)
    (hz : (φ ⟨z,marker_mem_point a⟩ : G')=z') :
    ((ambientCore z).subgroupOf a.P.M).map φ.toMonoidHom=(ambientCore z').subgroupOf a'.P.M := by
  let e := pointOverlapEquiv a a' φ hz
  have he : ((core z).subgroupOf (PlaneOverlap a)).map e.toMonoidHom =
      (core z').subgroupOf (PlaneOverlap a') := by
    rw [←overlap_core_eq_radical_commutator a,←overlap_core_eq_radical_commutator a',
      map_commutator,pCore_map_iso,radical_map_equiv]
  have forward (m : a.P.M) (hm : (m : G) ∈ ambientCore z) : (φ m : G') ∈ ambientCore z' := by
    let i : PlaneOverlap a := ⟨⟨m,ambientCore_le z hm⟩,m.property⟩
    have hi : i ∈ (core z).subgroupOf (PlaneOverlap a) := by
      obtain ⟨q,hq,hqv⟩ := hm
      change i.val ∈ core z
      exact (show q=i.val from Subtype.ext hqv) ▸ hq
    have hx := mem_map_of_mem e.toMonoidHom hi
    rw [he] at hx
    exact ⟨(e i).val,hx,rfl⟩
  apply eq_of_le_of_card_ge
  · rintro _ ⟨m,hm,rfl⟩
    exact forward m hm
  · rw [card_map_of_injective φ.injective]
    have hle (a : SourceIncidence.LocalData h) : ambientCore z ≤ a.P.M := by
      rintro _ ⟨q,hq,rfl⟩
      exact overlap_cubicLift_le a (core_le_twoThreeCore h hq)
    have hle' : ambientCore z' ≤ a'.P.M := by
      rintro _ ⟨q,hq,rfl⟩
      exact overlap_cubicLift_le a' (core_le_twoThreeCore h' hq)
    rw [Nat.card_congr (subgroupOfEquivOfLe (hle a)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hle').toEquiv]
    change Nat.card ((core z').map (centralizer z').subtype) ≤
      Nat.card ((core z).map (centralizer z).subtype)
    rw [card_map_of_injective (centralizer z).subtype_injective,
      card_map_of_injective (centralizer z').subtype_injective,h.core_card,h'.core_card]

private theorem marker_orbit_in_point_line (v : G) (hv : v ∈ a.d.space) (hne : v ≠ 1) :
    ∃ k : a.P.M, (k : G) ∈ a.L.G₂ ∧ (k : G)*z*(k : G)⁻¹=v := by
  obtain ⟨n,hn,he⟩ := a.d.normalizer_transitive v hv hne
  obtain ⟨k,hk,s,hs,hks⟩ := a.d.normalizer_product h n hn
  have hsz : s*z*s⁻¹=z := by
    rw [←hs z (a.d.markedPoint 0).property,mul_inv_cancel_right]
  refine ⟨⟨k,a.K_le_point hk⟩,a.line_normalizer.symm ▸ a.d.K_le_normalizer hk,?_⟩
  calc
    k*z*k⁻¹ = k*(s*z*s⁻¹)*k⁻¹ := by rw [hsz]
    _ = (k*s)*z*(k*s)⁻¹ := by group
    _ = v := by rw [hks,he]

/-- The three-space is recovered from its marker and the literal point-line
intersection, so every comparison preserving that flag preserves the space. -/
theorem pointMap_space (φ : a.P.M ≃* a'.P.M)
    (hz : (φ ⟨z,marker_mem_point a⟩ : G')=z')
    (hL : (a.L.G₂.subgroupOf a.P.M).map φ.toMonoidHom=a'.L.G₂.subgroupOf a'.P.M) :
    (a.d.space.subgroupOf a.P.M).map φ.toMonoidHom=a'.d.space.subgroupOf a'.P.M := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨v,hv,rfl⟩
    by_cases hv1 : (v : G)=1
    · have he : v=1 := Subtype.ext hv1
      rw [he,map_one]
      exact one_mem _
    obtain ⟨k,hk,hkv⟩ := marker_orbit_in_point_line a v hv hv1
    have hk' := mem_map_of_mem φ.toMonoidHom (show k ∈ a.L.G₂.subgroupOf a.P.M from hk)
    rw [hL] at hk'
    have hn : (φ k : G') ∈ normalizer (a'.d.space : Set G') := a'.line_normalizer ▸ hk'
    have he : k*⟨z,marker_mem_point a⟩*k⁻¹=v := Subtype.ext hkv
    have he' := congrArg (fun m : a.P.M => (φ m : G')) he
    simp only [map_mul,map_inv,coe_mul,coe_inv,hz] at he'
    change (φ v : G') ∈ a'.d.space
    exact he' ▸ (mem_normalizer_iff.mp hn z').mp (a'.d.markedPoint 0).property
  · rw [card_map_of_injective φ.injective,
      Nat.card_congr (subgroupOfEquivOfLe (a.space_le_E.trans a.P.E_le)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (a'.space_le_E.trans a'.P.E_le)).toEquiv,
      show Nat.card a.d.space=8 from a.d.card,show Nat.card a'.d.space=8 from a'.d.card]

/-- The same point comparison carries each of the seven cores, with its
actual central involution as the index. -/
theorem pointMap_seven_core (φ : a.P.M ≃* a'.P.M)
    (hz : (φ ⟨z,marker_mem_point a⟩ : G')=z')
    (v : a.P.M) (hv : (v : G) ∈ a.d.space) (hne : (v : G) ≠ 1) :
    ((ambientCore (v : G)).subgroupOf a.P.M).map φ.toMonoidHom =
      (ambientCore (φ v : G')).subgroupOf a'.P.M := by
  obtain ⟨k,_,hkv⟩ := marker_orbit_in_point_line a v hv hne
  have hm : k*⟨z,marker_mem_point a⟩*k⁻¹=v := Subtype.ext hkv
  have hm' : (φ k : G')*z'*(φ k : G')⁻¹=(φ v : G') := by
    have hh := congrArg (fun m : a.P.M => (φ m : G')) hm
    simpa only [map_mul,map_inv,coe_mul,coe_inv,hz] using hh
  rw [←hkv,←core_conjugate a.P.M k z,Subgroup.map_map]
  have hc : φ.toMonoidHom.comp (MulAut.conj k).toMonoidHom =
      (MulAut.conj (φ k)).toMonoidHom.comp φ.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change φ (k*x*k⁻¹)=φ k*φ x*(φ k)⁻¹
    rw [map_mul,map_mul,map_inv]
  rw [hc,←Subgroup.map_map,pointMap_core a a' φ hz,core_conjugate,hm']

private theorem pointKernel_eq_join :
    a.d.K.subgroupOf a.P.M = ⨆ v : {v : G // v ∈ a.d.space ∧ v ≠ 1},
      (ambientCore v.val).subgroupOf a.P.M := by
  apply Subgroup.map_injective a.P.M.subtype_injective
  rw [map_subgroupOf_eq_of_le a.K_le_point,Subgroup.map_iSup]
  have hle (v : {v : G // v ∈ a.d.space ∧ v ≠ 1}) : ambientCore v.val ≤ a.P.M :=
    (core_le_threeSpaceCores a.d.space v.property.1 v.property.2).trans a.K_le_point
  simp_rw [map_subgroupOf_eq_of_le (hle _)]
  rfl

private theorem pointMap_line_kernel_le (φ : a.P.M ≃* a'.P.M)
    (hz : (φ ⟨z,marker_mem_point a⟩ : G')=z')
    (hL : (a.L.G₂.subgroupOf a.P.M).map φ.toMonoidHom=a'.L.G₂.subgroupOf a'.P.M) :
    (a.d.K.subgroupOf a.P.M).map φ.toMonoidHom ≤ a'.d.K.subgroupOf a'.P.M := by
  rw [pointKernel_eq_join,Subgroup.map_iSup]
  apply iSup_le
  intro v
  let m : a.P.M := ⟨v,a.P.E_le (a.space_le_E v.property.1)⟩
  change ((ambientCore (m : G)).subgroupOf a.P.M).map φ.toMonoidHom ≤ _
  rw [pointMap_seven_core a a' φ hz m v.property.1 v.property.2]
  have hv := mem_map_of_mem φ.toMonoidHom
    (show m ∈ a.d.space.subgroupOf a.P.M from v.property.1)
  rw [pointMap_space a a' φ hz hL] at hv
  have hn : (φ m : G') ≠ 1 := by
    intro he
    have hm : m=1 := φ.injective ((Subtype.ext he).trans φ.map_one.symm)
    exact v.property.2 (congrArg Subtype.val hm)
  exact subgroupOf_mono a'.P.M (core_le_threeSpaceCores a'.d.space hv hn)

private theorem map_symm_eq {A B : Type*} [Group A] [Group B]
    (φ : A ≃* B) (U : Subgroup A) (V : Subgroup B)
    (he : U.map φ.toMonoidHom=V) : V.map φ.symm.toMonoidHom=U := by
  rw [←he,Subgroup.map_map]
  have hid : φ.symm.toMonoidHom.comp φ.toMonoidHom=MonoidHom.id A := by
    ext x
    exact φ.symm_apply_apply x
  rw [hid,Subgroup.map_id]

/-- The actual join of the seven cores is transported by the same point map. -/
theorem pointMap_line_kernel (φ : a.P.M ≃* a'.P.M)
    (hz : (φ ⟨z,marker_mem_point a⟩ : G')=z')
    (hL : (a.L.G₂.subgroupOf a.P.M).map φ.toMonoidHom=a'.L.G₂.subgroupOf a'.P.M) :
    (a.d.K.subgroupOf a.P.M).map φ.toMonoidHom=a'.d.K.subgroupOf a'.P.M := by
  apply le_antisymm (pointMap_line_kernel_le a a' φ hz hL)
  have hz' : (φ.symm ⟨z',marker_mem_point a'⟩ : G)=z := by
    have he : (⟨z',marker_mem_point a'⟩ : a'.P.M)=φ ⟨z,marker_mem_point a⟩ := Subtype.ext hz.symm
    rw [he,φ.symm_apply_apply]
  have hr := pointMap_line_kernel_le a' a φ.symm hz'
    (map_symm_eq φ _ _ hL)
  intro k hk
  exact ⟨φ.symm k,hr (mem_map_of_mem φ.symm.toMonoidHom hk),φ.apply_symm_apply k⟩

private theorem pointCentralizer_eq :
    a.d.S.subgroupOf a.P.M=Subgroup.centralizer (a.d.space.subgroupOf a.P.M : Set a.P.M) := by
  ext m
  constructor
  · intro hm v hv
    exact Subtype.ext (hm (v : G) hv)
  · intro hm v hv
    exact congrArg Subtype.val (hm ⟨v,a.P.E_le (a.space_le_E hv)⟩ hv)

/-- The comparison preserves S∩M through its literal centralizer definition. -/
theorem pointMap_line_centralizer (φ : a.P.M ≃* a'.P.M)
    (hz : (φ ⟨z,marker_mem_point a⟩ : G')=z')
    (hL : (a.L.G₂.subgroupOf a.P.M).map φ.toMonoidHom=a'.L.G₂.subgroupOf a'.P.M) :
    (a.d.S.subgroupOf a.P.M).map φ.toMonoidHom=a'.d.S.subgroupOf a'.P.M := by
  rw [pointCentralizer_eq,pointCentralizer_eq]
  have hspace := pointMap_space a a' φ hz hL
  have he : φ '' (a.d.space.subgroupOf a.P.M : Set a.P.M)=
      (a'.d.space.subgroupOf a'.P.M : Set a'.P.M) := congrArg SetLike.coe hspace
  apply le_antisymm
  · exact (map_centralizer_le_centralizer_image _ φ.toMonoidHom).trans_eq (congrArg Subgroup.centralizer he)
  · intro m hm
    refine ⟨φ.symm m,?_,φ.apply_symm_apply m⟩
    intro v hv
    apply φ.injective
    simpa only [map_mul,φ.apply_symm_apply] using hm (φ v) (he ▸ Set.mem_image_of_mem φ hv)

private noncomputable def centralPointPlacement :
    lineCentralPoint a ≃* a.d.S.subgroupOf a.P.M where
  toFun x := ⟨⟨x,x.property.2⟩,x.property.1⟩
  invFun x := ⟨x.val,⟨x.property,x.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private noncomputable def centralPointEmbedding : lineCentralPoint a →* a.P.M :=
  (a.d.S.subgroupOf a.P.M).subtype.comp (centralPointPlacement a).toMonoidHom

private theorem pointCubic_image (Y : Sylow 3 (lineCentralPoint a)) :
    (((Y : Subgroup (lineCentralPoint a)).map (lineCentralPoint a).subtype).subgroupOf a.P.M) =
      (Y : Subgroup (lineCentralPoint a)).map (centralPointEmbedding a) := by
  apply Subgroup.map_injective a.P.M.subtype_injective
  have hle : (Y : Subgroup (lineCentralPoint a)).map (lineCentralPoint a).subtype ≤ a.P.M :=
    (map_subtype_le _).trans inf_le_right
  rw [map_subgroupOf_eq_of_le hle,Subgroup.map_map]
  rfl

private noncomputable def centralPointEquiv (φ : a.P.M ≃* a'.P.M)
    (hz : (φ ⟨z,marker_mem_point a⟩ : G')=z')
    (hL : (a.L.G₂.subgroupOf a.P.M).map φ.toMonoidHom=a'.L.G₂.subgroupOf a'.P.M) :
    lineCentralPoint a ≃* lineCentralPoint a' :=
  (centralPointPlacement a).trans (((φ.subgroupMap (a.d.S.subgroupOf a.P.M)).trans
    (MulEquiv.subgroupCongr (pointMap_line_centralizer a a' φ hz hL))).trans
      (centralPointPlacement a').symm)

/-- Align the cubic normalizers inside the same S∩M. The conjugator is
constructed by Sylow conjugacy, fixes the marker, and preserves the line flag. -/
theorem exists_point_edge_correction (φ : a.P.M ≃* a'.P.M)
    (hz : (φ ⟨z,marker_mem_point a⟩ : G')=z')
    (hL : (a.L.G₂.subgroupOf a.P.M).map φ.toMonoidHom=a'.L.G₂.subgroupOf a'.P.M)
    (t : G) (ht : t ∈ a.L.G₂) (hnt : t ∉ a.P.M)
    (t' : G') (ht' : t' ∈ a'.L.G₂) (hnt' : t' ∉ a'.P.M) :
    ∃ n : lineCentralPoint a',
      let ψ := φ.trans (MulAut.conj (⟨n,n.property.2⟩ : a'.P.M))
      (ψ ⟨z,marker_mem_point a⟩ : G')=z' ∧
      (a.L.G₂.subgroupOf a.P.M).map ψ.toMonoidHom=a'.L.G₂.subgroupOf a'.P.M ∧
      ((lineEdgeGroup a t).subgroupOf a.P.M).map ψ.toMonoidHom =
        (lineEdgeGroup a' t').subgroupOf a'.P.M := by
  obtain ⟨Y,hY⟩ := exists_lineEdge_point_normalizer a t ht hnt
  obtain ⟨Y',hY'⟩ := exists_lineEdge_point_normalizer a' t' ht' hnt'
  let F := centralPointEquiv a a' φ hz hL
  let P := Y.mapSurjective (f := F.toMonoidHom) F.surjective
  obtain ⟨n,hn⟩ := MulAction.exists_smul_eq (lineCentralPoint a') P Y'
  let nM := centralPointEmbedding a' n
  let ψ := φ.trans (MulAut.conj nM)
  have hnL : nM ∈ a'.L.G₂.subgroupOf a'.P.M := by
    change (n : G') ∈ a'.L.G₂
    rw [a'.line_normalizer]
    exact Subgroup.centralizer_le_normalizer _ n.property.1
  have hψL : (a.L.G₂.subgroupOf a.P.M).map ψ.toMonoidHom = a'.L.G₂.subgroupOf a'.P.M := by
    change (a.L.G₂.subgroupOf a.P.M).map
      ((MulAut.conj nM).toMonoidHom.comp φ.toMonoidHom)=_
    rw [←Subgroup.map_map,hL]
    exact mem_normalizer_iff_map_conj_eq.mp (le_normalizer hnL)
  have hψz : (ψ ⟨z,marker_mem_point a⟩ : G')=z' := by
    change (n : G')*(φ ⟨z,marker_mem_point a⟩ : G')*(n : G')⁻¹=z'
    rw [hz,←n.property.1 z' (a'.d.markedPoint 0).property,mul_inv_cancel_right]
  refine ⟨n,hψz,hψL,?_⟩
  let U := (Y : Subgroup (lineCentralPoint a)).map (lineCentralPoint a).subtype
  let U' := (Y' : Subgroup (lineCentralPoint a')).map (lineCentralPoint a').subtype
  have hYmap : (Y : Subgroup (lineCentralPoint a)).map
      ((MulAut.conj n).toMonoidHom.comp F.toMonoidHom) = (Y' : Subgroup (lineCentralPoint a')) := by
    have he := congrArg Sylow.toSubgroup hn
    change ((Y : Subgroup (lineCentralPoint a)).map F.toMonoidHom).map
      (MulAut.conj n).toMonoidHom = _ at he
    rwa [Subgroup.map_map] at he
  have hU : (U.subgroupOf a.P.M).map ψ.toMonoidHom=U'.subgroupOf a'.P.M := by
    rw [pointCubic_image,pointCubic_image,Subgroup.map_map]
    have he : ψ.toMonoidHom.comp (centralPointEmbedding a) =
        (centralPointEmbedding a').comp ((MulAut.conj n).toMonoidHom.comp F.toMonoidHom) := by
      apply MonoidHom.ext
      intro x
      rfl
    rw [he,←Subgroup.map_map,hYmap]
  change ((lineEdgeGroup a t).subgroupOf a.P.M).map ψ.toMonoidHom = _
  rw [hY,hY',Subgroup.map_sup,Subgroup.map_inf _ _ _ ψ.injective,
    pointMap_line_kernel a a' ψ hψz hψL,pointMap_line_centralizer a a' ψ hψz hψL,
    map_equiv_normalizer_eq,hU]

/-- Source (8.4), including the full embedded edge fixer. A single point
isomorphism preserves the marker and both flags and transports the actual
edge tM to the specified target edge t'M at the subgroup level. -/
theorem exists_point_edge_equiv
    (t : G) (ht : t ∈ a.L.G₂) (hnt : t ∉ a.P.M)
    (t' : G') (ht' : t' ∈ a'.L.G₂) (hnt' : t' ∉ a'.P.M) :
    ∃ (g : M24) (φ : a.P.M ≃* a'.P.M),
      g • a.trio.parts=a'.trio.parts ∧
      g • a.sextet.parts=a'.sextet.parts ∧
      (∀ m, a'.P.projection (φ m)=g*a.P.projection m*g⁻¹) ∧
      (φ ⟨z,marker_mem_point a⟩ : G')=z' ∧
      ((centralizer z).subgroupOf a.P.M).map φ.toMonoidHom=(centralizer z').subgroupOf a'.P.M ∧
      (a.L.G₂.subgroupOf a.P.M).map φ.toMonoidHom=a'.L.G₂.subgroupOf a'.P.M ∧
      (a.d.space.subgroupOf a.P.M).map φ.toMonoidHom=a'.d.space.subgroupOf a'.P.M ∧
      (a.d.K.subgroupOf a.P.M).map φ.toMonoidHom=a'.d.K.subgroupOf a'.P.M ∧
      (a.d.S.subgroupOf a.P.M).map φ.toMonoidHom=a'.d.S.subgroupOf a'.P.M ∧
      ((lineEdgeGroup a t).subgroupOf a.P.M).map φ.toMonoidHom=
        (lineEdgeGroup a' t').subgroupOf a'.P.M := by
  obtain ⟨g,φ,hgL,hgH,hp,hz,_,hL,_⟩ := exists_point_flag_equiv a a'
  obtain ⟨n,hψz,hψL,hψB⟩ := exists_point_edge_correction a a' φ hz hL t ht hnt t' ht' hnt'
  let nM := centralPointEmbedding a' n
  let ψ := φ.trans (MulAut.conj nM)
  have hnL : (nM : G') ∈ a'.L.G₂ := by
    rw [a'.line_normalizer]
    exact Subgroup.centralizer_le_normalizer _ n.property.1
  have hnH : (nM : G') ∈ centralizer z' :=
    a'.d.S_le_point_centralizer (a'.d.markedPoint 0).property n.property.1
  have hpL := (a'.point_line_overlap nM).mp hnL
  have hpH := (a'.point_plane_todd_overlap nM).mp hnH
  refine ⟨a'.P.projection nM*g,ψ,?_,?_,?_,hψz,pointEquiv_overlap a a' ψ hψz,hψL,
    pointMap_space a a' ψ hψz hψL,pointMap_line_kernel a a' ψ hψz hψL,
    pointMap_line_centralizer a a' ψ hψz hψL,hψB⟩
  · rw [mul_smul,hgL,hpL]
  · rw [mul_smul,hgH,hpH]
  · intro m
    change a'.P.projection (nM*φ m*nM⁻¹)=_
    rw [map_mul,map_mul,map_inv,hp]
    group

/-- Construct the independent local comparisons of (8.3)--(8.4) for the
same actual edge. The target reversal is exactly the plane image of t.
Agreement of these two maps is not asserted by this intermediate theorem. -/
theorem exists_local_edge_equivs (d : CubicNormalizerData a) (d' : CubicNormalizerData a')
    (t : centralizer z) (ht : (t : G) ∈ a.L.G₂) (hnt : (t : G) ∉ a.P.M) :
    ∃ (C : cubicCentralizerInH a.e a.X ≃* cubicCentralizerInH a'.e a'.X)
      (n : cubicNormalizerInH a'.e a'.X) (g : M24)
      (φM : a.P.M ≃* a'.P.M) (φH : centralizer z ≃* centralizer z'),
      (∀ c, cubicNativeProjection h' a'.e a'.X (C c)=cubicNativeProjection h a.e a.X c) ∧
      φH planeMarker=planeMarker ∧
      (∀ c : cubicCentralizerInH a.e a.X,
        φH c.val=(cubicNormalizerAction a'.e a'.X n (C c)).val) ∧
      (core z).map φH.toMonoidHom=core z' ∧
      (cubicSylowImage a.e a.X).map φH.toMonoidHom=cubicSylowImage a'.e a'.X ∧
      (a.P.M.subgroupOf (centralizer z)).map φH.toMonoidHom=a'.P.M.subgroupOf (centralizer z') ∧
      (a.L.G₂.subgroupOf (centralizer z)).map φH.toMonoidHom=a'.L.G₂.subgroupOf (centralizer z') ∧
      (φM ⟨z,marker_mem_point a⟩ : G')=z' ∧
      (∀ m, a'.P.projection (φM m)=g*a.P.projection m*g⁻¹) ∧
      ((centralizer z).subgroupOf a.P.M).map φM.toMonoidHom=(centralizer z').subgroupOf a'.P.M ∧
      (a.L.G₂.subgroupOf a.P.M).map φM.toMonoidHom=a'.L.G₂.subgroupOf a'.P.M ∧
      ((lineEdgeGroup a t).subgroupOf a.P.M).map φM.toMonoidHom=
        (lineEdgeGroup a' (φH t)).subgroupOf a'.P.M := by
  obtain ⟨_,C,n,H,_,_,hC,hz,hHC,hQ,hA,_,_,hHI,hHL,_,_⟩ := exists_plane_flag_equiv a a' d d'
  have ht' : (H t : G') ∈ a'.L.G₂ := by
    have hx := mem_map_of_mem H.toMonoidHom (show t ∈ a.L.G₂.subgroupOf (centralizer z) from ht)
    rw [hHL] at hx
    exact hx
  have hnt' : (H t : G') ∉ a'.P.M := by
    intro hx
    have hx' : H t ∈ (a.P.M.subgroupOf (centralizer z)).map H.toMonoidHom := hHI.symm ▸ hx
    exact hnt ((mem_map_iff_mem (f := H.toMonoidHom) H.injective).mp hx')
  obtain ⟨g,M,_,_,hp,hMz,hMI,hML,_,_,_,hB⟩ :=
    exists_point_edge_equiv a a' t ht hnt (H t) ht' hnt'
  exact ⟨C,n,g,M,H,hC,hz,hHC,hQ,hA,hHI,hHL,hMz,hp,hMI,hML,hB⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
