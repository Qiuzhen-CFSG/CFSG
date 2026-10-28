module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedThompson
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedPointData
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.LineData
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CocodeContainment
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Defs

/-!
# Compatible local geometry from a marked cocode normalizer

The non-FF cocode argument identifies a conjugate of the actual kernel
with the Thompson subgroup of the common Sylow for the source three-space.
The same centralizer element transports the M24 projection and vector
coordinates. The cocode involution bound places the three-space inside
this kernel, and Thompson weak closure puts all seven point cores in its
normalizer. The previously proved radical and alternating image then give
the line group and the literal trio and sextet images.

The marked point constructor supplies the Todd splitting and exact hexad
preimage in the originally supplied cubic quotient. The index fifteen
places the line pair in that hexad. These facts construct every LocalData
field, retaining the chosen cubic Sylow and both transported Todd markings.
Native.LocalData applies the construction to the literal matrix model.
No splitting, incidence or local-data package is assumed. The hypothesis
of an actual marked cocode normalizer is explicit; constructing it from
arbitrary IsTypeJ4 remains a separate source obligation.

Source: Aschbacher--Segev, The uniqueness of groups of type J4, Invent.
Math. 105 (1991), (4.4)--(4.8), pp.597--599, DOI 10.1007/BF01232280.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open Sporadic.Mathieu MathieuCode M24LocalGeometry
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open LocalGeometry LocalGeometry.LocalSubgroups
variable {G : Type*} [Group G] [Finite G]
variable (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))

private def moveNormalizer (c : MulAut G) :
    normalizer (W : Set G) ≃* normalizer (W.map c.toMonoidHom : Set G) :=
  (c.subgroupMap (normalizer (W : Set G))).trans
    (MulEquiv.subgroupCongr (W.map_equiv_normalizer_eq c))

omit [Finite G] in
include hf hk hE in
private theorem transport (c : MulAut G) :
    let W' := W.map c.toMonoidHom
    let : IsElementaryAbelian 2 W' := IsElementaryAbelian.map c.toMonoidHom
    ∃ (f' : normalizer (W' : Set G) →* M24) (E' : Additive W' ≃ₗ[ZMod 2] Cocode),
      Function.Surjective f' ∧ f'.ker = W'.subgroupOf (normalizer (W' : Set G)) ∧
      (∀ n v, E' (Additive.ofMul (W'.normalizerMonoidHom n v)) =
        cocodeRepresentation (f' n) (E' (Additive.ofMul v))) ∧
      (∀ n, f' (moveNormalizer W c n) = f n) ∧
      (∀ w, E' (Additive.ofMul (c.subgroupMap W w)) = E (Additive.ofMul w)) := by
  let W' := W.map c.toMonoidHom
  let : IsElementaryAbelian 2 W' := IsElementaryAbelian.map c.toMonoidHom
  let e : W ≃* W' := c.subgroupMap W
  let n := moveNormalizer W c
  let f' := f.comp n.symm.toMonoidHom
  let E' := (e.symm.toAdditive.toLinearEquiv (ZMod.map_smul _)).trans E
  refine ⟨f',E',hf.comp n.symm.surjective,?_,?_,?_,?_⟩
  · ext v
    obtain ⟨v,rfl⟩ := n.surjective v
    change f (n.symm (n v)) = 1 ↔ c v.val ∈ W'
    rw [n.symm_apply_apply,←MonoidHom.mem_ker,hk]
    constructor
    · exact fun hv => mem_map_of_mem _ hv
    · rintro ⟨w,hw,he⟩
      change v.val ∈ W
      exact c.injective he ▸ hw
  · intro v w
    obtain ⟨v,rfl⟩ := n.surjective v
    obtain ⟨w,rfl⟩ := e.surjective w
    have he : W'.normalizerMonoidHom (n v) (e w) = e (W.normalizerMonoidHom v w) := by
      apply Subtype.ext
      change c v.val * c w.val * (c v.val)⁻¹ = c (v.val*w.val*v.val⁻¹)
      simp only [map_mul,map_inv]
    rw [he]
    change E (Additive.ofMul (e.symm (e _))) =
      cocodeRepresentation (f (n.symm (n v))) (E (Additive.ofMul (e.symm (e w))))
    rw [e.symm_apply_apply,e.symm_apply_apply,n.symm_apply_apply]
    exact hE v w
  · intro v
    exact congrArg f (n.symm_apply_apply v)
  · intro w
    exact congrArg (fun w : W => E (Additive.ofMul w)) (e.symm_apply_apply w)

attribute [local instance] ThreeSpaceData.R_normal_in_S_intrinsic
include hf hk hE in
/-- All earlier local data from a genuine marked cocode normalizer. -/
theorem marked_cocode_localData (z : W) (sextet : Sextet)
    (hz : E (Additive.ofMul z) = sextetVector sextet)
    (h : IsTypeJ4 (z : G))
    (cubic : CubicAutomorphismQuotient (centralizer (z : G) ⧸ core (z : G)))
    (X : Sylow 3 (CubicLift.subgroup cubic)) :
    ∃ (data : SourceIncidence.LocalData h) (g : centralizer (z : G)),
      data.e = cubic ∧ HEq data.X X ∧ data.P.E = W.map (MulAut.conj (g : G)).toMonoidHom ∧
      data.P.M = (normalizer (W : Set G)).map (MulAut.conj (g : G)).toMonoidHom ∧
      (∀ w : W, data.P.vectorEmbedding (Multiplicative.ofAdd (E (Additive.ofMul w))) =
        MulAut.conj (g : G) w.val) ∧
      ∃ m : normalizer (W : Set G) ≃* data.P.M,
        (∀ n, (m n).val = MulAut.conj (g : G) n.val) ∧
        ∀ n, data.P.projection (m n) = f n := by
  obtain ⟨d⟩ := source_three_space_data h cubic X
  obtain ⟨U,hU,_,hR,hZU,_⟩ := d.exists_common_sylow_structure h
  obtain ⟨g,hJ⟩ := marked_cocode_common_thompson W f hf hk E hE z sextet hz h U
    (hU.trans inf_le_left)
  let c := MulAut.conj (g : G)
  let W' := W.map c.toMonoidHom
  let : IsElementaryAbelian 2 W' := IsElementaryAbelian.map c.toMonoidHom
  change W' = elementaryAbelianMaxJ (U : Subgroup G) at hJ
  obtain ⟨f',E',hf',hk',hE',hfmove,hEmove⟩ := transport W f hf hk E hE c
  let z' := c.subgroupMap W z
  have hzz : (z' : G) = z.val :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property)
  have hz' : E' (Additive.ofMul z') = sextetVector sextet := (hEmove z).trans hz
  have hWcard : Nat.card W' = 2048 := by
    change Nat.card (Additive W') = _
    rw [Nat.card_congr E'.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      finrank_cocode,Nat.card_zmod]
    norm_num
  have hCW : Subgroup.centralizer (W' : Set G) = W' :=
    marked_cocode_selfCentralizing W' f' hk' E' hE'
  let : IsElementaryAbelian 2 d.space := d.elementary
  have hJU : elementaryAbelianMaxJ (U : Subgroup G) ≤ (U : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hWN : W' ≤ normalizer (d.space : Set G) := (hJ.le.trans hJU).trans (hU.trans inf_le_right)
  have hZN : d.space ≤ normalizer (W' : Set G) := by
    rw [hJ]
    exact hZU.trans ((U : Subgroup G).le_normalizer.trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ _))
  have hZC := cocode_small_normalized_centralizes W' d.space f' E'
    (fun n v => hE' n v.toMul) hZN hWN (by have hc : Nat.card d.space = 8 := d.card; omega)
  have hZW : d.space ≤ W' := hZC.trans_eq hCW
  have hWS : W' ≤ d.S :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (Subgroup.centralizer_le hZW)
  have hK : d.K ≤ normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) := by
    change (⨆ t : {t : G // t ∈ d.space ∧ t ≠ 1}, ambientCore t.val) ≤ _
    apply iSup_le
    intro t
    apply ambientCore_le_normalizer_thompson (d.point_type h t.property.1 t.property.2) U
    rw [←hJ]
    exact hZC t.property.1
  have hKW : d.K ≤ normalizer (W' : Set G) := hJ.symm ▸ hK
  obtain ⟨A,hA⟩ := d.elementary_eleven_alternating_sylow h W' hWcard hZW hWS hKW
  have hAS : elementaryAbelianMaxJ (U : Subgroup G) ≤ d.S := hJ ▸ hWS
  have hA' : d.symmetricImage h (elementaryAbelianMaxJ (U : Subgroup G)) =
      AlternatingSylowNormalizer.image A := hJ ▸ hA
  have hBc := d.pointLineGroup_card h _ hR hAS hK A hA'
  have hQc := d.pointLineGroup_twoCore_card h _ hR hAS hK A hA'
  have hWB : W' ≤ d.pointLineGroup (U : Subgroup G) := by
    rw [show W' = elementaryAbelianMaxJ (U : Subgroup G) from hJ]
    exact le_inf (hAS.trans (Subgroup.centralizer_le_normalizer _))
      (elementaryAbelianMaxJ (U : Subgroup G)).le_normalizer
  have hBN : d.pointLineGroup (U : Subgroup G) ≤ normalizer (W' : Set G) := by
    rw [show W' = elementaryAbelianMaxJ (U : Subgroup G) from hJ]
    exact inf_le_right
  have hUB : (U : Subgroup G) ≤ d.pointLineGroup (U : Subgroup G) :=
    le_inf (hU.trans inf_le_right) ((U : Subgroup G).le_normalizer.trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ _))
  obtain ⟨trio,htrio,_⟩ := marked_overlap_trio W' (d.pointLineGroup (U : Subgroup G))
    hWB hBN f' hf' hk' (IsElementaryAbelian.isPGroup 2 W') hWcard U hUB hBc hQc
  have hrel : (d.pointLineGroup (U : Subgroup G)).subgroupOf (normalizer (W' : Set G)) =
      (normalizer (d.space : Set G)).subgroupOf (normalizer (W' : Set G)) := by
    ext n
    change (n.val ∈ normalizer (d.space : Set G) ∧
      n.val ∈ normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G)) ↔ _
    exact and_iff_left (hJ ▸ n.property)
  rw [hrel] at htrio
  have hplane := marked_cocode_plane_card W' f' hf' hk' hWcard E' hE' z' sextet hz'
  have himage := marked_cocode_plane_image W' f' hf' E' hE' z' sextet hz'
  rw [hzz] at hplane himage
  have hplaneJ : Nat.card (normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) ⊓
      centralizer (z : G) : Subgroup G) = 283115520 := hJ ▸ hplane
  have hpi := d.pointPlane_line_index h _ hK hBc hplaneJ
  have ht' : IsTypeJ4 (z' : G) := hzz.symm ▸ h
  have hp' := marked_pointData W' f' hf' hk' E' hE' z' sextet hz' ht'
  rw [hzz] at hp'
  obtain ⟨P,hPc,hPE,hPM,hPq,hPv⟩ := hp' cubic
  have hvec (v : W') : P.vectorEmbedding (Multiplicative.ofAdd (E' (Additive.ofMul v))) = v.val := hPv v
  have hproj (n : P.M) : P.projection n = f' (MulEquiv.subgroupCongr hPM n) := by
    obtain ⟨x,rfl⟩ := P.toddEquiv.surjective n
    change (P.toddEquiv.symm (P.toddEquiv x)).right = _
    rw [P.toddEquiv.symm_apply_apply]
    exact (hPq x).symm
  subst cubic
  have hEU : P.E = elementaryAbelianMaxJ (U : Subgroup G) := hPE.trans hJ
  have hPN : P.M = normalizer (P.E : Set G) := hPM.trans (congrArg (fun W : Subgroup G => normalizer (W : Set G)) hPE.symm)
  have hKP : d.K ≤ P.M := hPM.symm ▸ hKW
  have hpiP : (normalizer (d.space : Set G)).relIndex (P.M ⊓ centralizer (z : G)) = 15 := by
    rw [hPM,show W' = elementaryAbelianMaxJ (U : Subgroup G) from hJ]
    exact hpi
  obtain ⟨line,hLN,hLK,hLS⟩ := d.exists_lineData P h U hPN hEU hR
    (hPE.symm ▸ hZW) (hPE.symm ▸ hWS) hKP A (hPE.symm ▸ hA) hpiP
  let := d.multiplicitySpace_elementary h
  obtain ⟨natA,natF,hnat⟩ := d.exists_multiplicity_natural_equiv h
  have hUM : (U : Subgroup G) ≤ P.M := by
    rw [hPN,hEU]
    exact (U : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
  let data : SourceIncidence.LocalData h := {
    e := P.cubic
    X := X
    d := d
    P := P
    cubic_eq := rfl
    L := line
    point_normalizer := hPN.symm
    line_normalizer := hLN
    K_image := hLK
    S_image := hLS
    T := U
    sylow_le := by
      rw [hLN]
      exact le_inf (le_inf (hU.trans inf_le_left) hUM) (hU.trans inf_le_right)
    E_eq_maxJ := hEU
    space_le_E := hPE.symm ▸ hZW
    E_le_S := hPE.symm ▸ hWS
    alternatingSylow := A
    E_quotient := hPE.symm ▸ hA
    trio := trio
    sextet := sextet
    line_image := by
      rw [hLN]
      ext b
      constructor
      · rintro ⟨n,hn,rfl⟩
        rw [hproj]
        exact htrio ▸ mem_map_of_mem f' (show MulEquiv.subgroupCongr hPM n ∈
          (normalizer (d.space : Set G)).subgroupOf (normalizer (W' : Set G)) from hn)
      · intro hb
        rw [←htrio] at hb
        obtain ⟨n,hn,rfl⟩ := hb
        refine ⟨(MulEquiv.subgroupCongr hPM).symm n,hn,?_⟩
        rw [hproj,MulEquiv.apply_symm_apply]
    plane_image := by
      ext b
      constructor
      · rintro ⟨n,hn,rfl⟩
        rw [hproj]
        exact himage ▸ mem_map_of_mem f' (show MulEquiv.subgroupCongr hPM n ∈
          (centralizer (z : G)).subgroupOf (normalizer (W' : Set G)) from hn)
      · intro hb
        rw [←himage] at hb
        obtain ⟨n,hn,rfl⟩ := hb
        refine ⟨(MulEquiv.subgroupCongr hPM).symm n,hn,?_⟩
        rw [hproj,MulEquiv.apply_symm_apply]
    marker_vector := by rw [←hz']; exact (hvec z').trans hzz
    naturalEquiv := natF
    alternatingEquiv := natA
    natural_equivariant := fun b v => hnat b (Additive.ofMul v) }
  refine ⟨data,g,rfl,HEq.rfl,hPE,hPM.trans (W.map_equiv_normalizer_eq c).symm,?_,?_,?_,?_⟩
  · intro w
    rw [←hEmove w]
    exact hvec (c.subgroupMap W w)
  · exact (moveNormalizer W c).trans (MulEquiv.subgroupCongr hPM.symm)
  · intro n
    rfl
  · intro n
    rw [hproj]
    exact hfmove n
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
