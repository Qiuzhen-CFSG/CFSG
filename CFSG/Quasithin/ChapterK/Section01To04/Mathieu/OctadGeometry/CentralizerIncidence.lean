module

public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.OctadGeometry.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.OctadGeometry.CentralizerIncidence.Certificate
public import Theory.Mathieu.M24.ChapterHStabilizers.Involutions

/-!
# Native centralizer incidence for K.4.3

For a nonidentity element z of the actual octad kernel, H.16.2(6) supplies
four-dimensional Vz and the order sixteen of its pointwise centralizer Dz.
The displacement identification in `Reduction` then puts sixteen explicit
native permutations, conjugated along z, inside Dz. Cardinality proves that
these are all of Dz. Their checked fixed sets give actual octads for every
nonidentity member. Their checked centralizing conjugators identify all pairs
<z,d> outside <z>, and their action on the original octad has point stabilizer
exactly <z>.

Every transport uses the original M24 permutations and the literal
`MathieuCode.codeRepresentation`. The inclusion in an octad kernel uses the
proved equality with the mapped intrinsic two-core. The final theorem applies
the point-stabilizer result to the literal M22 pair stabilizer, adding precisely
H.16.2(7)'s fixed-space formula to obtain rank two and fixed dimension six.

These are conditional K.4 results with the displayed earlier-source inputs.
Their producers are `qt-h16-code-chief-flags` and
`qt-h16-code-centralizer-geometry`; `qt-k04-mathieu-ratios` retains their source
discharge. The parent octad-geometry task retains the full K.4.3 assembly.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), K.4.3--4,
printed pp.458--459 (PDF pp.469--470); H.16.2(6)--(7), printed pp.402--403.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterH.Section13To16
open scoped Pointwise
namespace CFSG.Quasithin.ChapterK.Mathieu.OctadGeometry.CentralizerIncidence
open Certificate

private theorem kernel_fixes (O : Octad) (z : M24) (hz : z ∈ octadKernel O)
    (i : Fin 24) (hi : i ∈ O.val) : z • i = i := by
  have hz' : z ∈ octadPointwiseKernel O := by rwa [← octad_core_map_eq_pointwise O]
  exact (mem_octadPointwiseKernel O z).mp hz' i hi

private theorem marking (O : Octad) (z : M24) (hz : z ∈ octadKernel O)
    (hz1 : z ≠ 1) : ∃ g : M24, MulAut.conj g (element 1) = z := by
  have hc := m24Blocks_card O.val O.property
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < O.val.card by omega)
  rcases M24InvolutionCentralizers.involution_classes z
      (octad_involution_order O z hz hz1) with h | h
  · obtain ⟨g,hg⟩ := isConj_iff.mp h
    exact ⟨g, by rw [element_one]; exact hg⟩
  · have hf := M24ChapterHStabilizers.class2B_fixed_empty h
    have hm := (M24ChapterHStabilizers.mem_fixedPoints z i).mpr (kernel_fixes O z hz i hi)
    rw [hf] at hm
    exact (Finset.notMem_empty _ hm).elim

private theorem fixes_conjugated_displacement (g a b : M24)
    (h : ∀ v : Code, codeRepresentation a (displacement codeRepresentation b v) =
      displacement codeRepresentation b v) (v : Code) :
    codeRepresentation (MulAut.conj g a)
      (displacement codeRepresentation (MulAut.conj g b) v) =
        displacement codeRepresentation (MulAut.conj g b) v := by
  have he := congrArg (codeRepresentation g) (h (codeRepresentation g⁻¹ v))
  simpa only [displacement, LinearMap.sub_apply, LinearMap.id_apply,
    MulAut.conj_apply, map_mul, Module.End.mul_apply, map_sub,
    Representation.inv_self_apply, Representation.self_inv_apply] using he

private theorem transported_mem (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hdim : Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4)
    (g : M24) (hg : MulAut.conj g (element 1) = z) (n : Fin 16) :
    MulAut.conj g (element n) ∈ codeOctadInvolutionCentralizer O z := by
  refine ⟨Subgroup.mem_top _, ?_⟩
  intro v hv
  rw [← octad_involution_displacement O z hz hz1 hdim] at hv
  obtain ⟨w,rfl⟩ := hv
  rw [← hg]
  exact fixes_conjugated_displacement g (element n) (element 1)
    (fixes_code_displacement n) w

private theorem coverage (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hdim : Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4)
    (hcard : Nat.card (codeOctadInvolutionCentralizer O z) = 16)
    (g : M24) (hg : MulAut.conj g (element 1) = z)
    (a : M24) (ha : a ∈ codeOctadInvolutionCentralizer O z) :
    ∃ n : Fin 16, MulAut.conj g (element n) = a := by
  let f : Fin 16 → codeOctadInvolutionCentralizer O z :=
    fun n => ⟨MulAut.conj g (element n), transported_mem O z hz hz1 hdim g hg n⟩
  have hi : Function.Injective f := by
    intro n m he
    exact element_injective ((MulAut.conj g).injective (congrArg Subtype.val he))
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hi, by rw [Nat.card_fin, hcard]⟩).2
  obtain ⟨n,hn⟩ := hs ⟨a,ha⟩
  exact ⟨n,congrArg Subtype.val hn⟩

/-- The native action of Dz on O has no point stabilizer outside <z>.
Only the dimension and order clauses of H.16.2(6) are used. -/
theorem octad_centralizer_point_stabilizer (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hdim : Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4)
    (hcard : Nat.card (codeOctadInvolutionCentralizer O z) = 16)
    (a : M24) (ha : a ∈ codeOctadInvolutionCentralizer O z)
    (i : Fin 24) (hi : i ∈ O.val) (hai : a • i = i) :
    a ∈ Subgroup.zpowers z := by
  obtain ⟨g,hg⟩ := marking O z hz hz1
  obtain ⟨n,rfl⟩ := coverage O z hz hz1 hdim hcard g hg a ha
  have hzi := kernel_fixes O z hz i hi
  rw [← hg] at hzi
  have hz' : element 1 • (g⁻¹ • i) = g⁻¹ • i := by
    simpa only [MulAut.conj_apply, mul_smul, inv_smul_smul] using
      congrArg (fun j : Fin 24 => g⁻¹ • j) hzi
  have ha' : element n • (g⁻¹ • i) = g⁻¹ • i := by
    simpa only [MulAut.conj_apply, mul_smul, inv_smul_smul] using
      congrArg (fun j : Fin 24 => g⁻¹ • j) hai
  rcases Certificate.point_stabilizer n _ hz' ha' with rfl | rfl
  · rw [element_zero, map_one]
    exact (Subgroup.zpowers z).one_mem
  · rw [hg]
    exact Subgroup.mem_zpowers z

private theorem transport_octad (g a : M24) (P : Octad)
    (hf : ∀ i : Fin 24, a • i = i ↔ i ∈ P.val) :
    ∃ Q : Octad, (MulAut.conj g a) ∈ octadKernel Q ∧
      ∀ i : Fin 24, (MulAut.conj g a) • i = i ↔ i ∈ Q.val := by
  let Q : Octad := ⟨g • P.val, by
    have he := (mem_M24_iff g.val).mp g.property
    change g.val • P.val ∈ (m24Blocks : Set (Finset (Fin 24)))
    rw [← he]
    exact Set.smul_mem_smul_set P.property⟩
  have hfixed (i : Fin 24) : (MulAut.conj g a) • i = i ↔ i ∈ Q.val := by
    change _ ↔ i ∈ g • P.val
    rw [Finset.mem_smul_finset]
    constructor
    · intro h
      refine ⟨g⁻¹ • i, (hf _).mp ?_, smul_inv_smul _ _⟩
      simpa only [MulAut.conj_apply, mul_smul, inv_smul_smul] using
        congrArg (fun j : Fin 24 => g⁻¹ • j) h
    · rintro ⟨j,hj,rfl⟩
      simp only [MulAut.conj_apply, mul_smul, inv_smul_smul, (hf j).mpr hj]
  refine ⟨Q, ?_, hfixed⟩
  change _ ∈ (pCore 2 (octadStabilizer Q)).map (octadStabilizer Q).subtype
  rw [octad_core_map_eq_pointwise]
  exact (mem_octadPointwiseKernel Q _).mpr (fun i hi => (hfixed i).mpr hi)

/-- Every element of Dz outside <z> fixes exactly a genuine octad and belongs
to its actual octad kernel. The octad type is proved from native witnesses. -/
theorem octad_centralizer_involution_octad (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hdim : Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4)
    (hcard : Nat.card (codeOctadInvolutionCentralizer O z) = 16)
    (d : M24) (hd : d ∈ codeOctadInvolutionCentralizer O z)
    (hdz : d ∉ Subgroup.zpowers z) :
    ∃ P : Octad, d ∈ octadKernel P ∧ ∀ i : Fin 24, d • i = i ↔ i ∈ P.val := by
  obtain ⟨g,hg⟩ := marking O z hz hz1
  obtain ⟨n,rfl⟩ := coverage O z hz hz1 hdim hcard g hg d hd
  have hn : n ≠ 0 := by
    rintro rfl
    rw [element_zero, map_one] at hdz
    exact hdz (Subgroup.one_mem _)
  obtain ⟨P,hP⟩ := fixed_octad n hn
  exact transport_octad g (element n) P hP

/-- The same native witnesses prove order two and fusion with z in M24. -/
theorem octad_centralizer_involution_fusion (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hdim : Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4)
    (hcard : Nat.card (codeOctadInvolutionCentralizer O z) = 16)
    (d : M24) (hd : d ∈ codeOctadInvolutionCentralizer O z)
    (hdz : d ∉ Subgroup.zpowers z) : orderOf d = 2 ∧ IsConj z d := by
  obtain ⟨P,hP,_⟩ := octad_centralizer_involution_octad O z hz hz1 hdim hcard d hd hdz
  have hd1 : d ≠ 1 := fun he => hdz (he ▸ (Subgroup.zpowers z).one_mem)
  obtain ⟨g,hg⟩ := marking O z hz hz1
  obtain ⟨h,hh⟩ := marking P d hP hd1
  exact ⟨octad_involution_order P d hP hd1,
    (isConj_iff.mpr ⟨g,hg⟩).symm.trans (isConj_iff.mpr ⟨h,hh⟩)⟩

private theorem centralizes_preserves_octad (O : Octad) (z g : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hg : MulAut.conj g z = z) : g ∈ octadStabilizer O := by
  have hc := m24Blocks_card O.val O.property
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < O.val.card by omega)
  obtain ⟨P,hP,hfixed⟩ := fixed_involution_octad z (octad_involution_order O z hz hz1)
    ⟨i,kernel_fixes O z hz i hi⟩
  have he : O.val = P.val := Finset.eq_of_subset_of_card_le
    (fun j hj => (hfixed j).mp (kernel_fixes O z hz j hj))
    (by rw [m24Blocks_card _ P.property, hc])
  have hfix : M24ChapterHStabilizers.fixedPoints z = O.val := by
    ext j
    rw [M24ChapterHStabilizers.mem_fixedPoints, hfixed, he]
  apply MulAction.mem_stabilizer_iff.mpr
  rw [← hfix, ← M24ChapterHStabilizers.fixedPoints_conj, hg]

private theorem conj_comp_apply (g h a : M24) :
    MulAut.conj (g * h) a = MulAut.conj g (MulAut.conj h a) := by
  simp only [MulAut.conj_apply, mul_inv_rev]
  group

private theorem conj_inv_cancel (g a : M24) :
    MulAut.conj g⁻¹ (MulAut.conj g a) = a := by
  simp only [MulAut.conj_apply, inv_inv]
  group

private theorem map_pair (g z d : M24) :
    (octadPair z d).map (MulAut.conj g).toMonoidHom =
      octadPair (MulAut.conj g z) (MulAut.conj g d) := by
  simp only [octadPair, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    MulEquiv.coe_toMonoidHom]

/-- The pairs <z,d> and <z,e> are conjugate by an actual element of C_M(z),
which lies in the original octad stabilizer. -/
theorem octad_pairs_conjugate (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hdim : Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4)
    (hcard : Nat.card (codeOctadInvolutionCentralizer O z) = 16)
    (d e : M24) (hd : d ∈ codeOctadInvolutionCentralizer O z)
    (he : e ∈ codeOctadInvolutionCentralizer O z)
    (hdz : d ∉ Subgroup.zpowers z) (hez : e ∉ Subgroup.zpowers z) :
    ∃ g ∈ octadStabilizer O,
      MulAut.conj g z = z ∧
      (octadPair z d).map (MulAut.conj g).toMonoidHom = octadPair z e := by
  obtain ⟨g,hg⟩ := marking O z hz hz1
  obtain ⟨n,hn⟩ := coverage O z hz hz1 hdim hcard g hg d hd
  obtain ⟨m,hm⟩ := coverage O z hz hz1 hdim hcard g hg e he
  have outside (k : Fin 16) (h : MulAut.conj g (element k) ∉ Subgroup.zpowers z) :
      k ≠ 0 ∧ k ≠ 1 := by
    constructor
    · rintro rfl
      rw [element_zero, map_one] at h
      exact h (Subgroup.one_mem _)
    · rintro rfl
      rw [hg] at h
      exact h (Subgroup.mem_zpowers z)
  have hn' := outside n (hn.symm ▸ hdz)
  have hm' := outside m (hm.symm ▸ hez)
  let c := conjugator m * (conjugator n)⁻¹
  have hc1 : MulAut.conj c (element 1) = element 1 := by
    rw [conj_comp_apply, ← conjugator_centralizes n, conj_inv_cancel,
      conjugator_centralizes]
    exact (conjugator_centralizes n).symm
  have hcn : MulAut.conj c (element n) = element m := by
    rw [conj_comp_apply, ← conjugator_fuses n hn'.1 hn'.2, conj_inv_cancel,
      conjugator_fuses m hm'.1 hm'.2]
  let k := g * c * g⁻¹
  have hkz : MulAut.conj k z = z := by
    rw [← hg, conj_comp_apply, conj_inv_cancel, conj_comp_apply, hc1]
  have hkd : MulAut.conj k d = e := by
    rw [← hn, conj_comp_apply, conj_inv_cancel, conj_comp_apply, hcn, hm]
  exact ⟨k,centralizes_preserves_octad O z k hz hz1 hkz,hkz,
    by rw [map_pair, hkz, hkd]⟩

/-- Discharge the point-stabilizer premise of the literal M22 reduction.
The remaining inputs are precisely H.16.2(6)--(7); there is no extra
K.4 incidence or conjugacy premise. -/
theorem m22_code_geometry_of_earlier_centralizers
    (hdim : ∀ (O : Octad) (z : M24), z ∈ octadKernel O → z ≠ 1 →
      Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4)
    (hcard : ∀ (O : Octad) (z : M24), z ∈ octadKernel O → z ≠ 1 →
      Nat.card (codeOctadInvolutionCentralizer O z) = 16)
    (hfixed : ∀ (O : Octad) (z : M24), z ∈ octadKernel O → z ≠ 1 →
      ∀ B : Subgroup M24, z ∈ B → B ≤ codeOctadInvolutionCentralizer O z →
        Module.finrank (ZMod 2) (fixedSpace codeRepresentation B) = 8 - rank B) :
    ∀ A ∈ quadraticSubgroups m22OuterCodeRepresentation,
      rank A = 2 ∧ Module.finrank (ZMod 2)
        (fixedSpace codeRepresentation (A.map m22PairStabilizer.subtype)) = 6 := by
  apply m22_code_geometry_of_point_stabilizers hdim hfixed
  intro O z hz hz1 a ha i hi hai
  exact octad_centralizer_point_stabilizer O z hz hz1
    (hdim O z hz hz1) (hcard O z hz hz1) a ha i hi hai

end CFSG.Quasithin.ChapterK.Mathieu.OctadGeometry.CentralizerIncidence
