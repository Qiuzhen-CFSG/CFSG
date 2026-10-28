module

public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.LinearSteps
public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.M22Restriction
public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.OctadGeometry.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.OctadGeometry.CentralizerIncidence
public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.OctadGeometry.PairSpan

/-!
# Native K.4.3 and its literal M22 applications

`k4_3_of_earlier_source` proves every clause of K.4.3 from precisely the
native H.16.2(3),(6),(7) inputs: the actual equivariant orthogonal quotient
marking, intrinsic core factorization, centralizer order and elementary
structure, and fixed-space dimensions. All K.4 incidence and span premises
are discharged using `CentralizerIncidence` and `PairSpan`.

Quadraticity puts an actor containing z and d inside both actual displacement
centralizers. Their intersection cannot exceed the generated four-group,
since H.16.2(7) and the six-dimensional displacement span would conflict.
The native pair conjugators then give the full octad-stabilizer conjugacy
conclusion on the code or its dual. The intrinsic core's factorization is
also expressed as a literal set product, retaining relative normality.

For the setwise pair stabilizer {0,9}, the native point-stabilizer calculation
and the retained inner displacement give the exact premises of both M22
ratio consumers. `m22_quadratic_bounds_of_earlier_source` proves K.4.4's
rank-two and codimension-four/five conclusions, and
`m22_ratios_of_earlier_source` supplies the code and cocode ratio bounds.

This is the permitted earlier-source conditional implication. The parent
`qt-k04-mathieu-ratios` discharges the H.16 inputs from
`qt-h16-code-chief-flags` and `qt-h16-code-centralizer-geometry`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), K.4.3--4,
printed pp.458--459, refs/quasithin.pdf.
-/

public section
open Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open CFSG.Quasithin.ChapterH.Section13To16
open MathieuCode
open scoped Pointwise
namespace CFSG.Quasithin.ChapterK.Mathieu.OctadGeometry

/-- Connect the literal pair-stabilizer geometry to both K.4.4 ratio consumers.
This preserves the conditional reduction interface. The theorem
`m22_ratios_of_earlier_source` below discharges both geometric inputs using
CentralizerIncidence and PairSpan. The other inputs are H.16.2(6)--(7). -/
theorem m22_ratios_of_point_stabilizers_and_orthogonal_displacement
    (hdim : ∀ (O : Octad) (z : M24), z ∈ octadKernel O → z ≠ 1 →
      Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4)
    (hD : ∀ (O : Octad) (z : M24), z ∈ octadKernel O → z ≠ 1 →
      IsElementaryAbelian 2 (codeOctadInvolutionCentralizer O z))
    (hfixed : ∀ (O : Octad) (z : M24), z ∈ octadKernel O → z ≠ 1 →
      ∀ B : Subgroup M24, z ∈ B → B ≤ codeOctadInvolutionCentralizer O z →
        Module.finrank (ZMod 2) (fixedSpace codeRepresentation B) = 8 - rank B)
    (hpoint : ∀ (O : Octad) (z : M24), z ∈ octadKernel O → z ≠ 1 →
      ∀ a ∈ codeOctadInvolutionCentralizer O z, ∀ i ∈ O.val,
        a • i = i → a ∈ Subgroup.zpowers z)
    (hspan : ∀ (O : Octad) (z d : M24), z ∈ octadKernel O → z ≠ 1 →
      d ∈ codeOctadInvolutionCentralizer O z → d ∉ Subgroup.zpowers z →
        6 ≤ Module.finrank (ZMod 2)
          (LinearMap.range (displacement codeRepresentation z) ⊔
            LinearMap.range (displacement codeRepresentation d) : Submodule (ZMod 2) Code)) :
    2 ≤ quadraticRatio m22OuterCodeRepresentation ∧
      2 < quadraticRatio m22OuterCocodeRepresentation := by
  refine ⟨m22_code_ratio_of_octad_geometry
    (m22_code_geometry_of_point_stabilizers hdim hfixed hpoint), ?_⟩
  apply m22_cocode_ratio_of_octad_geometry
  apply m22_cocode_geometry_of_point_stabilizers_and_spans hdim hfixed hpoint
  intro O z d hz hz1 hd hdz
  exact (octad_pair_spaces_of_span_lower O z d hz hz1 (hdim O z hz hz1) hd hdz
    (hD O z hz hz1) (hfixed O z hz hz1) (hspan O z d hz hz1 hd hdz)).2.1

/-- K.4.3(3) from the six-space calculation and H.16.2(7). Here P is the
actual octad whose kernel contains d. A larger intersection would fix at
most five dimensions, although it fixes the whole displacement six-space. -/
theorem octad_centralizer_intersection_of_span_lower (O P : Octad) (z d : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hdimz : Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4)
    (hd : d ∈ codeOctadInvolutionCentralizer O z) (hdz : d ∉ Subgroup.zpowers z)
    (hdP : d ∈ octadKernel P)
    (hdimd : Module.finrank (ZMod 2) (codeOctadInvolutionFixed P d) = 4)
    (hD : IsElementaryAbelian 2 (codeOctadInvolutionCentralizer O z))
    (hfixed : ∀ B : Subgroup M24, z ∈ B → B ≤ codeOctadInvolutionCentralizer O z →
      Module.finrank (ZMod 2) (fixedSpace codeRepresentation B) = 8 - rank B)
    (hspan : 6 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (displacement codeRepresentation z) ⊔
        LinearMap.range (displacement codeRepresentation d) : Submodule (ZMod 2) Code)) :
    octadPair z d = codeOctadInvolutionCentralizer O z ⊓ codeOctadInvolutionCentralizer P d := by
  have hd1 : d ≠ 1 := fun he => hdz (he ▸ (Subgroup.zpowers z).one_mem)
  have hzE : z ∈ octadPair z d := Subgroup.subset_closure (by simp)
  have hdE : d ∈ octadPair z d := Subgroup.subset_closure (by simp)
  have hq := (octad_pair_quadratic_commutator O z d hz hz1 hdimz hd hD).1
  have hED := quadratic_le_octad_centralizer O z hz hz1 hdimz _ hzE (Or.inl hq)
  have hEDd := quadratic_le_octad_centralizer P d hdP hd1 hdimd _ hdE (Or.inl hq)
  let B := codeOctadInvolutionCentralizer O z ⊓ codeOctadInvolutionCentralizer P d
  have hEB : octadPair z d ≤ B := le_inf hED hEDd
  have hzB : z ∈ B := hEB hzE
  have hW : LinearMap.range (displacement codeRepresentation z) ⊔
      LinearMap.range (displacement codeRepresentation d) ≤ fixedSpace codeRepresentation B := by
    apply sup_le
    · intro v hv a
      exact a.property.1.2 v ((octad_involution_displacement O z hz hz1 hdimz) ▸ hv)
    · intro v hv a
      exact a.property.2.2 v ((octad_involution_displacement P d hdP hd1 hdimd) ▸ hv)
  have hbound := hspan.trans (Submodule.finrank_mono hW)
  rw [hfixed B hzB inf_le_left] at hbound
  have hrB : rank B ≤ 2 := by omega
  have hnontrivial {H : Subgroup M24} (hzH : z ∈ H) : H ≠ ⊥ := by
    intro he
    exact hz1 (Subgroup.mem_bot.mp (he ▸ hzH))
  have hDz : IsElementaryTwo (codeOctadInvolutionCentralizer O z) :=
    ⟨hnontrivial (octad_involution_mem_centralizer O z),hD⟩
  have hBe := hDz.of_le inf_le_left (hnontrivial hzB)
  have hEe := hDz.of_le hED (hnontrivial hzE)
  have hrE := (octad_pair_rank_fixed O z d hz1 hd hdz hD hfixed).1
  apply Subgroup.eq_of_le_of_card_ge hEB
  rw [hBe.card_eq_two_pow_rank,hEe.card_eq_two_pow_rank,hrE]
  exact Nat.pow_le_pow_right (by decide) hrB


private theorem octad_involution_centralizer_le_stabilizer (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set M24) ≤ octadStabilizer O := by
  have hzfix := (mem_octadPointwiseKernel O z).mp
    (show z ∈ octadPointwiseKernel O by rwa [← octad_core_map_eq_pointwise O])
  obtain ⟨i,hi⟩ := Finset.card_pos.mp
    (show 0 < O.val.card by rw [m24Blocks_card _ O.property]; decide)
  obtain ⟨P,_,hP⟩ := fixed_involution_octad z (octad_involution_order O z hz hz1)
    ⟨i,hzfix i hi⟩
  have he : O.val = P.val := Finset.eq_of_subset_of_card_le
    (fun j hj => (hP j).mp (hzfix j hj))
    (by rw [m24Blocks_card _ P.property,m24Blocks_card _ O.property])
  have hf (j : Fin 24) : z • j = j ↔ j ∈ O.val := by simpa only [he] using hP j
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro j hj
  apply (hf _).mp
  rw [← mul_smul, ← Subgroup.mem_centralizer_singleton_iff.mp hg,
    mul_smul, (hf j).mpr hj]

/-- The H.16.2 core factorization is a literal product, and KO is normal
relative to that core. No ambient M24 normality is asserted. -/
theorem octad_core_product (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hcore : codeInvolutionCore z = octadKernel O ⊔ codeOctadInvolutionCentralizer O z) :
    (codeInvolutionCore z : Set M24) =
      (octadKernel O : Set M24) * (codeOctadInvolutionCentralizer O z : Set M24) ∧
      ((octadKernel O).subgroupOf (codeInvolutionCore z)).Normal := by
  have hCM : codeInvolutionCore z ≤ Subgroup.centralizer ({z} : Set M24) := by
    rintro _ ⟨a,_,rfl⟩
    exact a.property
  have hMO := hCM.trans (octad_involution_centralizer_le_stabilizer O z hz hz1)
  have hnorm : octadStabilizer O ≤ Subgroup.normalizer (octadKernel O : Set M24) := by
    have h := (pCore 2 (octadStabilizer O)).le_normalizer_map (octadStabilizer O).subtype
    intro g hg
    exact h (Subgroup.mem_map.mpr ⟨⟨g,hg⟩,
      Subgroup.le_normalizer_of_normal (Subgroup.mem_top _),rfl⟩)
  have hKN : codeOctadInvolutionCentralizer O z ≤ Subgroup.normalizer (octadKernel O : Set M24) :=
    (show codeOctadInvolutionCentralizer O z ≤ codeInvolutionCore z by
      rw [hcore]; exact le_sup_right).trans (hMO.trans hnorm)
  refine ⟨?_,(Subgroup.normal_subgroupOf_iff_le_normalizer ?_).mpr (hMO.trans hnorm)⟩
  · rw [hcore]
    exact Subgroup.coe_mul_of_right_le_normalizer_left _ _ hKN
  · rw [hcore]
    exact le_sup_left


section EarlierSource
variable
    (hdim : ∀ (O : Octad) (z : M24), z ∈ octadKernel O → z ≠ 1 →
      Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4)
    (hcard : ∀ (O : Octad) (z : M24), z ∈ octadKernel O → z ≠ 1 →
      Nat.card (codeOctadInvolutionCentralizer O z) = 16)
    (hD : ∀ (O : Octad) (z : M24), z ∈ octadKernel O → z ≠ 1 →
      IsElementaryAbelian 2 (codeOctadInvolutionCentralizer O z))
    (hfixed : ∀ (O : Octad) (z : M24), z ∈ octadKernel O → z ≠ 1 →
      ∀ B : Subgroup M24, z ∈ B → B ≤ codeOctadInvolutionCentralizer O z →
        Module.finrank (ZMod 2) (fixedSpace codeRepresentation B) = 8 - rank B)
    (Q : ∀ O : Octad,
      (Code ⧸ codeOctadMoved O) ≃ₗ[ZMod 2] BinaryPermutation.natural O.val)
    (hQ : ∀ (O : Octad) (g : octadStabilizer O) (v : Code),
      Q O ((codeOctadMoved O).mkQ (codeRepresentation g.val v)) =
        BinaryPermutation.naturalRepresentation O.val (CocodeOctad.coordinateAction O g)
          (Q O ((codeOctadMoved O).mkQ v)))

include hdim hcard hD Q hQ in
/-- The K.4.3 pair span is at least six, with point freeness discharged by the
native centralizer action. The inputs are only H.16.2(3),(6). -/
theorem octad_pair_span_of_earlier_source (O : Octad) (z d : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hd : d ∈ codeOctadInvolutionCentralizer O z) (hdz : d ∉ Subgroup.zpowers z) :
    6 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (displacement codeRepresentation z) ⊔
        LinearMap.range (displacement codeRepresentation d) : Submodule (ZMod 2) Code) := by
  apply PairSpan.octad_pair_span_lower O z d hz hz1 (hdim O z hz hz1) hd
    (hD O z hz hz1) (Q O) (hQ O)
  intro i hi hdi
  exact hdz (CentralizerIncidence.octad_centralizer_point_stabilizer O z hz hz1
    (hdim O z hz hz1) (hcard O z hz hz1) d hd i hi hdi)

include hdim hcard hD hfixed Q hQ in
/-- K.4.3(3),(5),(6), with the actual fixed octad of d and no remaining
incidence, fusion or displacement premise. -/
theorem octad_pair_geometry_of_earlier_source (O : Octad) (z d : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hd : d ∈ codeOctadInvolutionCentralizer O z) (hdz : d ∉ Subgroup.zpowers z) :
    ∃ P : Octad, d ∈ octadKernel P ∧ (∀ i : Fin 24, d • i = i ↔ i ∈ P.val) ∧
      octadPair z d = codeOctadInvolutionCentralizer O z ⊓
        codeOctadInvolutionCentralizer P d ∧
      fixedSpace codeRepresentation (octadPair z d) =
        subspaceCommutator codeRepresentation ⊤ (octadPair z d) ∧
      subspaceCommutator codeRepresentation ⊤ (octadPair z d) =
        codeOctadInvolutionFixed O z ⊔ codeOctadInvolutionFixed P d ∧
      Module.finrank (ZMod 2)
        (codeOctadInvolutionFixed O z ⊔ codeOctadInvolutionFixed P d :
          Submodule (ZMod 2) Code) = 6 ∧
      fixedCodim codeRepresentation.dual (octadPair z d) = 6 := by
  obtain ⟨P,hdP,hP⟩ := CentralizerIncidence.octad_centralizer_involution_octad O z hz hz1
    (hdim O z hz hz1) (hcard O z hz hz1) d hd hdz
  have hd1 : d ≠ 1 := fun he => hdz (he ▸ (Subgroup.zpowers z).one_mem)
  have hs := octad_pair_span_of_earlier_source hdim hcard hD Q hQ O z d hz hz1 hd hdz
  have hi := octad_centralizer_intersection_of_span_lower O P z d hz hz1
    (hdim O z hz hz1) hd hdz hdP (hdim P d hdP hd1) (hD O z hz hz1)
    (hfixed O z hz hz1) hs
  obtain ⟨hf,hsix,hdual⟩ := octad_pair_spaces_of_span_lower O z d hz hz1
    (hdim O z hz hz1) hd hdz (hD O z hz hz1) (hfixed O z hz hz1) hs
  have hc := (octad_pair_quadratic_commutator O z d hz hz1
    (hdim O z hz hz1) hd (hD O z hz hz1)).2
  rw [octad_involution_displacement O z hz hz1 (hdim O z hz hz1),
    octad_involution_displacement P d hdP hd1 (hdim P d hdP hd1)] at hc hsix
  exact ⟨P,hdP,hP,hi,hf,hc,hsix,hdual⟩

include hdim hcard hD hfixed Q hQ in
/-- Every noncyclic quadratic actor through z is one of the pairs <z,e>.
Quadraticity confines it to both actual centralizers; their intersection
computed above is the pair. The same argument includes the dual code. -/
theorem quadratic_eq_octad_pair_of_earlier_source (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (A : Subgroup M24) (hzA : z ∈ A)
    (hA : A ∈ quadraticSubgroups codeRepresentation ∪
      quadraticSubgroups codeRepresentation.dual) :
    ∃ e ∈ codeOctadInvolutionCentralizer O z,
      e ∉ Subgroup.zpowers z ∧ A = octadPair z e := by
  have hq : IsQuadratic codeRepresentation A ∨ IsQuadratic codeRepresentation.dual A :=
    hA.elim (fun h => Or.inl h.2.2) (fun h => Or.inr h.2.2)
  have hr : 1 < rank A := hA.elim (fun h => h.2.1) (fun h => h.2.1)
  have hAD := quadratic_le_octad_centralizer O z hz hz1 (hdim O z hz hz1) A hzA hq
  have hex : ∃ e ∈ A, e ∉ Subgroup.zpowers z := by
    by_contra! hn
    have hc := Subgroup.card_le_of_le (show A ≤ Subgroup.zpowers z from hn)
    rw [Nat.card_zpowers, octad_involution_order O z hz hz1] at hc
    have hlog := Nat.log_mono_right (b := 2) hc
    change rank A ≤ 1 at hlog
    omega
  obtain ⟨e,he,hez⟩ := hex
  obtain ⟨P,heP,_,hi,_⟩ :=
    octad_pair_geometry_of_earlier_source hdim hcard hD hfixed Q hQ O z e hz hz1 (hAD he) hez
  have he1 : e ≠ 1 := fun heq => hez (heq ▸ (Subgroup.zpowers z).one_mem)
  have hAD' := quadratic_le_octad_centralizer P e heP he1 (hdim P e heP he1) A he hq
  refine ⟨e,hAD he,hez,le_antisymm (hi ▸ le_inf hAD hAD') ?_⟩
  apply (Subgroup.closure_le _).mpr
  intro a ha
  rcases ha with rfl | rfl <;> assumption

include hdim hcard hD hfixed Q hQ in
/-- The rank-two form of K.4.3(4), used by the M23/M24 ratio assembly. -/
theorem quadratic_rank_two_of_earlier_source (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (A : Subgroup M24) (hzA : z ∈ A)
    (hA : A ∈ quadraticSubgroups codeRepresentation ∪
      quadraticSubgroups codeRepresentation.dual) : rank A = 2 := by
  obtain ⟨e,he,hez,rfl⟩ :=
    quadratic_eq_octad_pair_of_earlier_source hdim hcard hD hfixed Q hQ O z hz hz1 A hzA hA
  exact (octad_pair_rank_fixed O z e hz1 he hez (hD O z hz hz1)
    (hfixed O z hz hz1)).1

include hdim hcard hD hfixed Q hQ in
/-- The full M_O-conjugacy conclusion K.4.3(4), for the code and its dual.
The conjugator can in fact be chosen to centralize the marked z. -/
theorem quadratic_conjugate_octad_pair_of_earlier_source (O : Octad) (z d : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hd : d ∈ codeOctadInvolutionCentralizer O z) (hdz : d ∉ Subgroup.zpowers z)
    (A : Subgroup M24) (hzA : z ∈ A)
    (hA : A ∈ quadraticSubgroups codeRepresentation ∪
      quadraticSubgroups codeRepresentation.dual) :
    ∃ g ∈ octadStabilizer O, MulAut.conj g z = z ∧
      (octadPair z d).map (MulAut.conj g).toMonoidHom = A := by
  obtain ⟨e,he,hez,rfl⟩ :=
    quadratic_eq_octad_pair_of_earlier_source hdim hcard hD hfixed Q hQ O z hz hz1 A hzA hA
  exact CentralizerIncidence.octad_pairs_conjugate O z hz hz1
    (hdim O z hz hz1) (hcard O z hz hz1) d e hd he hdz hez

include hdim hcard hD hfixed Q hQ in
/-- All six clauses of K.4.3 on the literal Mathieu code. The displayed core
factorization, like the other inputs in this section, is precisely the earlier
H.16.2 conclusion. Both new intersections, the classification of quadratic
actors and the common six-space are proved here. The parent source assembly
retains discharge of H.16.2(3),(6),(7). -/
theorem k4_3_of_earlier_source (O : Octad) (z d : M24)
    (hz : z ∈ octadKernel O) (hz1 : z ≠ 1)
    (hcore : codeInvolutionCore z = octadKernel O ⊔ codeOctadInvolutionCentralizer O z)
    (hd : d ∈ codeOctadInvolutionCentralizer O z) (hdz : d ∉ Subgroup.zpowers z) :
    ((codeInvolutionCore z : Set M24) =
      (octadKernel O : Set M24) * (codeOctadInvolutionCentralizer O z : Set M24) ∧
      ((octadKernel O).subgroupOf (codeInvolutionCore z)).Normal ∧
      codeOctadInvolutionCentralizer O z ⊓ octadKernel O = Subgroup.zpowers z ∧
      Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4 ∧
      IsElementaryAbelian 2 (codeOctadInvolutionCentralizer O z) ∧
      Nat.card (codeOctadInvolutionCentralizer O z) = 16) ∧
    (subspaceCommutator codeRepresentation ⊤ (Subgroup.zpowers z) =
      codeOctadInvolutionFixed O z) ∧
    ∃ P : Octad, d ∈ octadKernel P ∧ (∀ i : Fin 24, d • i = i ↔ i ∈ P.val) ∧
      octadPair z d = codeOctadInvolutionCentralizer O z ⊓
        codeOctadInvolutionCentralizer P d ∧
      (∀ A : Subgroup M24, z ∈ A →
        A ∈ quadraticSubgroups codeRepresentation ∪ quadraticSubgroups codeRepresentation.dual →
        ∃ g ∈ octadStabilizer O, MulAut.conj g z = z ∧
          (octadPair z d).map (MulAut.conj g).toMonoidHom = A) ∧
      fixedSpace codeRepresentation (octadPair z d) =
        subspaceCommutator codeRepresentation ⊤ (octadPair z d) ∧
      subspaceCommutator codeRepresentation ⊤ (octadPair z d) =
        codeOctadInvolutionFixed O z ⊔ codeOctadInvolutionFixed P d ∧
      Module.finrank (ZMod 2)
        (codeOctadInvolutionFixed O z ⊔ codeOctadInvolutionFixed P d :
          Submodule (ZMod 2) Code) = 6 ∧
      fixedCodim codeRepresentation.dual (octadPair z d) = 6 := by
  obtain ⟨P,hdP,hP,hi,hspaces⟩ :=
    octad_pair_geometry_of_earlier_source hdim hcard hD hfixed Q hQ O z d hz hz1 hd hdz
  obtain ⟨hproduct,hnormal⟩ := octad_core_product O z hz hz1 hcore
  refine ⟨⟨hproduct,hnormal,octad_centralizer_inf_kernel O z hz hz1 (hfixed O z hz hz1),
    hdim O z hz hz1,hD O z hz hz1,hcard O z hz hz1⟩,
    octad_involution_commutator O z hz hz1 (hdim O z hz hz1),P,hdP,hP,hi,?_,hspaces⟩
  exact quadratic_conjugate_octad_pair_of_earlier_source hdim hcard hD hfixed Q hQ O z d
    hz hz1 hd hdz

include hdim hcard hD hfixed Q hQ in
/-- The geometric premise of the cocode ratio consumer for the literal
setwise pair stabilizer {0,9}. Only the inner involution's displacement is
retained on restriction; no arbitrary lifting of quadraticity is used. -/
theorem m22_cocode_geometry_of_earlier_source :
    ∀ A ∈ quadraticSubgroups m22OuterCodeRepresentation,
      rank A = 2 ∧ ∃ x d : m22PairStabilizer,
        x ∈ A ∧ d ∈ A ∧ orderOf x = 2 ∧ x.val • (0 : Fin 24) = 0 ∧
        Module.finrank (ZMod 2) (LinearMap.range (displacement codeRepresentation x.val) ⊔
          LinearMap.range (displacement codeRepresentation d.val) : Submodule (ZMod 2) Code) = 6 := by
  apply m22_cocode_geometry_of_point_stabilizers_and_spans hdim hfixed
  · intro O z hz hz1 a ha i hi hai
    exact CentralizerIncidence.octad_centralizer_point_stabilizer O z hz hz1
      (hdim O z hz hz1) (hcard O z hz hz1) a ha i hi hai
  · intro O z d hz hz1 hd hdz
    exact (octad_pair_spaces_of_span_lower O z d hz hz1 (hdim O z hz hz1) hd hdz
      (hD O z hz hz1) (hfixed O z hz hz1)
      (octad_pair_span_of_earlier_source hdim hcard hD Q hQ O z d hz hz1 hd hdz)).2.1

include hdim hcard hD hfixed Q hQ in
/-- Both K.4.4 bounds for the literal setwise pair stabilizer. The code
has fixed codimension at least four, and the actual cocode at least five. -/
theorem m22_quadratic_bounds_of_earlier_source :
    (∀ A ∈ quadraticSubgroups m22OuterCodeRepresentation,
      rank A = 2 ∧ 4 ≤ fixedCodim m22OuterCodeRepresentation A) ∧
    (∀ A ∈ quadraticSubgroups m22OuterCocodeRepresentation,
      rank A = 2 ∧ 5 ≤ fixedCodim m22OuterCocodeRepresentation A) := by
  constructor
  · intro A hA
    obtain ⟨hr,hf⟩ := CentralizerIncidence.m22_code_geometry_of_earlier_centralizers
      hdim hcard hfixed A hA
    exact ⟨hr,m22_code_bound_of_fixed_six A hf⟩
  · intro A hA
    have hcode : A ∈ quadraticSubgroups m22OuterCodeRepresentation :=
      ⟨hA.1,hA.2.1,(m22_code_quadratic_iff_cocode A).mpr hA.2.2⟩
    obtain ⟨hr,x,d,hx,hd,hx2,h0,hspan⟩ :=
      m22_cocode_geometry_of_earlier_source hdim hcard hD hfixed Q hQ A hcode
    exact ⟨hr,m22_cocode_bound_of_inner_pair A x d hx hd hx2 h0 hspan⟩

include hdim hcard hD hfixed Q hQ in
/-- The actual M22 code and cocode ratio applications, with every K.4 geometry
premise discharged. The remaining hypotheses are exactly the indicated earlier
native H.16.2 conclusions, retained by the parent Mathieu source assembly. -/
theorem m22_ratios_of_earlier_source :
    2 ≤ quadraticRatio m22OuterCodeRepresentation ∧
      2 < quadraticRatio m22OuterCocodeRepresentation := by
  exact ⟨m22_code_ratio_of_octad_geometry
    (CentralizerIncidence.m22_code_geometry_of_earlier_centralizers hdim hcard hfixed),
    m22_cocode_ratio_of_octad_geometry
      (m22_cocode_geometry_of_earlier_source hdim hcard hD hfixed Q hQ)⟩

end EarlierSource

end CFSG.Quasithin.ChapterK.Mathieu.OctadGeometry
