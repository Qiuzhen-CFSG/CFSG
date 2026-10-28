module
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.Flags
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetRecovery
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace

/-!
# The even section of the M24 code at a sextet

The common column parity defines a hyperplane of the eleven-dimensional
code. Golay recovery maps this ten-dimensional even section onto the binary
hexacode, with kernel exactly the four-dimensional sextet code space. The
map intertwines the full sextet stabilizer with its actual hexacode quotient.

The section is characterized intrinsically: all sextet translations have
displacement in the fixed four-space exactly on this hyperplane. This gives
the coordinates needed to identify an original selected B/U, rather than
replacing the original pair by a model group.

Source: Aschbacher--Smith H.16.1(3) and 8.2.8(4--5), printed pp.402,718,
refs/quasithin.pdf. The Golay and hexacode constructions used here are the
ATLAS port; see Theory.AtlasPort.OtherSporadic.Mathieu.SextetRecovery and
LICENSES/ATLAS.txt for attribution and license.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode.SextetLayers.CoordinateTransport
open Atlas.Codes
open scoped BigOperators
namespace MathieuCode.NormalizedShadowRows.CodeSection

def atlasParity : Atlas.Codes.golay →ₗ[Bit] Bit :=
  (LinearMap.snd Bit P6 Bit).comp
    ((LinearMap.snd Bit hexacode (P6 × Bit)).comp golayEquiv.symm.toLinearMap)

def atlasRecover : Atlas.Codes.golay →ₗ[Bit] hexacode :=
  (LinearMap.fst Bit hexacode (P6 × Bit)).comp golayEquiv.symm.toLinearMap

lemma atlasParity_block (w : Atlas.Codes.golay) (i : HexIndex) :
    atlasParity w = ∑ k, w.val (i,k) := by
  obtain ⟨⟨h,r,ε⟩,rfl⟩ := golayEquiv.surjective w
  calc
    atlasParity (golayEquiv (h,r,ε)) = ε := by simp [atlasParity]
    _ = _ := (golayEncoder_blockParity h r ε i).symm

lemma atlasRecover_block (w : Atlas.Codes.golay) (hw : atlasParity w = 0) (i : HexIndex) :
    (atlasRecover w).val i = blockDecode (fun k => w.val (i,k)) := by
  obtain ⟨⟨h,r,ε⟩,rfl⟩ := golayEquiv.surjective w
  have hε : ε = 0 := by simpa [atlasParity] using hw
  subst ε
  simpa [atlasRecover, golayEquiv_apply, golayEncoder, c0Encoder] using (c0Encoder_decode h r i).symm

def atlasEvenInGolay : C0 →ₗ[Bit] Atlas.Codes.golay :=
  C0.inclusion (fun w hw => ((C0_even_blocks w).mp hw).1)

lemma atlasParity_even (w : C0) : atlasParity (atlasEvenInGolay w) = 0 := by
  rw [atlasParity_block _ (0,0)]
  exact (even_weight_iff _).mp (((C0_even_blocks w.val).mp w.property).2 (0,0))

lemma atlasRecover_even (w : C0) : atlasRecover (atlasEvenInGolay w) = recoverHex w := by
  apply Subtype.ext
  funext i
  rw [atlasRecover_block _ (atlasParity_even w), recoverHex_blocks]
  rfl

def nativeGolayEquiv (S : Sextet) : Atlas.Codes.golay ≃ₗ[Bit] MathieuCode.golay :=
  (nativeWordEquiv S).ofSubmodules _ _ (nativeWordEquiv_golay S)

lemma nativeGolayEquiv_val (S : Sextet) (w : Atlas.Codes.golay) :
    (nativeGolayEquiv S w).val = nativeWordEquiv S w.val := rfl

lemma nativeGolayEquiv_symm_val (S : Sextet) (w : MathieuCode.golay) (p : Omega) :
    ((nativeGolayEquiv S).symm w).val p = w.val (nativePointEquiv S p) := by
  have he := congrArg (fun u : MathieuCode.golay => u.val (nativePointEquiv S p))
    ((nativeGolayEquiv S).apply_symm_apply w)
  simpa only [nativeGolayEquiv_val, nativeWordEquiv_apply, Equiv.symm_apply_apply] using he

lemma codeLine_parity (S : Sextet) :
    codeLine ≤ (atlasParity.comp (nativeGolayEquiv S).symm.toLinearMap).ker := by
  intro w hw
  obtain ⟨c,hc⟩ := (BinaryPermutation.mem_constants_iff w.val).mp hw
  change atlasParity ((nativeGolayEquiv S).symm w) = 0
  rw [atlasParity_block _ (0,0)]
  simp only [nativeGolayEquiv_symm_val, hc, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  change 4 • c = 0
  fin_cases c <;> decide

lemma codeLine_recover (S : Sextet) :
    codeLine ≤ (atlasRecover.comp (nativeGolayEquiv S).symm.toLinearMap).ker := by
  intro w hw
  obtain ⟨c,hc⟩ := (BinaryPermutation.mem_constants_iff w.val).mp hw
  apply Subtype.ext
  funext i
  change (atlasRecover ((nativeGolayEquiv S).symm w)).val i = 0
  have hp : atlasParity ((nativeGolayEquiv S).symm w) = 0 := codeLine_parity S hw
  calc
    (atlasRecover ((nativeGolayEquiv S).symm w)).val i =
        blockDecode (fun k => ((nativeGolayEquiv S).symm w).val (i,k)) :=
      atlasRecover_block _ hp i
    _ = 0 := by simp only [nativeGolayEquiv_symm_val, hc, blockDecode_constant]

def parity (S : Sextet) : Code →ₗ[Bit] Bit :=
  codeLine.liftQ (atlasParity.comp (nativeGolayEquiv S).symm.toLinearMap) (codeLine_parity S)

def recover (S : Sextet) : Code →ₗ[Bit] hexacode :=
  codeLine.liftQ (atlasRecover.comp (nativeGolayEquiv S).symm.toLinearMap) (codeLine_recover S)

lemma parity_mk (S : Sextet) (w : MathieuCode.golay) (i : HexIndex) :
    parity S (codeLine.mkQ w) = ∑ k, w.val (nativePointEquiv S (i,k)) := by
  change atlasParity ((nativeGolayEquiv S).symm w) = _
  rw [atlasParity_block _ i]
  simp only [nativeGolayEquiv_symm_val]

lemma recover_mk (S : Sextet) (w : MathieuCode.golay)
    (hw : parity S (codeLine.mkQ w) = 0) (i : HexIndex) :
    (recover S (codeLine.mkQ w)).val i =
      blockDecode (fun k => w.val (nativePointEquiv S (i,k))) := by
  change (atlasRecover ((nativeGolayEquiv S).symm w)).val i = _
  have hw' : atlasParity ((nativeGolayEquiv S).symm w) = 0 := hw
  rw [atlasRecover_block _ hw']
  simp only [nativeGolayEquiv_symm_val]

def evenSpace (S : Sextet) : Submodule Bit Code := (parity S).ker

lemma even_mk_iff (S : Sextet) (w : MathieuCode.golay) :
    codeLine.mkQ w ∈ evenSpace S ↔ ((nativeGolayEquiv S).symm w).val ∈ C0 := by
  rw [C0_even_blocks]
  constructor
  · intro hw
    refine ⟨((nativeGolayEquiv S).symm w).property,fun i => ?_⟩
    apply (even_weight_iff _).mpr
    exact (atlasParity_block _ i).symm.trans hw
  · intro hw
    change atlasParity ((nativeGolayEquiv S).symm w) = 0
    rw [atlasParity_block _ (0,0)]
    exact (even_weight_iff _).mp (hw.2 (0,0))

lemma recover_kernel (S : Sextet) {v : Code} (hv : v ∈ evenSpace S) :
    recover S v = 0 ↔ v ∈ CodeFlags.sextetCodeSpace S := by
  obtain ⟨w,rfl⟩ := codeLine.mkQ_surjective v
  rw [CodeFlags.sextetCodeSpace_mk_iff]
  constructor
  · intro hz B hB x hx y hy
    obtain ⟨i,hi⟩ := (nativePartEquiv S).surjective ⟨B,hB⟩
    obtain ⟨⟨ix,k⟩,rfl⟩ := (nativePointEquiv S).surjective x
    obtain ⟨⟨iy,l⟩,rfl⟩ := (nativePointEquiv S).surjective y
    have hix : ix = i := (nativePointEquiv_mem_part S (ix,k) i).mp (by simpa [hi] using hx)
    have hiy : iy = i := (nativePointEquiv_mem_part S (iy,l) i).mp (by simpa [hi] using hy)
    subst ix; subst iy
    have hp : ∑ k, w.val (nativePointEquiv S (i,k)) = 0 := (parity_mk S w i).symm.trans hv
    have hd : blockDecode (fun k => w.val (nativePointEquiv S (i,k))) = 0 := by
      rw [←recover_mk S w hv i, hz]; rfl
    have he := even_block_decomposition (fun k => w.val (nativePointEquiv S (i,k))) hp
    rw [hd, map_zero] at he
    exact (congrFun he k).trans (congrFun he l).symm
  · intro hc
    apply Subtype.ext
    funext i
    rw [recover_mk S w hv i]
    have he : (fun k => w.val (nativePointEquiv S (i,k))) =
        fun _ => w.val (nativePointEquiv S (i,0)) := by
      funext k
      exact hc _ (nativePartEquiv S i).property _
        ((nativePointEquiv_mem_part S _ i).mpr rfl) _
        ((nativePointEquiv_mem_part S _ i).mpr rfl)
    rw [he, blockDecode_constant]
    rfl

lemma parity_surjective (S : Sextet) : Function.Surjective (parity S) := by
  intro c
  refine ⟨codeLine.mkQ (nativeGolayEquiv S (golayEquiv (0,0,c))),?_⟩
  change atlasParity ((nativeGolayEquiv S).symm (nativeGolayEquiv S _)) = c
  simp [atlasParity]

lemma evenSpace_finrank (S : Sextet) : Module.finrank Bit (evenSpace S) = 10 := by
  have hd := (parity S).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (parity_surjective S), finrank_code,
    finrank_top, Module.finrank_self] at hd
  change 1 + Module.finrank Bit (evenSpace S) = 11 at hd
  omega

def evenClass (S : Sextet) (w : C0) : Code :=
  codeLine.mkQ (nativeGolayEquiv S (atlasEvenInGolay w))

lemma evenClass_mem (S : Sextet) (w : C0) : evenClass S w ∈ evenSpace S := by
  rw [evenClass,even_mk_iff,(nativeGolayEquiv S).symm_apply_apply]
  exact w.property

lemma recover_evenClass (S : Sextet) (w : C0) : recover S (evenClass S w) = recoverHex w := by
  change atlasRecover ((nativeGolayEquiv S).symm (nativeGolayEquiv S (atlasEvenInGolay w))) = _
  rw [(nativeGolayEquiv S).symm_apply_apply,atlasRecover_even]

lemma evenClass_surjective (S : Sextet) {v : Code} (hv : v ∈ evenSpace S) :
    ∃ w : C0, evenClass S w = v := by
  obtain ⟨w,rfl⟩ := codeLine.mkQ_surjective v
  let z : C0 := ⟨((nativeGolayEquiv S).symm w).val,(even_mk_iff S w).mp hv⟩
  refine ⟨z,?_⟩
  change codeLine.mkQ (nativeGolayEquiv S ((nativeGolayEquiv S).symm w)) = _
  rw [(nativeGolayEquiv S).apply_symm_apply]

lemma evenClass_equivariant (S : Sextet) (s : SextetStabilizer) (w : C0) :
    codeRepresentation (nativeStabilizerEquiv S s).val (evenClass S w) =
      evenClass S (sextetC0Action s w) := by
  rw [evenClass,codeRepresentation_mk,evenClass]
  apply congrArg codeLine.mkQ
  apply Subtype.ext
  funext x
  obtain ⟨p,rfl⟩ := (nativePointEquiv S).surjective x
  have hs : ((nativeStabilizerEquiv S s).val)⁻¹ • nativePointEquiv S p =
      nativePointEquiv S (s.val.val⁻¹ p) := by
    change ((nativeStabilizerEquiv S s)⁻¹).val.val ((nativeMarking S).pointEquiv p) =
      (nativeMarking S).pointEquiv (s.val.val⁻¹ p)
    rw [←map_inv]
    exact nativeStabilizer_coordinates S s⁻¹ p
  change nativeWordEquiv S (atlasEvenInGolay w).val
    (((nativeStabilizerEquiv S s).val)⁻¹ • nativePointEquiv S p) =
      nativeWordEquiv S (sextetC0Action s w).val (nativePointEquiv S p)
  rw [hs]
  simp only [nativeWordEquiv_apply,Equiv.symm_apply_apply]
  rfl

lemma evenSpace_invariant (S : Sextet) (g : sextetStabilizer S)
    {v : Code} (hv : v ∈ evenSpace S) : codeRepresentation g.val v ∈ evenSpace S := by
  obtain ⟨s,rfl⟩ := (nativeStabilizerEquiv S).surjective g
  obtain ⟨w,rfl⟩ := evenClass_surjective S hv
  rw [evenClass_equivariant]
  exact evenClass_mem S _

lemma recover_equivariant (S : Sextet) (g : sextetStabilizer S)
    {v : Code} (hv : v ∈ evenSpace S) :
    recover S (codeRepresentation g.val v) = hexAction (nativeQuotient S g) (recover S v) := by
  obtain ⟨s,rfl⟩ := (nativeStabilizerEquiv S).surjective g
  obtain ⟨w,rfl⟩ := evenClass_surjective S hv
  rw [evenClass_equivariant,recover_evenClass,recover_evenClass,nativeQuotient_apply]
  exact recoverHex_equivariant s w

lemma recover_surjective (S : Sextet) (h : hexacode) :
    ∃ v ∈ evenSpace S, recover S v = h := by
  obtain ⟨w,rfl⟩ := recoverHex_surjective h
  exact ⟨evenClass S w,evenClass_mem S w,recover_evenClass S w⟩

lemma sextetCodeSpace_le_evenSpace (S : Sextet) : CodeFlags.sextetCodeSpace S ≤ evenSpace S := by
  intro v hv
  obtain ⟨w,rfl⟩ := codeLine.mkQ_surjective v
  have hc := (CodeFlags.sextetCodeSpace_mk_iff S w).mp hv
  have he (k : Fin 4) : w.val (nativePointEquiv S ((0,0),k)) =
      w.val (nativePointEquiv S ((0,0),0)) :=
    hc _ (nativePartEquiv S (0,0)).property _
      ((nativePointEquiv_mem_part S _ _).mpr rfl) _
      ((nativePointEquiv_mem_part S _ _).mpr rfl)
  change parity S (codeLine.mkQ w) = 0
  rw [parity_mk S w (0,0)]
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  change 4 • w.val (nativePointEquiv S ((0,0),0)) = 0
  generalize w.val (nativePointEquiv S ((0,0),0)) = c
  fin_cases c <;> decide

private lemma row_translation_constant_parity : ∀ w : Fin 4 → Bit,
    (∀ k l, w (rowLabel.symm (rowLabel k + b)) - w k =
      w (rowLabel.symm (rowLabel l + b)) - w l) → ∑ k, w k = 0 := by decide +kernel

lemma displacement_mem_fourSpace_iff (S : Sextet) (v : Code) :
    (∀ t : Multiplicative hexacode,
      codeRepresentation (nativeTranslation S t).val v - v ∈ CodeFlags.sextetCodeSpace S) ↔
        v ∈ evenSpace S := by
  constructor
  · intro hd
    obtain ⟨w,rfl⟩ := codeLine.mkQ_surjective v
    let t : Multiplicative hexacode := Multiplicative.ofAdd
      ⟨hexEncoder (0,0,1),⟨(0,0,1),rfl⟩⟩
    have hw := hd t⁻¹
    rw [codeRepresentation_mk,←map_sub,CodeFlags.sextetCodeSpace_mk_iff] at hw
    have hg : ((nativeTranslation S t⁻¹).val)⁻¹ = (nativeTranslation S t).val := by
      rw [map_inv,Subgroup.coe_inv,inv_inv]
    have hc (k l : Fin 4) := hw _ (nativePartEquiv S (0,0)).property
      (nativePointEquiv S ((0,0),k)) ((nativePointEquiv_mem_part S _ _).mpr rfl)
      (nativePointEquiv S ((0,0),l)) ((nativePointEquiv_mem_part S _ _).mpr rfl)
    have hp : ∑ k, w.val (nativePointEquiv S ((0,0),k)) = 0 := by
      apply row_translation_constant_parity
      intro k l
      have he := hc k l
      change w.val (((nativeTranslation S t⁻¹).val)⁻¹ • nativePointEquiv S ((0,0),k)) -
        w.val (nativePointEquiv S ((0,0),k)) =
        w.val (((nativeTranslation S t⁻¹).val)⁻¹ • nativePointEquiv S ((0,0),l)) -
        w.val (nativePointEquiv S ((0,0),l)) at he
      rw [hg,CodeFlags.translation_coordinates,CodeFlags.translation_coordinates] at he
      exact he
    change parity S (codeLine.mkQ w) = 0
    rw [parity_mk S w (0,0)]
    exact hp
  · intro hv t
    have hve := evenSpace_invariant S (nativeTranslation S t) hv
    apply (recover_kernel S ((evenSpace S).sub_mem hve hv)).mp
    rw [map_sub,recover_equivariant S (nativeTranslation S t) hv]
    have ht : nativeQuotient S (nativeTranslation S t) = 1 := by
      change nativeTranslation S t ∈ (nativeQuotient S).ker
      rw [nativeQuotient_kernel]
      exact ⟨t,rfl⟩
    rw [ht,map_one]
    exact sub_self _

end MathieuCode.NormalizedShadowRows.CodeSection
