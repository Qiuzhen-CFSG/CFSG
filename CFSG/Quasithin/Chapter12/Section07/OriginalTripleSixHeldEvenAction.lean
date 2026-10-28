module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldEvenParabolic
public import Theory.SpecificGroups.PSL3Four.CentralCover.FullPlaneQuotient
public import Theory.Representation.BinaryInternalFixedSpaceCodimension.CoreFourOffender
public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Irreducible
public import Theory.Representation.BinaryOffender.SimpleSubgroup
import Theory.SpecificGroups.SL2.FieldAutomorphismCore
import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# The actual irreducible normalizer image in the original even branch

The opposite parabolic induces its original A₅ quotient on W. The original
U has image elementary four with fixed codimension two, so this literal A₅
lies in the offender-generated subgroup. Its central four-group supplies a
nonzero fixed vector. Every group, action and kernel comes from the original
source; no bound on the Sylow image is asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem component_conjugate_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G)) (k : G) :
    let H := centralizer ({(t:G)} : Set G)
    let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
    let B := conjugateSpanBy Lt H
    let Bk := B.map (MulAut.conj k).toMonoidHom
    ∃ f : Bk→*Matrix.PSL3Four.PSL, Function.Surjective f ∧ f.ker=center Bk ∧
      Nat.card f.ker=4 ∧ centerIn Bk=(tripleSixPoint D a t).map (MulAut.conj k).toMonoidHom := by
  let H := centralizer ({(t:G)} : Set G)
  let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
  let B := conjugateSpanBy Lt H
  let c := MulAut.conj k
  let Bk := B.map c.toMonoidHom
  obtain ⟨_,hcenter,hV,hn,he⟩ := original_tripleSix_point_identification_at h structural D a t ht heven hout
  let := hn
  obtain ⟨e₀⟩ := he
  let e := (QuotientGroup.quotientMulEquivOfEq hV.symm).trans e₀
  let f := Matrix.PSL3Four.ElementaryParabolic.centerProjection e
  have hf := Matrix.PSL3Four.ElementaryParabolic.centerProjection_surjective e
  have hfk : f.ker=center B := Matrix.PSL3Four.ElementaryParabolic.centerProjection_ker e
  let eb := B.equivMapOfInjective c.toMonoidHom c.injective
  let fk := f.comp eb.symm.toMonoidHom
  have hfkKer : fk.ker=center Bk := by
    ext x
    change f (eb.symm x)=1 ↔ x∈center Bk
    rw [←MonoidHom.mem_ker,hfk]
    constructor
    · intro hx
      have hh := (centerCongr eb ⟨eb.symm x,hx⟩).property
      change eb (eb.symm x)∈center Bk at hh
      simpa only [MulEquiv.apply_symm_apply] using hh
    · intro hx
      exact (centerCongr eb.symm ⟨x,hx⟩).property
  have hcenterK : centerIn Bk=(tripleSixPoint D a t).map c.toMonoidHom := by
    rw [centerIn_eq_map_center,←B.map_embeddedCenter c.toMonoidHom c.injective,
      ←centerIn_eq_map_center,hcenter]
  refine ⟨fk,hf.comp eb.symm.surjective,hfkKer,?_,hcenterK⟩
  rw [hfkKer,←card_map_of_injective Bk.subtype_injective,←centerIn_eq_map_center,
    hcenterK,card_map_of_injective c.injective]
  exact (tripleSixPoint_properties D a t ht).2.2.1

/-- The source's actual full normalizer image is faithful irreducible and
contains the literal A₅ parabolic image in its offender subgroup, with a
nonzero fixed vector for that same A₅. The Sylow-image bound is a later duty. -/
theorem original_tripleSix_escaping_even_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G))
    (hTK : (T : Subgroup G)≤K) :
    let H := centralizer ({(t:G)} : Set G)
    let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
    let B := conjugateSpanBy Lt H
    Nat.card T=512 ∧ ∃ k∈K, ∃ S : Sylow 2 B, ∃ W : Subgroup G,
      ∃ hWe : IsElementaryAbelian 2 W, letI := hWe
      let Bk := B.map (MulAut.conj k).toMonoidHom
      let R := ((S : Subgroup B).map B.subtype).map (MulAut.conj k).toMonoidHom
      let L := (normalizer (W.subgroupOf Bk : Set Bk)).map Bk.subtype
      let I := normalizer (W : Set G)
      let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
      let τ := imageRepresentation ρ
      let A := actionSubgroup ρ (U.subgroupOf I)
      let C := actionSubgroup ρ (L.subgroupOf I)
      U≤R ∧ W≤R ∧ R≤(T : Subgroup G) ∧ Nat.card R=256 ∧ Nat.card W=64 ∧
      W≠U ∧ U⊔W=R ∧ U⊓W=centerIn R ∧ Nat.card (U⊓W : Subgroup G)=16 ∧
      (T : Subgroup G)≤normalizer (R : Set G)⊓I ∧
      L≤I ∧ L.pCoreIn 2=W ∧ Function.Injective τ ∧ τ.IsIrreducible ∧
      Nonempty (C≃*alternatingGroup (Fin 5)) ∧ Nat.card A=4 ∧ IsOffender τ A ∧
      A≤C ∧ C≤offenderSubgroup τ ∧ fixedSpace τ C≠⊥ := by
  let H := centralizer ({(t:G)} : Set G)
  let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
  let B := conjugateSpanBy Lt H
  obtain ⟨hTc,k,hk,S,W,hUR,hWR,hRT,hRc,hWe,hWc,hne,hgen,hint,hZc,hTN,
    hLp,hLc,hLcore,hLcomm,hLC,hLCc,_,hLW,_,hirr⟩ :=
    original_tripleSix_escaping_even_parabolic h structural D a t ht heven hout hTK
  let := hWe
  let c := MulAut.conj k
  let Bk := B.map c.toMonoidHom
  let R := ((S : Subgroup B).map B.subtype).map c.toMonoidHom
  let L := (normalizer (W.subgroupOf Bk : Set Bk)).map Bk.subtype
  let I := normalizer (W : Set G)
  let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
  let τ := imageRepresentation ρ
  let A := actionSubgroup ρ (U.subgroupOf I)
  let C := actionSubgroup ρ (L.subgroupOf I)
  have hRB : R≤Bk := map_mono (map_subtype_le _)
  have hWB : W≤Bk := hWR.trans hRB
  have hTI : (T : Subgroup G)≤I := hTN.trans inf_le_right
  have hRI : R≤I := hRT.trans hTI
  have hRL : R≤L := by
    intro x hx
    refine ⟨⟨x,hRB hx⟩,?_,rfl⟩
    rw [←subgroupOf_normalizer_eq hWB]
    exact hRI hx
  have hUL : U≤L := hUR.trans hRL
  have hWI : W≤I := W.le_normalizer
  obtain ⟨f,hf,hfk,hfkc,hBkC⟩ := component_conjugate_cover h structural D a t ht heven hout k
  have hU : U.map c.toMonoidHom=U := mem_normalizer_iff_map_conj_eq.mp (D.normalizes hk)
  have hCU : centerIn Bk≤U := by
    rw [hBkC]
    exact (map_mono (f := c.toMonoidHom) (tripleSixPoint_properties D a t ht).2.1).trans_eq hU
  have hCR : centerIn Bk≤centerIn R := by
    intro x hx
    exact ⟨hUR (hCU hx),fun y hy => hx.2 y (hRB hy)⟩
  have hCW : centerIn Bk≤W := by rw [←hint] at hCR; exact hCR.trans inf_le_right
  obtain ⟨eL⟩ := Matrix.PSL3Four.FullPlaneNormalizer.embedded_plane_quotient Bk W f hf hfk hfkc hWB hCW hWc
  let eA := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := Matrix.PSL3Four.F)).trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four Matrix.PSL3Four.card_F).some
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let := D.elementary
  have hUc : Nat.card U=64 :=
    (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans Atlas.Codes.hexacode_card
  have hinterc : Nat.card (U⊓W : Subgroup G)=16 := by rwa [hint]
  have hfixed : W⊓centralizer (U : Set G)=U⊓W := by
    rw [hint]
    apply le_antisymm
    · intro x hx
      refine ⟨hWR hx.1,?_⟩
      have hxW : x∈centralizer (W : Set G) := by
        intro w hw
        exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := W)).comm ⟨w,hw⟩ ⟨x,hx.1⟩)
      have hh : x∈centralizer ((U⊔W : Subgroup G) : Set G) := by
        have hUX : U≤centralizer ({x} : Set G) := fun u hu =>
          mem_centralizer_singleton_iff.mpr (hx.2 u hu)
        have hWX : W≤centralizer ({x} : Set G) := fun w hw =>
          mem_centralizer_singleton_iff.mpr (hxW w hw)
        intro r hr
        exact mem_centralizer_singleton_iff.mp ((sup_le hUX hWX) hr)
      rwa [hgen] at hh
    · intro x hx
      have hxW : x∈W := (hint.symm ▸ hx).2
      exact ⟨hxW,fun u hu => hx.2 u (hUR hu)⟩
  obtain ⟨heC,hAc,hA,hAC⟩ := BinaryInternalFixedSpaceCodimension.core_four_offender
    U W I L le_rfl hLW hUL hLcore hLcomm hUc hWc hinterc hfixed (eL.trans eA)
  have hW : W≠⊥ := by intro hh; rw [hh,card_bot] at hWc; omega
  have hi : τ.IsIrreducible := (BinaryInternalFixedSpaceCodimension.irreducible_of_subgroup_minimal
    W I hWI le_rfl hW (fun J hJW hIJ => hirr J hJW ((sup_le hLW hTI).trans hIJ))).2
  obtain ⟨ec⟩ := heC
  let : IsSimpleGroup C := ec.isSimpleGroup
  have hCJ : C≤offenderSubgroup τ := by
    have hh := simple_range_le_offenderSubgroup τ C.subtype (A.subgroupOf C)
      (by rwa [map_subgroupOf_eq_of_le hAC])
    rwa [range_subtype] at hh
  have hCZ : centerIn Bk=centerIn L := hBkC.trans hLC.symm
  have hZne : centerIn Bk≠⊥ := by
    intro hh
    rw [←hCZ,hh,card_bot] at hLCc
    omega
  obtain ⟨⟨z,hz⟩,hzne'⟩ := ne_bot_iff_exists_ne_one.mp hZne
  have hzne : z≠1 := fun he => hzne' (Subtype.ext he)
  have hzc : z∈centralizer (L : Set G) := by
    rw [hCZ] at hz
    exact hz.2
  let v : Additive W := Additive.ofMul ⟨z,hCW hz⟩
  have hv : v∈fixedSpace τ C := by
    rw [fixedSpace_actionSubgroup]
    exact (BinaryInternalFixedSpaceCodimension.mem_invariants W I L le_rfl hLW v).mpr hzc
  have hfixne : fixedSpace τ C≠⊥ := by
    intro hh
    rw [hh] at hv
    have hv0 : v=0 := hv
    exact hzne (congrArg (fun v : Additive W => (v.toMul:G)) hv0)
  exact ⟨hTc,k,hk,S,W,hWe,hUR,hWR,hRT,hRc,hWc,hne,hgen,hint,hinterc,hTN,
    hLW,hLcore,imageRepresentation_injective ρ,hi,⟨ec⟩,hAc,hA,hAC,hCJ,hfixne⟩

end CFSG.Quasithin.Chapter12.Section07
