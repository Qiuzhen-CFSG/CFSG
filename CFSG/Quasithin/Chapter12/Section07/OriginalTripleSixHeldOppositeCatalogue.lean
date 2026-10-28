module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositeAction
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositeCore
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.OffenderSubgroup
public import Theory.Representation.BinaryInternalFixedSpaceCodimension.CentricSylowImage
import all CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositeCore
import Theory.GroupTheory.PCoreSurjective
import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Image

/-!
# The complete B.5 source on the original opposite-plane normalizer image

The full normalizer action has exactly the original W as kernel. Its
faithful six-dimensional quotient has Sylow order sixteen, and the original
opposite A₅ is still a literal subgroup of its offender-generated subgroup.
The two-local cover supplies the genuine B.5 classification on that subgroup.
All kernels and the original dihedral map are retained. No row of B.5 is
assumed, and no identification of the full point centralizer is asserted.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_opposite_catalogue
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G))
    (π : T→*DihedralGroup 4) [IsExtraspecial 2 π.ker] (hP : Nat.card π.ker=128) :
    let P := π.ker.map (T : Subgroup G).subtype
    let H := centralizer ({(t:G)} : Set G)
    let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
    let B := conjugateSpanBy Lt H
    ∃ k∈K, ∃ S : Sylow 2 B, ∃ W : Subgroup G,
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
      U⊔W=R ∧ U⊓W=centerIn R ∧ Nat.card (U⊓W : Subgroup G)=16 ∧
      (T : Subgroup G)≤normalizer (R : Set G)⊓I ∧ L≤I ∧ L.pCoreIn 2=W ∧
      centralizer (W : Set G)=W ∧ I.pCoreIn 2=W ∧
      (actionHom ρ).ker=W.subgroupOf I ∧
      Module.finrank (ZMod 2) (Additive W)=6 ∧
      (∀ Q : Sylow 2 (actionImage ρ), Nat.card Q=16) ∧
      Function.Injective τ ∧ τ.IsIrreducible ∧ pCore 2 (actionImage ρ)=⊥ ∧
      Nonempty (ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple (actionImage ρ)) ∧
      ChapterB.SourceInduction.AdequateAlternative (τ.comp (offenderSubgroup τ).subtype) ∧
      Nonempty (C≃*alternatingGroup (Fin 5)) ∧ Nat.card A=4 ∧ IsOffender τ A ∧
      A≤C ∧ C≤offenderSubgroup τ ∧ fixedSpace τ C≠⊥ ∧
      Nat.card (W⊓P : Subgroup G)=16 ∧ centerIn P≤W ∧
      (U⊓P : Subgroup G)≠W⊓P := by
  let H := centralizer ({(t:G)} : Set G)
  let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
  let B := conjugateSpanBy Lt H
  obtain ⟨k,hk,S,W,hWe,hUR,hWR,hRT,hRc,hWc,_,hgen,hint,hIc,hTN,hLI,hLcore,
    hf,hi,heC,hAc,hA,hAC,hCJ,hfix,hWP,hZW,hneq⟩ :=
    original_tripleSix_escaping_opposite_action h structural D a t ht heven hout π hP
  let := hWe
  let Bk := B.map (MulAut.conj k).toMonoidHom
  let L := (normalizer (W.subgroupOf Bk : Set Bk)).map Bk.subtype
  let I := normalizer (W : Set G)
  let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
  let τ := imageRepresentation ρ
  let q := actionHom ρ
  have hTW : (T : Subgroup G)≤I := hTN.trans inf_le_right
  have hWT : W≤(T : Subgroup G) := hWR.trans hRT
  have hC := opposite_plane_centralizer h structural D a t ht heven hout W hWT hTW hWc hIc
  obtain ⟨hker,hSc⟩ := BinaryInternalFixedSpaceCodimension.centric_sylow_image_card T W hWT hTW hC
  have hTc := (original_tripleSix_escaping_full_affine_model h structural D a t ht heven hout).1
  have hsyl (Q : Sylow 2 (actionImage ρ)) : Nat.card Q=16 := by
    have hh := hSc Q
    rw [hWc,hTc] at hh
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0<64) hh
  have hdim : Module.finrank (ZMod 2) (Additive W)=6 := by
    apply Nat.pow_right_injective (by decide : 1<2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    change Nat.card W=_ at hh
    simpa only [Nat.card_zmod,hWc] using hh.symm
  let : τ.IsIrreducible := hi
  have hcore := Representation.QuadraticFourGroup.twoCore_eq_bot_of_faithful_irreducible τ hf
  let : IsElementaryAbelian 2 (W.subgroupOf I) := IsElementaryAbelian.subgroupOf W.le_normalizer
  have hqker : IsPGroup 2 q.ker := by
    rw [hker]
    exact IsElementaryAbelian.isPGroup 2 _
  have hcoreI : pCore 2 I=W.subgroupOf I := by
    rw [←q.comap_pCore_of_ker_isPGroup ρ.asGroupHom.rangeRestrict_surjective hqker,
      hcore,MonoidHom.comap_bot]
    exact hker
  have hcoreG : I.pCoreIn 2=W := by
    change (pCore 2 I).map I.subtype=W
    rw [hcoreI,map_subgroupOf_eq_of_le W.le_normalizer]
  have hWne : W≠⊥ := by intro he; rw [he,card_bot] at hWc; omega
  let cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple (actionImage ρ) := {
    Cover := I
    kernel := q.ker
    sqtk := h.simpleQTKE.twoLocal_sqtk ⟨W,hWne,IsElementaryAbelian.isPGroup 2 W,rfl⟩
    equiv := QuotientGroup.quotientKerEquivOfSurjective q ρ.asGroupHom.rangeRestrict_surjective }
  have hc := ChapterB.SourceInduction.offenderSubgroup_adequateAlternative τ hf hcore cover
  exact ⟨k,hk,S,W,hWe,hUR,hWR,hRT,hRc,hWc,hgen,hint,hIc,hTN,hLI,hLcore,
    hC,hcoreG,hker,hdim,hsyl,hf,hi,hcore,⟨cover⟩,hc,heC,hAc,hA,hAC,hCJ,hfix,hWP,hZW,hneq⟩

end CFSG.Quasithin.Chapter12.Section07
