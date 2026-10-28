module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldEvenAction
public import Theory.Representation.BinaryInternalFixedSpaceCodimension.SylowImageBound
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ElementarySylowEight.Source

/-!
# The original even branch forces a square outside the opposite plane

The actual full normalizer is a two-local SQTK cover of its faithful action
image. The complete B.5 sieve contradicts elementary Sylow image of order at
most eight, because the literal opposite A₅ fixes a nonzero vector in that
irreducible image. Hence an actual element of the original T has square
outside the chosen W. This is an original-source consequence, before the
independent even-affine calculation excludes that square.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

public theorem original_tripleSix_escaping_even_square_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G))
    (hTK : (T : Subgroup G)≤K) :
    ∃ W : Subgroup G, IsElementaryAbelian 2 W ∧ Nat.card W=64 ∧
      W≤(T : Subgroup G) ∧ (T : Subgroup G)≤normalizer (W : Set G) ∧
      Nat.card (U⊓W : Subgroup G)=16 ∧ ∃ x∈(T : Subgroup G), x^2∉W := by
  obtain ⟨hTc,k,_,S,W,hWe,hUR,hWR,hRT,_,hWc,_,_,_,hUWc,hTN,
    _,_,hf,hi,⟨ec⟩,_,_,_,hCJ,hfix⟩ :=
    original_tripleSix_escaping_even_action h structural D a t ht heven hout hTK
  let := hWe
  let H := centralizer ({(t:G)} : Set G)
  let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
  let B := conjugateSpanBy Lt H
  let Bk := B.map (MulAut.conj k).toMonoidHom
  let L := (normalizer (W.subgroupOf Bk : Set Bk)).map Bk.subtype
  let I := normalizer (W : Set G)
  let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
  let τ := imageRepresentation ρ
  let C := actionSubgroup ρ (L.subgroupOf I)
  have hW : W≠⊥ := by intro hh; rw [hh,card_bot] at hWc; omega
  have hWT : W≤(T : Subgroup G) := hWR.trans hRT
  have hTW : (T : Subgroup G)≤I := hTN.trans inf_le_right
  refine ⟨W,hWe,hWc,hWT,hTW,hUWc,?_⟩
  by_contra hs
  push Not at hs
  have hp := BinaryInternalFixedSpaceCodimension.sylow_image_elementary_eight T W hWT hTW hTc hWc hs
  have hb : ChapterB.SourceInduction.ElementarySylowEight.Bound (actionImage ρ) :=
    ChapterB.SourceInduction.ElementarySylowEight.of_sylows (fun P => (hp P).1) (fun P => (hp P).2)
  let q := actionHom ρ
  let cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple (actionImage ρ) := {
    Cover := I
    kernel := q.ker
    sqtk := h.simpleQTKE.twoLocal_sqtk ⟨W,hW,IsElementaryAbelian.isPGroup 2 W,rfl⟩
    equiv := QuotientGroup.quotientKerEquivOfSurjective q ρ.asGroupHom.rangeRestrict_surjective }
  exact hfix (ChapterB.SourceInduction.ElementarySylowEight.fixedSpace_eq_bot_from_source
    τ hf hi cover hb C hCJ ec)

end CFSG.Quasithin.Chapter12.Section07
