module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.MarkedQuotient
public import Theory.GroupTheory.WeakBNPair.RegularTree.RootQuotient

/-!
# The marked Tits system on the actual apartment quotient

The carrier is the quotient of the universal amalgam already constructed in
`MarkedQuotient`. Original root factorizations and two-cell endpoint structure
are transported through that same quotient map. Short-distance separation
supplies both local injectivity and the exact full Borel overlap.

The result is a genuine Tits system with exactly two marked simple reflections,
both endpoint images equal to their singleton standard parabolics, and an
amalgam isomorphism preserving both original inclusion squares. The Borel is
the image of the whole original middle group.

This is the conditional algebraic part of DGS (3.7), pp.79–80. Chapter 14
still has to supply the Cartan/apartment/root data, uniqueness and exchange;
(3.6) still has to prove separation. The root-sign and Borel-normalizer
intersection premises below are genuine geometric obligations, not supplied
by the endpoint kernel-disjointness result. Splitness and finite recognition
are not inferred merely from constructing this Tits system.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.GroupTheory
open Theory.GroupTheory.WeakBNPair.RegularTree
open RankTwoAmalgam
universe u
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable (α : RankTwoAmalgam L B R) (T : Set (SourceVertex α)) (n : ℕ)

/-- The full middle subgroup in the universal completion, with its original map. -/
abbrev originalMiddle : Subgroup α.Universal := ((Universal.left α).comp α.left).range

/-- Its image is the full middle image for the already fixed quotient map. -/
theorem originalMiddle_image : (originalMiddle α).map (quotientMap α T n) =
    (middleMap α T n).range :=
  (MonoidHom.range_comp (quotientMap α T n) ((Universal.left α).comp α.left)).symm

/-- Literal endpoint-image identifications, with the source orientation retained. -/
theorem originalEndpoint_image (i : Bool) :
    (Universal.cosetFamily α i).map (quotientMap α T n) =
      if i then (rightMap α T n).range else (leftMap α T n).range := by
  cases i
  · exact (MonoidHom.range_comp (quotientMap α T n) (Universal.left α)).symm
  · exact (MonoidHom.range_comp (quotientMap α T n) (Universal.right α)).symm

variable (hL : Function.Injective α.left) (hR : Function.Injective α.right)
variable (hsep : Separated (sourceRelation α T n) (sourceGraph α) (2 * n))
variable (hn : 1 < n)
variable (hcore : ((Universal.left α).range ⊓ (Universal.right α).range).normalCore = ⊥)

include hL hR hsep hn hcore

/-- Only the original two endpoint restrictions are injective. -/
theorem quotient_injOn_endpoint (i : Bool) :
    Set.InjOn (quotientMap α T n) (Universal.cosetFamily α i) := by
  cases i
  · rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩ he
    exact congrArg (Universal.left α) (leftMap_injective α T n hL hR hsep hn hcore he)
  · rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩ he
    exact congrArg (Universal.right α) (rightMap_injective α T n hL hR hsep hn hcore he)

variable (d : RootQuotientData (quotientMap α T n))
variable (hB : d.B = originalMiddle α)
variable (hP : ∀ i, d.endpoint i = Universal.cosetFamily α i)
variable (hBN : d.B.map (quotientMap α T n) ⊓ d.N.map (quotientMap α T n) =
  (d.B ⊓ d.N).map (quotientMap α T n))

/-- The source quotient supplies the overlap and injectivity premises of the
root-data transport. The root signs remain attached to this same map. -/
def sourceImageData : RootPairData (X := QuotientGroup α T n) :=
  d.imageData (_root_.QuotientGroup.mk'_surjective _)
    (fun i => by rw [hP i]; exact quotient_injOn_endpoint α T n hL hR hsep hn hcore i)
    (by
      rw [hP false, hP true, originalEndpoint_image, originalEndpoint_image,
        hB, originalMiddle_image]
      exact quotient_overlap α T n hL hR hsep hn)
    hBN

/-- The genuine BN-pair on `Universal / kernel`, rather than on an assumed
finite replacement of the universal completion. -/
abbrev sourceTitsSystem :=
  (sourceImageData α T n hL hR hsep hn hcore d hB hP hBN).titsSystem

/-- Precisely the two original chosen lifts mark the Weyl quotient. -/
abbrev sourceSimple (i : Bool) :=
  (sourceImageData α T n hL hR hsep hn hcore d hB hP hBN).simple i

theorem sourceSimple_injective :
    Function.Injective (sourceSimple α T n hL hR hsep hn hcore d hB hP hBN) :=
  RootPairData.simple_injective _

theorem sourceSimple_range :
    Set.range (sourceSimple α T n hL hR hsep hn hcore d hB hP hBN) =
      (sourceTitsSystem α T n hL hR hsep hn hcore d hB hP hBN).S := rfl

theorem sourceTitsSystem_rank_two :
    (sourceTitsSystem α T n hL hR hsep hn hcore d hB hP hBN).S.ncard = 2 :=
  RootPairData.rank_two _

/-- The Borel is the image of the entire original middle group. -/
theorem sourceTitsSystem_borel :
    (sourceTitsSystem α T n hL hR hsep hn hcore d hB hP hBN).B =
      (middleMap α T n).range := by
  change d.B.map (quotientMap α T n) = _
  rw [hB, originalMiddle_image]

/-- Both endpoint equations hold in the same constructed system. -/
theorem sourceTitsSystem_parabolic (i : Bool) :
    (if i then (rightMap α T n).range else (leftMap α T n).range) =
      (sourceTitsSystem α T n hL hR hsep hn hcore d hB hP hBN).standardParabolic
        {sourceSimple α T n hL hR hsep hn hcore d hB hP hBN i} := by
  rw [← originalEndpoint_image]
  have he := (sourceImageData α T n hL hR hsep hn hcore d hB hP hBN).endpoint_eq_standardParabolic i
  change (d.endpoint i).map (quotientMap α T n) = _ at he
  simpa only [hP i] using he

/-- The original Cartan intersection maps to the actual BN intersection. -/
theorem sourceTitsSystem_cartan :
    (sourceTitsSystem α T n hL hR hsep hn hcore d hB hP hBN).B ⊓
      (sourceTitsSystem α T n hL hR hsep hn hcore d hB hP hBN).N =
        (d.B ⊓ d.N).map (quotientMap α T n) := hBN

/-- The source amalgam is marked into the two standard parabolics and the
actual Borel, using the literal original endpoint and middle maps. -/
noncomputable def markedStandardIso :
    RankTwoAmalgam.Iso α
      (RankTwoAmalgam.ofSubgroups
        ((sourceTitsSystem α T n hL hR hsep hn hcore d hB hP hBN).standardParabolic
          {sourceSimple α T n hL hR hsep hn hcore d hB hP hBN false})
        (sourceTitsSystem α T n hL hR hsep hn hcore d hB hP hBN).B
        ((sourceTitsSystem α T n hL hR hsep hn hcore d hB hP hBN).standardParabolic
          {sourceSimple α T n hL hR hsep hn hcore d hB hP hBN true})
        ((sourceTitsSystem α T n hL hR hsep hn hcore d hB hP hBN).B_le_standardParabolic _)
        ((sourceTitsSystem α T n hL hR hsep hn hcore d hB hP hBN).B_le_standardParabolic _)) where
  left := (MonoidHom.ofInjective (leftMap_injective α T n hL hR hsep hn hcore)).trans
    (MulEquiv.subgroupCongr (sourceTitsSystem_parabolic α T n hL hR hsep hn hcore d hB hP hBN false))
  right := (MonoidHom.ofInjective (rightMap_injective α T n hL hR hsep hn hcore)).trans
    (MulEquiv.subgroupCongr (sourceTitsSystem_parabolic α T n hL hR hsep hn hcore d hB hP hBN true))
  middle := (MonoidHom.ofInjective (f := middleMap α T n)
    ((leftMap_injective α T n hL hR hsep hn hcore).comp hL)).trans
      (MulEquiv.subgroupCongr (sourceTitsSystem_borel α T n hL hR hsep hn hcore d hB hP hBN).symm)
  left_commutes b := by apply Subtype.ext; rfl
  right_commutes b := by
    apply Subtype.ext
    exact (DFunLike.congr_fun (quotient_compatible α T n) b).symm

@[simp] theorem markedStandardIso_left_apply (x : L) :
    ((markedStandardIso α T n hL hR hsep hn hcore d hB hP hBN).left x : QuotientGroup α T n) =
      quotientMap α T n (Universal.left α x) := rfl

@[simp] theorem markedStandardIso_right_apply (x : R) :
    ((markedStandardIso α T n hL hR hsep hn hcore d hB hP hBN).right x : QuotientGroup α T n) =
      quotientMap α T n (Universal.right α x) := rfl

@[simp] theorem markedStandardIso_middle_apply (b : B) :
    ((markedStandardIso α T n hL hR hsep hn hcore d hB hP hBN).middle b : QuotientGroup α T n) =
      quotientMap α T n (Universal.left α (α.left b)) := rfl

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
