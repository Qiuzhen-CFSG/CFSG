module
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.SignedModel
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.TorusRelations
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus

/-!
# Native torus words and faithful Borel coordinates

The signed presentation's parameterized Weyl and torus words are the existing
folded elementary words, transported through the original central quotient.
Thus the two torus parameters give the native torus equivalence. In particular
their product is multiplicative and injective. Combining this with the native
Borel factorization proves joint injectivity of the six positive coordinates
and the two torus units, the Borel-kernel input to presentation faithfulness.

The fixed field is the actual Frobenius-fixed subfield; no scalar inclusion or
quotient is replaced. These results cover every positive binary exponent.
Source: GLS3 2.3.5 and 2.4.7, with the original folded rank-one words.
-/

@[expose] public noncomputable section
namespace Triality.Standard.RootPresentationRecognition.SignedModel
open Parabolics ConcreteBruhat TorusCoordinates RadicalCoordinates.LeviCommutators
variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

private theorem foldedWeyl_val (T : Parameters) (hp : T.prime = 2)
    (a : Node) (t : RootField T a) :
    toCarrier T (foldedWeylElementary T hp a t) =
      rootElement T hp true a t * rootElement T hp false a (-t⁻¹) * rootElement T hp true a t :=
  ((toCarrier T).map_mul _ _).trans
    (congrArg (fun g => g * rootElement T hp true a t) ((toCarrier T).map_mul _ _))

theorem nA_eq (t : (ExtensionField P)ˣ) :
    (roots n hn).nA t = toCarrier P (foldedWeylElementary P rfl .arms t.val) := by
  have hs := PositiveWeylModel.short_zero P rfl t.val
  have hm := opposition_short_zero P rfl (t⁻¹).val
  have he := congrArg₂ (· * ·) (congrArg₂ (· * ·) hs hm) hs
  change (roots n hn).nA t = _ at he
  have hi : (t⁻¹).val = -t.val⁻¹ :=
    (Units.val_inv_eq_inv_val t).trans (CharTwo.neg_eq t.val⁻¹).symm
  exact he.trans ((congrArg
    (fun u => rootElement P rfl true .arms t.val * rootElement P rfl false .arms u *
      rootElement P rfl true .arms t.val) hi).trans (foldedWeyl_val P rfl .arms t.val).symm)

theorem nB_eq (t : (fixedField P)ˣ) :
    (roots n hn).nB t = toCarrier P (foldedWeylElementary P rfl .central t.val) := by
  have hs := PositiveWeylModel.long_zero P rfl t.val
  have hm := opposition_long_zero P rfl (t⁻¹).val
  have he := congrArg₂ (· * ·) (congrArg₂ (· * ·) hs hm) hs
  change (roots n hn).nB t = _ at he
  have hi : (t⁻¹).val = -t.val⁻¹ :=
    (Units.val_inv_eq_inv_val t).trans (CharTwo.neg_eq t.val⁻¹).symm
  exact he.trans ((congrArg
    (fun u => rootElement P rfl true .central t.val * rootElement P rfl false .central u *
      rootElement P rfl true .central t.val) hi).trans (foldedWeyl_val P rfl .central t.val).symm)

theorem hA_eq (t : (ExtensionField P)ˣ) :
    (roots n hn).hA t = toCarrier P (foldedTorusElementary P rfl .arms t) := by
  change (roots n hn).nA t * (roots n hn).nA 1 = _
  refine (congrArg₂ (· * ·) (nA_eq n hn t) (nA_eq n hn 1)).trans ?_
  have he : foldedWeylElementary P rfl .arms (1 : ExtensionField P) =
      foldedWeylElementary P rfl .arms (-1) :=
    congrArg (foldedWeylElementary P rfl .arms) (CharTwo.neg_eq (1 : ExtensionField P)).symm
  exact (congrArg (fun w => toCarrier P (foldedWeylElementary P rfl .arms t.val) *
    toCarrier P w) he).trans ((toCarrier P).map_mul _ _).symm

theorem hB_eq (t : (fixedField P)ˣ) :
    (roots n hn).hB t = toCarrier P (foldedTorusElementary P rfl .central t) := by
  change (roots n hn).nB t * (roots n hn).nB 1 = _
  refine (congrArg₂ (· * ·) (nB_eq n hn t) (nB_eq n hn 1)).trans ?_
  have he : foldedWeylElementary P rfl .central (1 : fixedField P) =
      foldedWeylElementary P rfl .central (-1) :=
    congrArg (foldedWeylElementary P rfl .central) (CharTwo.neg_eq (1 : fixedField P)).symm
  exact (congrArg (fun w => toCarrier P (foldedWeylElementary P rfl .central t.val) *
    toCarrier P w) he).trans ((toCarrier P).map_mul _ _).symm

/-- The presentation torus word is the existing faithful native torus coordinate. -/
theorem torus_eq (p : TorusParameters n hn) :
    (roots n hn).torus p = (torusMulEquiv P rfl p).val := by
  change (roots n hn).hA p.1 * (roots n hn).hB p.2 = _
  refine (congrArg₂ (· * ·) (hA_eq n hn p.1) (hB_eq n hn p.2)).trans ?_
  exact (map_mul (toCarrier P) _ _).symm

theorem torus_mul (p q : TorusParameters n hn) :
    (roots n hn).torus (p*q) = (roots n hn).torus p * (roots n hn).torus q := by
  simp only [torus_eq]
  exact congrArg Subtype.val (map_mul (torusMulEquiv P rfl) p q)

theorem torus_injective : Function.Injective (roots n hn).torus := by
  intro p q h
  apply (torusMulEquiv P rfl).injective
  exact Subtype.ext ((torus_eq n hn p).symm.trans (h.trans (torus_eq n hn q)))

theorem torus_one : (roots n hn).torus 1 = 1 := by
  rw [torus_eq]
  exact congrArg Subtype.val (map_one (torusMulEquiv P rfl))

/-- The six positive parameters and two torus units are faithful jointly. -/
theorem borel_coordinates_injective : Function.Injective
    (fun z : PositiveParameters n hn × TorusParameters n hn =>
      (nativePositiveRoots n hn).product z.1 * (roots n hn).torus z.2) := by
  intro z w h
  have hU (v : PositiveParameters n hn) : (nativePositiveRoots n hn).product v ∈ unipotent P := by
    rw [← native_positiveClosure n hn]
    exact ((nativePositiveRoots n hn).mem_positiveClosure_iff (native_relations n hn) _).mpr ⟨v,rfl⟩
  have hp : ((⟨(nativePositiveRoots n hn).product z.1,hU z.1⟩ : unipotent P),torusMulEquiv P rfl z.2) =
      (⟨(nativePositiveRoots n hn).product w.1,hU w.1⟩,torusMulEquiv P rfl w.2) := by
    apply (borelEquiv P rfl).injective
    apply Subtype.ext
    simpa only [borelEquiv_val P rfl, ← torus_eq n hn] using h
  apply Prod.ext
  · exact native_product_injective n hn (congrArg (fun p : unipotent P × torus P => p.1.val) hp)
  · exact (torusMulEquiv P rfl).injective (congrArg Prod.snd hp)

end Triality.Standard.RootPresentationRecognition.SignedModel
