module
public import Theory.GroupAction.BinaryA4Pair.NormalizerActors
public import Theory.Representation.BinaryPermutation.SixPolar

/-!
# Natural-module marking of the two symmetric-four actors

Conjugacy of the actual residual actor to the canonical binary A₆ action
retains its change of coordinates. The canonical action is the six-letter
polar action, whose duad coordinates identify it with the literal binary
permutation natural module. Thus group recognition and module recognition
use one group equivalence and satisfy the actual intertwining identity.

Source: Aschbacher–Smith, 14.3.19(4). The normalizer endpoint supplies the
representation mark needed by the A₆-block conclusion.
-/

namespace BinaryA4Pair
open Subgroup Theory.SpecificGroups.SymmetricSix
public theorem HasCanonicalModel.polar
    {W : Type*} [Group W] {P : Subgroup (MulAut W)} (h : HasCanonicalModel P) :
    ∃ (e : P ≃* alternatingGroup (Fin 6)) (q : W ≃* Multiplicative NaturalModule),
      ∀ (g : P) (w : W), (q (g.val w)).toAdd = polarAction (e g).val (q w).toAdd := by
  obtain ⟨b,hb⟩ := h
  let c := ((alternatingGroup (Fin 6)).equivMapOfInjective modelAction
    modelAction_injective).trans (MulEquiv.subgroupCongr modelAction_range)
  let d := (P.equivMapOfInjective (MulAut.congr b).toMonoidHom
    (MulAut.congr b).injective).trans (MulEquiv.subgroupCongr hb)
  let e := d.trans c.symm
  refine ⟨e,b.trans toPolar,?_⟩
  intro g w
  have he : modelAction (e g).val = (MulAut.congr b) g.val := by
    exact congrArg Subtype.val (c.apply_symm_apply (d g))
  have hx := congrArg (fun u : Aut => toPolar (u (b w))) he
  change toPolar (toPolar.symm (polarAut (e g).val (toPolar (b w)))) =
    toPolar (b (g.val (b.symm (b w)))) at hx
  simp only [MulEquiv.apply_symm_apply,MulEquiv.symm_apply_apply] at hx
  exact congrArg Multiplicative.toAdd hx.symm
public theorem HasCanonicalModel.natural
    {W : Type*} [Group W] {P : Subgroup (MulAut W)} (h : HasCanonicalModel P) :
    ∃ (e : P ≃* alternatingGroup (Fin 6))
      (q : W ≃* Multiplicative (BinaryPermutation.natural (Fin 6))),
      ∀ (g : P) (w : W), (q (g.val w)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (e g).val (q w).toAdd := by
  obtain ⟨e,q,hq⟩ := h.polar
  refine ⟨e,q.trans (AddEquiv.toMultiplicative PolarNatural.equiv.toAddEquiv),?_⟩
  intro g w
  change PolarNatural.equiv (q (g.val w)).toAdd =
    BinaryPermutation.naturalRepresentation (Fin 6) (e g).val (PolarNatural.equiv (q w).toAdd)
  rw [hq,PolarNatural.equiv_action]


local notation "S4" => Equiv.Perm (Fin 4)

/-- The residual actor and its literal module have a single natural A₆ marking. -/
public theorem natural_recognition_of_symmetricFour_actors
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W=16) (X Y : Subgroup (MulAut W))
    (eX : X ≃* S4) (eY : Y ≃* S4) (SX : Sylow 2 X) (SY : Sylow 2 Y)
    (hS : (SX : Subgroup X).map X.subtype = (SY : Subgroup Y).map Y.subtype)
    (t : MulAut W) (htX : t∈X) (ht3 : t^3=1)
    (htfixed : ∀ w, t w=w → w=1)
    (hfixed : Nat.card {w : W // ∀ g∈(pResidual 2 Y).map Y.subtype, g w=w}=2) :
    ∃ (e : ((pResidual 2 X).map X.subtype ⊔ (pResidual 2 Y).map Y.subtype :
        Subgroup (MulAut W)) ≃* alternatingGroup (Fin 6))
      (q : W ≃* Multiplicative (BinaryPermutation.natural (Fin 6))),
      ∀ (g : ((pResidual 2 X).map X.subtype ⊔ (pResidual 2 Y).map Y.subtype :
        Subgroup (MulAut W))) (w : W),
        (q (g.val w)).toAdd =
          BinaryPermutation.naturalRepresentation (Fin 6) (e g).val (q w).toAdd :=
  (canonical_model_of_symmetricFour_actors hcard X Y eX eY SX SY hS t htX ht3
    htfixed hfixed).natural

/-- The literal normalizer image acts as the six-letter binary natural module. -/
public theorem natural_recognition_of_normalizer_actors
    {G : Type*} [Group G] [Finite G]
    (A I J S L Y : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A=16)
    (hIA : I≤normalizer (A : Set G)) (hJA : J≤normalizer (A : Set G))
    (hSI : S≤I) (hSJ : S≤J)
    (eI : (A.normalizerMonoidHom.comp (inclusion hIA)).range ≃* S4)
    (eJ : (A.normalizerMonoidHom.comp (inclusion hJA)).range ≃* S4)
    (hS : Nat.card (A.normalizerMonoidHom.comp (inclusion (hSI.trans hIA))).range=8)
    (hpS : IsPGroup 2 S)
    (hL : L=(pResidual 2 I).map I.subtype)
    (hY : Y=(pResidual 2 J).map J.subtype)
    (ht : ∃ t : MulAut A, t∈(A.normalizerMonoidHom.comp (inclusion hIA)).range ∧
      t^3=1 ∧ ∀ a, t a=a → a=1)
    (hfixed : Nat.card (A ⊓ centralizer (Y : Set G) : Subgroup G)=2) :
    ∃ hK : L⊔Y≤normalizer (A : Set G),
      ∃ (e : (A.normalizerMonoidHom.comp (inclusion hK)).range ≃*
        alternatingGroup (Fin 6))
        (q : A ≃* Multiplicative (BinaryPermutation.natural (Fin 6))),
        ∀ (g : (A.normalizerMonoidHom.comp (inclusion hK)).range) (a : A),
          (q (g.val a)).toAdd =
            BinaryPermutation.naturalRepresentation (Fin 6) (e g).val (q a).toAdd := by
  obtain ⟨hK,hc⟩ := canonical_model_of_normalizer_actors A I J S L Y hA hIA hJA hSI hSJ
    eI eJ hS hpS hL hY ht hfixed
  exact ⟨hK,hc.natural⟩

end BinaryA4Pair
