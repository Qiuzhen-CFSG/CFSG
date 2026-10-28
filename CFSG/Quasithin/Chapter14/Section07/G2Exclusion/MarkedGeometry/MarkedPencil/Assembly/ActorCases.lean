module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Actors.Assembly
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions

/-!
# Joining the faithful actor and the pencil centralizer

An injective actor containing the derived binary G₂ group is either that
index-two subgroup or the full group. We construct equivalences respecting
the specified embedding, so the existing centralizer calculations apply to
the actual quotient action. Point transitivity identifies its full pencil
centralizer with a conjugate of the concrete root eight; this discharges the
centralizer premise in the B.4.6 offender application.

The full octonion actor also acts on the literal quotient through its given
module coordinates. This extension is kept explicit when the source actor
is only the derived group: its elementary eight is not placed inside that
smaller actor.

Source: Aschbacher–Smith 14.7.55(4),(5),(8), printed p.1066, PDF p.1083;
B.4.6(13), printed pp.88–90. The precise B.4.6 numerical and best-offender
premises remain with qt-b-04-g2. Existing ATLAS imports retain their attribution
in LICENSES/ATLAS.txt; no new ATLAS source is copied here.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Assembly
open Atlas.G2 Atlas.G2.Natural Atlas.SplitOctonion
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Representation Representation.BinaryOffender Subgroup
open Actors SourceActions

variable {D Q W : Type*} [Group D] [Group Q] [AddCommGroup W] [Module (ZMod 2) W]

/-- The two possible faithful source actors, with their actual embeddings. -/
theorem actor_equivalences (i : D →* Model (ZMod 2)) (hi : Function.Injective i)
    (hJ : commutator (Model (ZMod 2)) ≤ i.range) :
    (∃ j : commutator (Model (ZMod 2)) ≃* D, ∀ g, i (j g) = g.val) ∨
      (∃ j : Model (ZMod 2) ≃* D, ∀ g, i (j g) = g) := by
  by_cases heq : i.range = commutator (Model (ZMod 2))
  · let k := i.codRestrict (commutator (Model (ZMod 2)))
      (fun d => heq ▸ (show i d ∈ i.range from ⟨d,rfl⟩))
    have hk : Function.Bijective k := by
      constructor
      · intro x y h
        exact hi (congrArg Subtype.val h)
      · intro g
        obtain ⟨d,hd⟩ := hJ g.property
        exact ⟨d, Subtype.ext hd⟩
    let j := MulEquiv.ofBijective k hk
    exact Or.inl ⟨j.symm, fun g => congrArg Subtype.val (j.apply_symm_apply g)⟩
  · have hlt : commutator (Model (ZMod 2)) < i.range :=
      lt_of_le_of_ne hJ (Ne.symm heq)
    have hindex : (commutator (Model (ZMod 2))).index = 2 := by
      rw [BinaryParabolicPair.commutator_eq_longRootClosure, BinaryException.index_H]
    have hm := Subgroup.relIndex_mul_index hJ
    rw [hindex] at hm
    have hp : ((commutator (Model (ZMod 2))).relIndex i.range * i.range.index).Prime :=
      by rw [hm]; exact Nat.prime_two
    have hr : i.range = ⊤ := by
      rcases Nat.prime_mul_iff.mp hp with ⟨_,hr⟩ | ⟨_,hr⟩
      · exact Subgroup.index_eq_one.mp hr
      · exact (hlt.not_ge (Subgroup.relIndex_eq_one.mp hr)).elim
    let j := MulEquiv.ofBijective i ⟨hi, MonoidHom.range_eq_top.mp hr⟩
    exact Or.inr ⟨j.symm, fun g => j.apply_symm_apply g⟩

/-- The full model action on the literal quotient, even when the source
faithful actor is its derived subgroup. -/
@[instance_reducible] def modelQuotientAction
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (e : Multiplicative W ≃* Q) : MulDistribMulAction (Model (ZMod 2)) Q where
  smul g q := e (Multiplicative.ofAdd (σ g (e.symm q).toAdd))
  one_smul q := by
    change e (Multiplicative.ofAdd (σ 1 (e.symm q).toAdd)) = q
    rw [map_one]
    exact e.apply_symm_apply q
  mul_smul g h q := by
    change e (Multiplicative.ofAdd (σ (g*h) (e.symm q).toAdd)) =
      e (Multiplicative.ofAdd (σ g (e.symm (e (Multiplicative.ofAdd (σ h (e.symm q).toAdd)))).toAdd))
    rw [e.symm_apply_apply, map_mul]
    rfl
  smul_one g := by
    change e (Multiplicative.ofAdd (σ g (e.symm 1).toAdd)) = 1
    simp
  smul_mul g q r := by
    change e (Multiplicative.ofAdd (σ g (e.symm (q*r)).toAdd)) =
      e (Multiplicative.ofAdd (σ g (e.symm q).toAdd)) *
        e (Multiplicative.ofAdd (σ g (e.symm r).toAdd))
    rw [map_mul]
    change e (Multiplicative.ofAdd (σ g ((e.symm q).toAdd + (e.symm r).toAdd))) = _
    rw [map_add]
    exact e.map_mul _ _

/-- The extended full action restricts to the specified faithful action. -/
theorem modelQuotientAction_restrict [MulAction D Q]
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (i : D →* Model (ZMod 2)) (e : Multiplicative W ≃* Q)
    (he : ∀ d w, d • e (Multiplicative.ofAdd w) = e (Multiplicative.ofAdd (σ (i d) w)))
    (d : D) (q : Q) :
    (modelQuotientAction σ e).smul (i d) q = d • q := by
  obtain ⟨w,rfl⟩ := e.surjective q
  change e (Multiplicative.ofAdd (σ (i d) (e.symm (e w)).toAdd)) = d • e w
  rw [e.symm_apply_apply]
  exact (he d w.toAdd).symm

/-- The full centralizer is a conjugate of the root eight, with no
centralizer-identification premise. -/
theorem pencil_centralizer_conjugate
    (f : SingularMap W) (σ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (hf : f.Equivariant σ) (p : SingularPoints (ZMod 2)) :
    ∃ a : Model (ZMod 2), subspaceKernel σ (pencilSpan f p) ⊤ =
      BinaryCore.elementary.map (MulAut.conj a).toMonoidHom := by
  obtain ⟨g,hg⟩ := exists_smul_firstPoint p
  have hp : g⁻¹ • firstPoint = p := by rw [← hg, inv_smul_smul]
  refine ⟨g⁻¹, ?_⟩
  change fullCentralizer f σ p = _
  rw [← hp, ← fullCentralizer_conjugate f σ hf,
    fullCentralizer_firstPoint f σ hf]

/-- The clause-(5) deduction with the sibling centralizer input discharged.
Only the stated earlier B.4.6 model facts remain explicit. -/
theorem quotient_ff_bestOffenders
    {H : Type*} [Group H] (π : H →* D) (hπ : Function.Surjective π)
    (U V₁ V₂ : Subgroup H) [(V₁.subgroupOf U).Normal]
    [MulAction D (U ⧸ V₁.subgroupOf U)]
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (i : D →* Model (ZMod 2)) (hi : Function.Injective i)
    (e : Multiplicative W ≃* U ⧸ V₁.subgroupOf U)
    (he : ∀ d w, d • e (Multiplicative.ofAdd w) = e (Multiplicative.ofAdd (σ (i d) w)))
    (hderived : commutator (Model (ZMod 2)) ≤ i.range)
    (hRank : ∀ A : Subgroup (Model (ZMod 2)), A ≤ commutator (Model (ZMod 2)) →
      IsElementaryTwo A → rank A ≤ 2)
    (hOne : ∀ A : Subgroup (Model (ZMod 2)), IsElementaryTwo A →
      rank A = 1 → 2 ≤ fixedCodim σ A)
    (hTwo : ∀ A : Subgroup (Model (ZMod 2)), A ≤ commutator (Model (ZMod 2)) →
      IsElementaryTwo A → rank A = 2 → 3 ≤ fixedCodim σ A)
    (hB46 : ∀ B : Subgroup (Model (ZMod 2)), IsBestOffender σ B ↔
      ∃ g : Model (ZMod 2), BinaryCore.elementary.map (MulAut.conj g).toMonoidHom = B)
    (f : SingularMap W) (hf : f.Equivariant σ) (p : SingularPoints (ZMod 2))
    (hmark : (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
      (transportGeometry f.geometry e).point p)
    (hff : IsFFModule (σ.comp i)) :
    (∃ j : D ≃* Model (ZMod 2), ∀ d, j d = i d) ∧
      {B : Subgroup D | IsBestOffender (σ.comp i) B} =
        Set.range (fun h : H =>
          (_root_.fixingSubgroup D
            (quotientPencilSpan (transportGeometry f.geometry e)
              ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) :
                Set (U ⧸ V₁.subgroupOf U))).map (MulAut.conj (π h)).toMonoidHom) := by
  obtain ⟨a,ha⟩ := pencil_centralizer_conjugate f σ hf p
  exact source_quotient_ff_bestOffenders π hπ U V₁ V₂ σ i hi e he hderived
    hRank hOne hTwo f p hmark a ha hB46 hff

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Assembly
