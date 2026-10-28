module

public import Theory.SpecificGroups.Janko1.Model.InvolutionCentralizer
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.PResidual.Defs
public import Theory.GroupTheory.SolvableResidual
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Nilpotent

/-!
# Structure of a realized C₂ × A₅ centralizer

For a group actually isomorphic to C₂ × A₅, projection onto A₅ identifies its
solvable radical with C₂ and its radical quotient with A₅. Projection onto C₂
has perfect kernel, which equals both the two-residual and the solvable residual.
Every Sylow two-subgroup maps to a subgroup of order four in the radical quotient.

These are consequences of an explicit multiplicative equivalence, retained as a
parameter. Constructing the equivalence for the J₁ matrix centralizer is separate.
The E-member application is in ChapterE's `JankoOne.CentralizerMember`.

Source: GLS3, Table 5.3f, as used in Aschbacher–Smith E.1.14(5), printed p.214.
-/

public section
open Subgroup
namespace Janko1.InvolutionCentralizer
private instance a5_perfect : Group.IsPerfect (alternatingGroup (Fin 5)) :=
  ⟨commutator_alternatingGroup_eq_top (by simp)⟩

private theorem a5_radical : solvableRadical (alternatingGroup (Fin 5)) = ⊥ := by
  let H := alternatingGroup (Fin 5)
  rcases (inferInstance : (solvableRadical H).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hs : Group.IsSolvable (⊤ : Subgroup H) := h ▸ inferInstance
    let := hs
    exact (Group.IsPerfect.not_isSolvable H
      (Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup H) ≃* H).toMonoidHom)
        topEquiv.surjective)).elim

variable {H : Type*} [Group H]
private def fstHom (e : H ≃* ProductModel) : H →* Multiplicative (ZMod 2) :=
  (MonoidHom.fst _ _).comp e.toMonoidHom
private def sndHom (e : H ≃* ProductModel) : H →* alternatingGroup (Fin 5) :=
  (MonoidHom.snd _ _).comp e.toMonoidHom

private theorem fst_surjective (e : H ≃* ProductModel) : Function.Surjective (fstHom e) := by
  intro x
  exact ⟨e.symm (x, 1), by simp [fstHom]⟩
private theorem snd_surjective (e : H ≃* ProductModel) : Function.Surjective (sndHom e) := by
  intro x
  exact ⟨e.symm (1, x), by simp [sndHom]⟩

private noncomputable def fstKerEquiv (e : H ≃* ProductModel) :
    (fstHom e).ker ≃* alternatingGroup (Fin 5) :=
  MulEquiv.ofBijective ((sndHom e).comp (fstHom e).ker.subtype) (by
    constructor
    · intro x y h
      apply Subtype.ext
      apply e.injective
      apply Prod.ext
      · exact x.property.trans y.property.symm
      · exact h
    · intro x
      refine ⟨⟨e.symm (1, x), by change (e (e.symm (1, x))).1 = 1; simp⟩, ?_⟩
      simp [sndHom])

private noncomputable def sndKerEquiv (e : H ≃* ProductModel) :
    (sndHom e).ker ≃* Multiplicative (ZMod 2) :=
  MulEquiv.ofBijective ((fstHom e).comp (sndHom e).ker.subtype) (by
    constructor
    · intro x y h
      apply Subtype.ext
      apply e.injective
      exact Prod.ext h (x.property.trans y.property.symm)
    · intro x
      refine ⟨⟨e.symm (x, 1), by change (e (e.symm (x, 1))).2 = 1; simp⟩, ?_⟩
      simp [fstHom])

private theorem card_two : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  change Nat.card (ZMod 2) = 2
  exact Nat.card_zmod 2

variable [Finite H]

private theorem radical_eq_ker (e : H ≃* ProductModel) : solvableRadical H = (sndHom e).ker := by
  let : Group.IsSolvable (sndHom e).ker :=
    Group.isSolvable_of_isSolvable_injective
      (f := (sndKerEquiv e).toMonoidHom) (sndKerEquiv e).injective
  have h := comap_solvableRadical_eq_of_solvable_ker (sndHom e) (snd_surjective e)
  simpa only [a5_radical, MonoidHom.comap_bot] using h.symm

/-- The solvable radical of a realized C₂ × A₅ is a two-group. -/
theorem radical_isTwoGroup (e : H ≃* ProductModel) : IsPGroup 2 (solvableRadical H) := by
  apply IsPGroup.of_card (n := 1)
  rw [radical_eq_ker e, Nat.card_congr (sndKerEquiv e).toEquiv, card_two]
  rfl

/-- Projection onto A₅ identifies the intrinsic radical quotient. -/
noncomputable def radicalQuotientEquiv (e : H ≃* ProductModel) :
    H ⧸ solvableRadical H ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq (radical_eq_ker e)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (sndHom e) (snd_surjective e))

/-- Both residuals are the perfect A₅ kernel of projection onto C₂. -/
theorem residual_eq (e : H ≃* ProductModel) : pResidual 2 H = solvableResidual H := by
  let L := (fstHom e).ker
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (fstKerEquiv e).symm.toMonoidHom) (fstKerEquiv e).symm.surjective
  have hp : IsPGroup 2 (H ⧸ L) :=
    (IsPGroup.of_card (p := 2) (n := 1) card_two).of_equiv
      (QuotientGroup.quotientKerEquivOfSurjective (fstHom e) (fst_surjective e)).symm
  let : Group.IsNilpotent (H ⧸ L) := hp.isNilpotent
  have hs : solvableResidual H = L := le_antisymm
    (solvableResidual_le_of_solvable_quotient L) (le_solvableResidual_of_isPerfect L)
  rw [hs]
  refine le_antisymm (sInf_le ⟨inferInstance, hp⟩) ?_
  apply le_sInf
  rintro N ⟨hn, hN⟩
  let := hn
  let : Group.IsNilpotent (H ⧸ N) := hN.isNilpotent
  exact le_of_isPerfect_of_solvable_quotient L N

/-- The image of any Sylow two-subgroup in the radical quotient has order four. -/
theorem sylow_image_card (e : H ≃* ProductModel) (T : Sylow 2 H) :
    Nat.card ((T : Subgroup H).map (QuotientGroup.mk' (solvableRadical H))) = 4 := by
  let Q := H ⧸ solvableRadical H
  have hQ : Nat.card Q = 60 := by
    rw [Nat.card_congr (radicalQuotientEquiv e).toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  let S : Sylow 2 Q := T.mapSurjective (QuotientGroup.mk'_surjective (solvableRadical H))
  change Nat.card S = 4
  rw [S.card_eq_multiplicity, hQ]
  decide +kernel

end Janko1.InvolutionCentralizer
