module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Bounds
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Moving

/-!
# Assembly of the H-star generation argument

The Hall actor is constructed from E.2.2 on the literal H and proved faithful
using the odd-kernel normalizer input. The source automizer bound handles an
actor preserving V. Otherwise the preceding Sp₄/G₂ normalization conclusion
forces SL₃, TI gives C_V(H)=1, and 3.1.8 gives L=[L,J(T)]. The doubled-module
recognition and its automizer bound then finish the second alternative.

Three genuine source inputs remain: the nonbinary 4.4.3 specialization,
the two model automizer bounds, and the B.5 doubled-module step. The theorem
below is a conditional assembly, not a completed proof of 11.2.1. The
11.0.3(5) premise is retained for the preceding-source assembly owner.

Source: Aschbacher--Smith, 11.2.1, printed pp.766--767.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The source assembly with each independent, still-unproved input exposed. -/
theorem conclusion_of_source_steps
    (hrows : OtherRowsNormalize D S)
    (hcontrol : OddKernelNormalizer (T := T) (L := L) (V := V))
    (hbounds : AutomizerBounds D S) (hdouble : DoublingStep D S)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Conclusion D S H := by
  by_cases hsmall : ChapterE.generationParameter H ≤ S.field.degree
  · exact Or.inl hsmall
  have hlarge : 1 < ChapterE.generationParameter H :=
    S.nonbinary.trans (Nat.lt_of_not_ge hsmall)
  obtain ⟨hP,f,_,hf,d,hm,_⟩ := hall_data D S hH hlarge
  have hfaith := hall_faithful D S hcontrol hH hlarge hP d hm
  let B := d.witness.abelianGroup.map H.subtype
  have hBH : B ≤ H := map_subtype_le _
  have hBM : B ≤ normalizer (L : Set G) := map_le_iff_le_comap.mpr (d.hall_le.trans hm.le)
  have hmove : ¬ B ≤ normalizer (V : Set G) := fun hn =>
    hsmall (parameter_le_degree_of_normalizes D S hbounds hH hP d hm hf hfaith hn)
  obtain ⟨m⟩ := linear_of_moving D S hrows hH hBH hBM hmove
  have hfixedB := fixed_eq_bot_of_moving D S m hBM hmove
  have hfixed : V ⊓ centralizer (H : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left V (centralizer_le hBH)).trans hfixedB.le)
  have hJ := thompson_of_fixed_eq_bot D S hH hfixed
  have hproper : V ≠ Source.conjugateSpan (normalizer (L : Set G)) V := by
    intro he
    apply hmove
    apply hBM.trans
    rw [he]
    exact le_normalizer_componentOrbit V _
  have hd := hdouble ⟨m⟩ hJ hproper
  exact Or.inr ⟨hd.isSL D S,hd,hfixed,hJ,
    parameter_le_twice_degree D S hbounds hd hH hP d hm hf hfaith⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
