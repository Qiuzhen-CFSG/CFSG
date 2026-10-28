module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddParity
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# Thompson fixation for an even five-point action

A maximum elementary subgroup moving a normal elementary module gives an
FF offender in its literal conjugation image. On the binary five-point
natural module every offender contains an odd permutation. Hence an even
marked action makes the whole elementary Thompson subgroup centralize the
module, including when the original action has a nontrivial kernel.

Source: Aschbacher–Smith B.3.2(4), B.4.2 and the A₅ step of 13.7.4,
printed pp.83, 87 and 937.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- An even marked five-point action centralizes every maximum elementary generator. -/
theorem five_thompson_centralizes_of_even_action
    (U R : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hUR : U ≤ R) (q : G →* Equiv.Perm (Fin 5))
    (f : U ≃* Multiplicative (BinaryPermutation.natural (Fin 5)))
    (hact : ∀ (g : G) (v : U),
      ((f.symm (Multiplicative.ofAdd
        (BinaryPermutation.naturalRepresentation (Fin 5) (q g) (f v).toAdd))) : G) =
        g * (v : G) * g⁻¹)
    (heven : R.map q ≤ alternatingGroup (Fin 5)) :
    elementaryAbelianMaxJ R ≤ centralizer (U : Set G) := by
  have hk : q.ker = centralizer (U : Set G) := by
    ext g
    constructor
    · intro hg v hv
      have h := hact g ⟨v,hv⟩
      change q g = 1 at hg
      rw [hg,map_one] at h
      simp only [Module.End.one_apply, ofAdd_toAdd,
        MulEquiv.symm_apply_apply] at h
      exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm
    · intro hg
      change q g = 1
      apply BinaryPermutation.naturalRepresentation_injective (Fin 5) (by decide)
      rw [map_one]
      apply LinearMap.ext
      intro w
      let v := f.symm (Multiplicative.ofAdd w)
      have h := hact g v
      rw [← hg v v.property, mul_inv_cancel_right] at h
      have hs : f.symm (Multiplicative.ofAdd
          (BinaryPermutation.naturalRepresentation (Fin 5) (q g) (f v).toAdd)) = v :=
        Subtype.ext h
      have hh := congrArg f hs
      simpa only [MulEquiv.apply_symm_apply, v, toAdd_ofAdd,
        Module.End.one_apply] using congrArg Multiplicative.toAdd hh
  let qr := q.rangeRestrict
  have hkr : qr.ker = centralizer (U : Set G) :=
    q.ker_rangeRestrict.trans hk
  let ρ := NormalElementaryQuotient.representation U qr q.rangeRestrict_surjective hkr
  let a : Additive U ≃+ BinaryPermutation.natural (Fin 5) :=
    f.toAdditive.trans (AddEquiv.additiveMultiplicative _)
  let e : Additive U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
    { a with map_smul' := ZMod.map_smul a }
  have he (g : q.range) (v : Additive U) :
      e (ρ g v) = BinaryPermutation.naturalRepresentation (Fin 5) g.val (e v) := by
    obtain ⟨g,rfl⟩ := q.rangeRestrict_surjective g
    have hr := NormalElementaryQuotient.representation_apply U qr
      q.rangeRestrict_surjective hkr g v
    have ha := hact g v.toMul
    have hh : (ρ (qr g) v).toMul = f.symm (Multiplicative.ofAdd
        (BinaryPermutation.naturalRepresentation (Fin 5) (q g) (f v.toMul).toAdd)) :=
      Subtype.ext (hr.trans ha.symm)
    change (f ((ρ (qr g) v).toMul)).toAdd = _
    rw [hh, MulEquiv.apply_symm_apply]
    rfl
  apply sSup_le
  intro A hA
  by_contra hn
  have hoff := NormalElementaryQuotient.maxElementary_isOffender U qr
    q.rangeRestrict_surjective hkr R A hUR hA (by rwa [hkr])
  have ht := hoff.map_equivariant ρ (BinaryPermutation.naturalRepresentation (Fin 5))
    q.range.subtype q.range.subtype_injective e he
  obtain ⟨B,hBA,hB⟩ := ht.exists_bestOffender _
  have hnot := ((Offenders.Odd.isBestOffender_natural_iff_caseAFamily
    (Or.inl rfl) B).mp hB).not_le_alternating
  apply hnot
  apply hBA.trans
  rw [Subgroup.map_map]
  exact (Subgroup.map_mono hA.1).trans heven
end CFSG.Quasithin.ChapterB
