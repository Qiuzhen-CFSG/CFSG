module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Action
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.EasyCases
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# The even natural-six point action

Every best offender inside the marked point radical contains the point
transposition. Thus an even action makes the elementary Thompson subgroup
centralize the natural module. B.2.10 then makes the literal point-radical
Baumann subgroup normal, closing the A₆-image branch of 13.2.2(7).

Source: Aschbacher--Smith B.3.4(1), C.1.37 and 13.2.2(7), pp.84,142,878.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinarySix
variable {G : Type*} [Group G] [Finite G]

/-- An even marked six-point action centralizes every maximum elementary generator. -/
theorem thompson_centralizes_even_point_action
    (U R : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hUR : U ≤ R) (q : G →* Equiv.Perm (Fin 6))
    (f : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hact : ∀ (g : G) (v : U),
      ((f.symm (Multiplicative.ofAdd
        (BinaryPermutation.naturalRepresentation (Fin 6) (q g) (f v).toAdd))) : G) =
        g * (v : G) * g⁻¹)
    (hpoint : R.map q ≤ ChapterC.NaturalSixControl.Model.E)
    (heven : R.map q ≤ alternatingGroup (Fin 6)) :
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
      apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
      rw [map_one]
      apply LinearMap.ext
      intro w
      let v := f.symm (Multiplicative.ofAdd w)
      have h := hact g v
      rw [← hg v v.property, mul_inv_cancel_right] at h
      have hs : f.symm (Multiplicative.ofAdd
          (BinaryPermutation.naturalRepresentation (Fin 6) (q g) (f v).toAdd)) = v :=
        Subtype.ext h
      have hh := congrArg f hs
      simpa only [MulEquiv.apply_symm_apply, v, toAdd_ofAdd,
        Module.End.one_apply] using congrArg Multiplicative.toAdd hh
  let qr := q.rangeRestrict
  have hkr : qr.ker = centralizer (U : Set G) :=
    q.ker_rangeRestrict.trans hk
  let ρ := NormalElementaryQuotient.representation U qr q.rangeRestrict_surjective hkr
  let a : Additive U ≃+ BinaryPermutation.natural (Fin 6) :=
    f.toAdditive.trans (AddEquiv.additiveMultiplicative _)
  let e : Additive U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
    { a with map_smul' := ZMod.map_smul a }
  have he (g : q.range) (v : Additive U) :
      e (ρ g v) = BinaryPermutation.naturalRepresentation (Fin 6) g.val (e v) := by
    obtain ⟨g,rfl⟩ := q.rangeRestrict_surjective g
    have hr := NormalElementaryQuotient.representation_apply U qr
      q.rangeRestrict_surjective hkr g v
    have ha := hact g v.toMul
    have hh : (ρ (qr g) v).toMul = f.symm (Multiplicative.ofAdd
        (BinaryPermutation.naturalRepresentation (Fin 6) (q g) (f v.toMul).toAdd)) :=
      Subtype.ext (hr.trans ha.symm)
    change (f ((ρ (qr g) v).toMul)).toAdd = _
    rw [hh, MulEquiv.apply_symm_apply]
    rfl
  apply sSup_le
  intro A hA
  by_contra hn
  have hoff := NormalElementaryQuotient.maxElementary_isOffender U qr
    q.rangeRestrict_surjective hkr R A hUR hA (by rwa [hkr])
  have ht := hoff.map_equivariant ρ (BinaryPermutation.naturalRepresentation (Fin 6))
    q.range.subtype q.range.subtype_injective e he
  obtain ⟨B,hBA,hB⟩ := ht.exists_bestOffender _
  have hBE : B ≤ ChapterC.NaturalSixControl.Model.E := by
    apply hBA.trans
    rw [Subgroup.map_map]
    exact (Subgroup.map_mono hA.1).trans hpoint
  have hBeven : B ≤ alternatingGroup (Fin 6) := by
    apply hBA.trans
    rw [Subgroup.map_map]
    exact (Subgroup.map_mono hA.1).trans heven
  have hswap := hBeven (ChapterC.NaturalSixControl.Model.best_contains_swap hBE hB)
  exact (by decide : ChapterB.Offenders.pairSwap 6 2 ∉ alternatingGroup (Fin 6)) hswap

/-- For the even action, B.2.10 gives normality of the actual point Baumann subgroup. -/
theorem baumann_normal_of_even_point_action
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* Equiv.Perm (Fin 6))
    (f : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hact : ∀ (g : G) (v : U),
      (f (MulAut.conjNormal g v)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (q g) (f v).toAdd)
    (hker : q.ker = pCore 2 G)
    (hrange : q.range = alternatingGroup (Fin 6)) :
    (ChapterB.baumann
      ((Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1.comap q).pCoreIn 2)).Normal := by
  let P := Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1.comap q
  let R := P.pCoreIn 2
  have hk : q.ker = centralizer (U : Set G) :=
    ChapterC.RankOne.SymmetricSix.natural_six_kernel_eq_centralizer U q f hact
  have hQP : pCore 2 G ≤ P := by
    rw [← hker]
    exact MonoidHom.ker_le_comap q _
  have hQR : pCore 2 G ≤ R :=
    le_pCoreIn_of_normalizes pCore_isPGroup hQP le_normalizer_of_normal
  have hUQ : U ≤ pCore 2 G := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩
  have hUR : U ≤ R := hUQ.trans hQR
  have hPi : P.map q = Theory.SpecificGroups.SymmetricSix.BinaryFlags.L1 := by
    change (Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1.comap q).map q = _
    rw [map_comap_eq, hrange]
    exact inf_comm _ _
  have hRi : R.map q ≤ ChapterC.NaturalSixControl.Model.E := by
    have hm := map_pCoreIn_of_ker_isPGroup q (hker.symm ▸ pCore_isPGroup) P
    rw [hPi, Theory.SpecificGroups.SymmetricSix.BinaryFlags.L1_core_eq_pointCoreEven] at hm
    rw [hm]
    exact inf_le_left.trans_eq ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional
  have heven : R.map q ≤ alternatingGroup (Fin 6) := hrange ▸ map_le_range q R
  have hJ := thompson_centralizes_even_point_action U R hUR q f (by
    intro g v
    have hh := hact g v
    change ((f.symm _) : G) = ((MulAut.conjNormal g v : U) : G)
    apply congrArg Subtype.val
    apply f.injective
    rw [f.apply_symm_apply]
    exact (congrArg Multiplicative.ofAdd hh).symm) hRi heven
  have hc : pCore 2 G = R ⊓ centralizer (U : Set G) := by
    rw [← hk, hker, inf_eq_right.mpr hQR]
  have hJ0 : ChapterB.thompsonJ R 0 ≤ centralizer (U : Set G) := by
    rw [ChapterB.thompsonJ_zero]
    exact hJ
  exact (ChapterB.lemma_B_2_10_centralizing U R hUR hQR hc hJ0).2.2.2

/-- Relabeling an arbitrary nonidentity point preserves its literal centralizer
and proves normality of its Baumann subgroup in the even action case. -/
theorem baumann_normal_of_even_natural_action
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* Equiv.Perm (Fin 6))
    (f : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hact : ∀ (g : G) (v : U),
      (f (MulAut.conjNormal g v)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (q g) (f v).toAdd)
    (hker : q.ker = pCore 2 G)
    (hrange : q.range = alternatingGroup (Fin 6)) (v : U) (hv : v ≠ 1) :
    (ChapterB.baumann ((centralizer ({(v : G)} : Set G)).pCoreIn 2)).Normal := by
  let ρ := BinaryPermutation.naturalRepresentation (Fin 6)
  have hfv : (f v).toAdd ≠ 0 := by
    intro h
    apply hv
    apply f.injective
    apply Multiplicative.toAdd.injective
    rw [map_one]
    exact h
  obtain ⟨a,ha⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport.transitive_nonzero
    (f v).toAdd (Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector 4 5)
    hfv Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector45_ne_zero
  let q0 := (MulAut.conj a.val).toMonoidHom.comp q
  let f0 : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
    f.trans (LinearMap.GeneralLinearGroup.toLinearEquiv
      (ρ.asGroupHom a.val)).toAddEquiv.toMultiplicative
  have hf0 (w : U) : (f0 w).toAdd = ρ a.val (f w).toAdd := rfl
  have hmark : (f0 v).toAdd =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector 4 5 := ha
  have hact0 (g : G) (w : U) : (f0 (MulAut.conjNormal g w)).toAdd =
      ρ (q0 g) (f0 w).toAdd := by
    rw [hf0,hact,hf0]
    change ρ a.val (ρ (q g) (f w).toAdd) =
      ρ (a.val * q g * a.val⁻¹) (ρ a.val (f w).toAdd)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel_right]
  have hk0 : q0.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj a.val).injective,hker]
  have hr0 : q0.range = alternatingGroup (Fin 6) := by
    rw [MonoidHom.range_comp,hrange]
    exact Theory.SpecificGroups.SymmetricSix.BinaryFlags.conjugate_alternating a.val
  have hP : centralizer ({(v : G)} : Set G) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1.comap q0 := by
    ext g
    have he : g ∈ centralizer ({(v : G)} : Set G) ↔ MulAut.conjNormal g v = v := by
      rw [mem_centralizer_singleton_iff]
      constructor
      · intro hc
        apply Subtype.ext
        change g * (v : G) * g⁻¹ = v
        rw [hc,mul_inv_cancel_right]
      · intro hc
        exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hc)
    rw [he]
    have he' : MulAut.conjNormal g v = v ↔
        ρ (q0 g) (Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector 4 5) =
          Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector 4 5 := by
      constructor
      · intro h
        have hh := hact0 g v
        rw [h,hmark] at hh
        exact hh.symm
      · intro h
        apply f0.injective
        apply Multiplicative.toAdd.injective
        rw [hact0,hmark,h]
    rw [he']
    change ρ (q0 g) (Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector 4 5) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector 4 5 ↔ _
    rw [Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector_map,
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector_eq_iff
        ((q0 g).injective.ne (by decide)) (by decide)]
    change Theory.SpecificGroups.SymmetricSix.pair (q0 g 4) (q0 g 5) =
      Theory.SpecificGroups.SymmetricSix.pair 4 5 ↔
      (Theory.SpecificGroups.SymmetricSix.pair 4 5).image (q0 g) =
        Theory.SpecificGroups.SymmetricSix.pair 4 5
    simp [Theory.SpecificGroups.SymmetricSix.pair]
  rw [hP]
  exact baumann_normal_of_even_point_action U q0 f0 hact0 hk0 hr0

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinarySix
