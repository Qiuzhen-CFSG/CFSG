module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.LinearCentralizer

/-!
# Exact residual of the marked orthogonal centralizer

Lift the projective centralizer to the actual elementary isometry group.
The faithful right block action identifies every lift with a right SL₂ factor
and an isometry of the complement. Projection of that isometry modulo its
normal elementary subgroup has prime-to-characteristic image. Its kernel
therefore maps to a normal subgroup of prime-to-characteristic index in the
projective centralizer, and this image is the right elementary block image.
The reverse residual inclusion follows; transvection generation supplies the
forward inclusion, including over F₃.

Only the index of the complementary elementary group remains an input to this
general result. `IsometryQuotients` supplies it in every odd and split rank used
by `SplitOddCentralizers`, including the ternary and split-four endpoints.
We do not require the complementary quotient map to descend through scalars.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.17,
printed p.39 of `refs/quasithin.pdf`; the central-product calculation uses
GLS3 §2.7 and the literal elementary and scalar-quotient conventions.
-/

public noncomputable section
namespace ClassicalOrthogonal.Fundamental.SplitOddBlocks
open Theory.AlgebraicGroup
universe u
variable {F V W : Type u} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- A prime-to-characteristic complementary isometry quotient identifies the
right elementary block image with the image of the literal nested residual. -/
theorem rightProjective_range_eq_residual_of_index (p : ℕ) [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (Q : QuadraticForm F V) (S : QuadraticForm F W)
    (e : ((formD 2 F).prod Q).IsometryEquiv S)
    (hindex : Nat.Coprime p (elementarySubgroup Q).index) :
    (rightProjective Q S e).range =
      (Subgroup.primeToResidual p
        (Subgroup.centralizer ((leftProjective Q S e).range : Set (ProjectiveElementary S)))).map
          (Subgroup.centralizer ((leftProjective Q S e).range : Set (ProjectiveElementary S))).subtype := by
  apply le_antisymm (rightProjective_range_le_residual p Q S e)
  let C := Subgroup.centralizer ((leftProjective Q S e).range : Set (ProjectiveElementary S))
  let D := C.comap (projectiveElementaryMap S)
  let q : D →* C := ((projectiveElementaryMap S).comp D.subtype).codRestrict C
    (fun y => y.property)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨g, hg⟩ := projectiveElementaryMap_surjective S x.val
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    change projectiveElementaryMap S g ∈ C
    exact hg ▸ x.property
  let r : D →* (rightIsometry Q S e).range :=
    ((elementarySubgroup S).subtype.comp D.subtype).codRestrict _ (by
      intro y
      obtain ⟨a, h, hh⟩ := projective_centralizer_coverage p hp Q S e y.val y.property
      exact ⟨(a, h), hh.symm⟩)
  let t : D →* Matrix.SpecialLinearGroup (Fin 2) F × quadraticIsometrySubgroup Q :=
    (MonoidHom.ofInjective (rightIsometry_injective Q S e)).symm.toMonoidHom.comp r
  have ht (y : D) : rightIsometry Q S e (t y) = y.val.val :=
    MonoidHom.apply_ofInjective_symm (rightIsometry_injective Q S e) (r y)
  let : (elementarySubgroup Q).Normal := elementary_normal Q
  let d : D →* (quadraticIsometrySubgroup Q) ⧸ elementarySubgroup Q :=
    (QuotientGroup.mk' (elementarySubgroup Q)).comp ((MonoidHom.snd _ _).comp t)
  have hd : Nat.Coprime p d.ker.index := by
    rw [Subgroup.index_ker]
    exact hindex.coprime_dvd_right d.range.card_subgroup_dvd_card
  let : (d.ker.map q).Normal := (inferInstance : d.ker.Normal).map q hq
  have hm : Nat.Coprime p (d.ker.map q).index :=
    hd.coprime_dvd_right (d.ker.index_map_dvd hq)
  rintro x ⟨z, hz, rfl⟩
  obtain ⟨y, hy, hyz⟩ := Subgroup.primeToResidual_le (d.ker.map q) hm hz
  have hb : (t y).2 ∈ elementarySubgroup Q :=
    (QuotientGroup.eq_one_iff (N := elementarySubgroup Q) (t y).2).mp hy
  let b : Matrix.SpecialLinearGroup (Fin 2) F × elementarySubgroup Q :=
    ((t y).1, ⟨(t y).2, hb⟩)
  have hbcover : rightCover Q S e b = y.val := by
    apply Subtype.ext
    exact (rightIsometry_elementary Q S e b).symm.trans (ht y)
  refine ⟨b, ?_⟩
  change projectiveElementaryMap S (rightCover Q S e b) = z.val
  rw [hbcover]
  exact congrArg Subtype.val hyz

end ClassicalOrthogonal.Fundamental.SplitOddBlocks
