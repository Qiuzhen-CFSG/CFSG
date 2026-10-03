module
public import ABG.ChapterII.Section1.RepresentativeFusionRelation
public import ABG.ChapterII.Section1.SmallNormalizerFusionControl
public import Theory.GroupTheory.NormalizerActionSurjective
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.SylowElementConjugacy
public import ABG.ChapterII.Section1.FourInvolutionRepresentatives
public import Theory.GroupTheory.SpecificGroups.QuaternionEightInvolution
/-!
# Global involution fusion for quasi-dihedral Sylow subgroups

For the actual chosen four subgroup `T` and quaternion subgroup `Q` of a
quasi-dihedral Sylow two-subgroup `P`, the four-subgroup automizer determines
the global involution count. Index six gives one conjugacy class; index two
gives two classes and weak closure of the embedded center of `P` in `P`.
The class-count conclusions include representatives, coverage, and pairwise
nonconjugacy, using the existing source predicates.

For index two, apply the representative fusion relation to the assertion
that an involution is conjugate within `P`. The low-index four normalizer
introduces no new fusion, and every quaternion normalizer fixes its unique
involution. Thus the two Sylow classes stay distinct globally. Writing the
Sylow center as the cyclic subgroup of its central involution shows that
any ambient conjugate contained in `P` is the same subgroup.

For index six, the normalizer acts as the full four-group automorphism group.
An identity-fixing swap conjugates the two Sylow class representatives lying
in the chosen `T`, so their global classes coincide. In both cases, conjugating
arbitrary involutions into the fixed Sylow subgroup supplies global coverage.

This proves the involution-count clauses of ABG Chapter II, §1, Proposition 1
and its Q-case center weak closure, article pp.10–11 of
`refs/latex/alperin-brauer-gorenstein.tex`, without any condition on the
quaternion outer automizer index.
-/

namespace ABG
variable {G : Type*} [Group G] [Finite G]
private theorem conj_order {H : Type*} [Group H] {x y : H} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).symm

private theorem conj_eq_of_central {H : Type*} [Group H] {x y : H}
    (hx : x ∈ Subgroup.center H) (hxy : IsConj x y) : x = y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  simpa only [Subgroup.mem_center_iff.mp hx g, mul_assoc, mul_inv_cancel, mul_one] using hg

private theorem four_full_conjugacy (T : Subgroup G) (hT : IsFourGroup T)
    (hindex : automizerIndex T = 6) (x y : T) (hx : x ≠ 1) (hy : y ≠ 1) :
    IsConj (x : G) (y : G) := by
  classical
  let : IsKleinFour T := hT
  let f : MulAut T := IsKleinFour.mulEquiv (Equiv.swap x y)
    (Equiv.swap_apply_of_ne_of_ne (Ne.symm hx) (Ne.symm hy))
  have hs : Function.Surjective T.normalizerMonoidHom :=
    T.normalizerMonoidHom_surjective_of_index_eq_card (by
      rw [IsKleinFour.card_mulAut T]
      exact hindex)
  obtain ⟨g, hg⟩ := hs f
  have hh := congrArg (fun f : MulAut T => (f x : G)) hg
  change (g : G) * (x : G) * (g : G)⁻¹ = (Equiv.swap x y x : G) at hh
  exact isConj_iff.mpr ⟨g, by simpa only [Equiv.swap_apply_left] using hh⟩

private theorem low_involution_control
    (P : Sylow 2 G) (T Q : Subgroup G) (hframe : QuasiDihedralFusionFrame P T Q)
    (hindex : automizerIndex T = 2)
    {x y : P} (hx : orderOf x = 2) (hxy : IsConj (x : G) (y : G)) :
    IsConj x y := by
  obtain ⟨eQ⟩ := hframe.2.2.2.2
  have huniq (u v : Q) (hu : orderOf u = 2) (hv : orderOf v = 2) : u = v := by
    apply eQ.injective
    exact QuaternionGroup.eq_of_orderOf_eq_two _ _
      ((eQ.orderOf_eq u).trans hu) ((eQ.orderOf_eq v).trans hv)
  have houter : outerAutomizerIndex T = 2 := by
    let : IsKleinFour T := hframe.2.2.2.1
    let : IsMulCommutative T := IsKleinFour.isMulCommutative
    rw [outerAutomizerIndex, sup_eq_right.mpr (Subgroup.le_centralizer T)]
    exact hindex
  apply quasiDihedral_representative_fusion_relation P T Q hframe
    (fun u v => orderOf u = 2 → IsConj u v)
    (fun u _ => IsConj.refl u)
    (fun huv hvw hu => (huv hu).trans (hvw ((conj_order (huv hu)).symm.trans hu)))
    (fun h _ => h) ?_ ?_ hxy hx
  · intro g hg u v hu huv _
    exact QuasiDihedral.small_normalizer_fusion_control (P : Subgroup G) T hframe.1
      hframe.2.1 (Or.inl hframe.2.2.2.1) houter g hg u v hu huv
  · intro g hg u v hu huv hu2
    have hvQ : (v : G) ∈ Q := by
      have hgi := (Subgroup.normalizer (Q : Set G)).inv_mem hg
      have hh := (hgi (u : G)).mp hu
      simpa only [inv_inv, huv, SetLike.mem_coe] using hh
    have hv2 : orderOf v = 2 := by
      have hc : IsConj (u : G) (v : G) := isConj_iff.mpr ⟨g⁻¹, by simpa only [inv_inv] using huv⟩
      simpa only [Subgroup.orderOf_coe] using (conj_order hc).symm.trans (by simpa only [Subgroup.orderOf_coe] using hu2)
    have he := huniq ⟨u, hu⟩ ⟨v, hvQ⟩
      ((Subgroup.orderOf_coe (⟨(u : G), hu⟩ : Q)).symm.trans ((Subgroup.orderOf_coe u).trans hu2))
      ((Subgroup.orderOf_coe (⟨(v : G), hvQ⟩ : Q)).symm.trans ((Subgroup.orderOf_coe v).trans hv2))
    have huv' : u = v := Subtype.ext (congrArg (fun q : Q => (q : G)) he)
    rw [huv']

private theorem two_classes_of_involution_control
    (P : Sylow 2 G) (hP : Stellmacher.IsSemidihedralGroup P)
    (hc : ∀ {x y : P}, orderOf x = 2 → IsConj (x : G) (y : G) → IsConj x y) :
    HasElementConjugacyClassCount G 2 2 := by
  obtain ⟨a, b, ha, hb, hab, hcov⟩ := QuasiDihedral.involution_conjugacy_classes hP
  let r : Fin 2 → G := ![(a : G), (b : G)]
  refine ⟨r, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [r, Subgroup.orderOf_coe] using ha
    · simpa [r, Subgroup.orderOf_coe] using hb
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hab (hc ha hij))
    · exact False.elim (hab (hc ha hij.symm))
    · rfl
  · intro x hx
    obtain ⟨y, hxy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
    have hy : orderOf y = 2 := by
      simpa only [Subgroup.orderOf_coe] using (conj_order hxy).symm.trans hx
    rcases hcov y hy with hy | hy
    · exact ⟨0, hxy.trans ((P : Subgroup G).subtype.map_isConj hy)⟩
    · exact ⟨1, hxy.trans ((P : Subgroup G).subtype.map_isConj hy)⟩

omit [Finite G] in
private theorem weak_center_of_involution_control
    (P : Sylow 2 G) (hP : Stellmacher.IsSemidihedralGroup P)
    (hc : ∀ {x y : P}, orderOf x = 2 → IsConj (x : G) (y : G) → IsConj x y) :
    BenderSuzuki.External.WeaklyClosedIn P (subgroupCenter (P : Subgroup G)) := by
  obtain ⟨n, hn, _, a, b, ha, hb, hab, hgen⟩ := hP
  let z : P := a ^ (2 ^ (n - 2))
  have hz : orderOf z = 2 := QuasiDihedral.half_order_pow_orderOf hn ha
  have hzC : z ∈ Subgroup.center P := QuasiDihedral.half_order_pow_mem_center hn a b ha hb hab hgen
  have hZ : subgroupCenter (P : Subgroup G) = Subgroup.zpowers (z : G) := by
    rw [subgroupCenter, QuasiDihedral.center_eq hn a b ha hb hab hgen, MonoidHom.map_zpowers]
    rfl
  constructor
  · exact Subgroup.map_subtype_le _
  · intro g hg
    rw [hZ, BenderSuzuki.PFchapter1section1.rightConjugate, Subgroup.conjBy, MonoidHom.map_zpowers] at hg ⊢
    have hy : (MulAut.conj g⁻¹) (z : G) ∈ P := hg (Subgroup.mem_zpowers _)
    let y : P := ⟨(MulAut.conj g⁻¹) (z : G), hy⟩
    have hzy : IsConj (z : G) (y : G) := isConj_iff.mpr ⟨g⁻¹, rfl⟩
    have he : z = y := conj_eq_of_central hzC (hc hz hzy)
    have he' : (MulAut.conj g⁻¹) (z : G) = (z : G) := (congrArg Subtype.val he).symm
    change Subgroup.zpowers ((MulAut.conj g⁻¹) (z : G)) = Subgroup.zpowers (z : G)
    rw [he']

private theorem high_involution_count (P : Sylow 2 G) (T : Subgroup G)
    (hT : IsFourGroup T) (hindex : automizerIndex T = 6)
    (hreps : ∃ z t : P, (z : G) ∈ T ∧ (t : G) ∈ T ∧ orderOf z = 2 ∧ orderOf t = 2 ∧
      ¬ IsConj z t ∧ ∀ x : P, orderOf x = 2 → IsConj x z ∨ IsConj x t) :
    HasElementConjugacyClassCount G 2 1 := by
  obtain ⟨z, t, hzT, htT, hz, ht, _, hcov⟩ := hreps
  have hzTorder : orderOf (⟨(z : G), hzT⟩ : T) = 2 :=
    (Subgroup.orderOf_coe _).symm.trans ((Subgroup.orderOf_coe z).trans hz)
  have htTorder : orderOf (⟨(t : G), htT⟩ : T) = 2 :=
    (Subgroup.orderOf_coe _).symm.trans ((Subgroup.orderOf_coe t).trans ht)
  have hzt : IsConj (z : G) (t : G) := four_full_conjugacy T hT hindex
    ⟨z, hzT⟩ ⟨t, htT⟩ (by intro h; simp [h] at hzTorder) (by intro h; simp [h] at htTorder)
  refine ⟨fun _ => (z : G), fun _ => (Subgroup.orderOf_coe z).trans hz,
    fun i j _ => Subsingleton.elim i j, ?_⟩
  intro x hx
  obtain ⟨y, hxy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  have hy : orderOf y = 2 := by
    simpa only [Subgroup.orderOf_coe] using (conj_order hxy).symm.trans hx
  refine ⟨0, hxy.trans ?_⟩
  rcases hcov y hy with hyz | hyt
  · exact (P : Subgroup G).subtype.map_isConj hyz
  · exact ((P : Subgroup G).subtype.map_isConj hyt).trans hzt.symm

/-- The four-subgroup automizer controls the exact global involution count and center weak closure. -/
public theorem quasiDihedral_involution_fusion
    (P : Sylow 2 G) (T Q : Subgroup G) (hframe : QuasiDihedralFusionFrame P T Q) :
    (automizerIndex T = 6 → HasElementConjugacyClassCount G 2 1) ∧
    (automizerIndex T = 2 → HasElementConjugacyClassCount G 2 2 ∧
      BenderSuzuki.External.WeaklyClosedIn P (subgroupCenter (P : Subgroup G))) := by
  constructor
  · intro hhigh
    exact high_involution_count P T hframe.2.2.2.1 hhigh
      (QuasiDihedral.four_involution_representatives (P : Subgroup G) hframe.1 T
        hframe.2.1 hframe.2.2.2.1)
  · intro hlow
    have hc : ∀ {x y : P}, orderOf x = 2 → IsConj (x : G) (y : G) → IsConj x y :=
      low_involution_control P T Q hframe hlow
    exact ⟨two_classes_of_involution_control P hframe.1 hc,
      weak_center_of_involution_control P hframe.1 hc⟩
end ABG
