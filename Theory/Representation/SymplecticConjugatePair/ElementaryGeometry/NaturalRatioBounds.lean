module
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.NaturalFamily.RootGeometry
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Placement
public import Theory.Representation.BinaryOffender.FaithfulRankOne

/-!
# Natural fixed-space bounds for symplectic four-space

Elementary subgroups are conjugate into the actual plane or point radical.
In the plane radical, an extra fixed vector places the subgroup in a long
root, of rank at most r. Otherwise its fixed codimension is 2r. In the point
radical, an element outside the plane radical already has fixed codimension
at least 2r. If the subgroup has an extra fixed vector, its matrices are
determined by two field parameters, so its rank is at most 2r. Otherwise it
fixes precisely the point and has codimension 3r. Hence all actors of ratio
below one are conjugate into a plane radical, and every elementary actor
has ratio at least 2/3.

This uses natural-module codimensions throughout. In particular it does not
assert that every subgroup outside the plane radical has codimension 3r.
Source: Aschbacher–Smith, K.3.4.1, printed p.456 (PDF p.467).
-/

public section
open scoped Matrix ENNReal
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open SymplecticConjugatePair
namespace SymplecticConjugatePair.NaturalBounds
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [CharP F 2] in
/-- Natural fixed codimensions are multiples of the coefficient-field degree. -/
lemma natural_fixedCodim_multiple {r : ℕ} (hF : Nat.card F = 2 ^ r)
    (A : Subgroup (Sp F)) : r ∣ fixedCodim binaryNatural A := by
  let W := Representation.invariants ((symplecticNatural (k := F) 2).comp A.subtype)
  have hW : fixedSpace binaryNatural A = W.restrictScalars (ZMod 2) := by
    ext v
    rfl
  unfold fixedCodim
  rw [hW, (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) W).finrank_eq,
    ← Module.finrank_mul_finrank (ZMod 2) F, coefficient_finrank hF]
  exact dvd_mul_right _ _

/-- Faithfulness makes each nontrivial natural fixed codimension at least r. -/
lemma natural_fixedCodim_lower {r : ℕ} (hF : Nat.card F = 2 ^ r)
    {A : Subgroup (Sp F)} (hA : A ≠ ⊥) : r ≤ fixedCodim binaryNatural A := by
  have hf : Function.Injective (binaryNatural (F := F)) := natural_injective
  have hp := fixedCodim_pos_of_faithful (binaryNatural (F := F)) hf hA
  exact Nat.le_of_dvd hp (natural_fixedCodim_multiple hF A)

/-- The actual plane-radical root alternative gives the ratio bound. -/
lemma plane_subgroup_natural_bound {r : ℕ} (hF : Nat.card F = 2 ^ r)
    {A : Subgroup (Sp F)} (hA : A ≤ planeRadical) (hne : A ≠ ⊥) :
    2 * rank A ≤ 3 * fixedCodim binaryNatural A := by
  by_cases he : fixedSpace binaryNatural A = (plane F).restrictScalars (ZMod 2)
  · have hc := fixedCodim_add_finrank (binaryNatural (F := F)) A
    rw [he, finrank_binary_plane hF, finrank_vector hF] at hc
    have hr := Nat.log_mono_right (b := 2) (Subgroup.card_le_of_le hA)
    change rank A ≤ rank (planeRadical (F := F)) at hr
    rw [rank_planeRadical hF] at hr
    omega
  · obtain ⟨R, hR, hAR⟩ := exists_sylowTransvectionRoot_of_fixedSpace_ne hA he
    have hr := hR.rank_le hF hAR
    have hc := natural_fixedCodim_lower hF hne
    omega

omit [Finite F] in
/-- Fixed vectors for the literal point-radical matrix. -/
lemma point_element_fixed_iff (u v z : F) (x : Vector F) :
    binaryNatural (pointRadicalElement u v z).val x = x ↔
      v * x (.inl 1) + z * x (.inr 0) + u * x (.inr 1) = 0 ∧
      u * x (.inr 0) = 0 ∧ v * x (.inr 0) = 0 := by
  change (pointRadicalMatrix u v z *ᵥ x) = x ↔ _
  simp [pointRadicalMatrix, funext_iff, Sum.forall, Fin.forall_fin_two,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
    fromBlocks, add_assoc, and_assoc]

/-- Outside the plane radical, the point-radical upper-left coordinate is nonzero. -/
lemma point_outside_plane_parameters {A : Subgroup (Sp F)}
    (hA : A ≤ SymplecticConjugatePair.pointRadical) (hn : ¬ A ≤ planeRadical) :
    ∃ u v z : F, (pointRadicalElement u v z).val ∈ A ∧ v ≠ 0 := by
  obtain ⟨g, hg, hp⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨u,v,z,rfl⟩ := (mem_pointRadical_iff g).mp (hA hg)
  refine ⟨u,v,z,hg,?_⟩
  intro hv
  apply hp
  rw [pointRadicalElement_eq_coordinate, planeRadical_eq_wing]
  exact ⟨CentralRootGeometry.element v z u 0,
    (CentralRootGeometry.element_mem_wing true v z u 0).mpr hv, rfl⟩

/-- The weaker point-radical bound needed for the sharp natural ratio. -/
lemma point_outside_plane_fixedCodim {r : ℕ} (hF : Nat.card F = 2 ^ r)
    {A : Subgroup (Sp F)} (hA : A ≤ SymplecticConjugatePair.pointRadical)
    (hn : ¬ A ≤ planeRadical) : 2 * r ≤ fixedCodim binaryNatural A := by
  obtain ⟨u,v,z,hg,hv⟩ := point_outside_plane_parameters hA hn
  let f : fixedSpace (binaryNatural (F := F)) A →ₗ[ZMod 2] (F × F) :=
    { toFun := fun x => (x.val (.inl 0), x.val (.inr 1))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_bot_iff.mp
    intro x hx
    have hz := (point_element_fixed_iff u v z x.val).mp (x.property ⟨_,hg⟩)
    have hc : x.val (.inr 0) = 0 := (mul_eq_zero.mp hz.2.2).resolve_left hv
    have he : x.val (.inl 0) = 0 ∧ x.val (.inr 1) = 0 := by
      exact Prod.mk.inj hx
    have hb : x.val (.inl 1) = 0 := by
      have hh := hz.1
      rw [hc,he.2,mul_zero,mul_zero,add_zero,add_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left hv
    apply Subtype.ext
    funext i
    fin_cases i <;> simp_all
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  have hc := fixedCodim_add_finrank (binaryNatural (F := F)) A
  rw [Module.finrank_prod, coefficient_finrank hF] at hd
  rw [finrank_vector hF] at hc
  omega

/-- An extra point-radical fixed vector leaves at most two independent field parameters. -/
lemma point_extra_fixed_rank_le {r : ℕ} (hF : Nat.card F = 2 ^ r)
    {A : Subgroup (Sp F)} (hA : A ≤ SymplecticConjugatePair.pointRadical)
    (hn : ¬ A ≤ planeRadical)
    (hex : fixedSpace binaryNatural A ≠ (point F).restrictScalars (ZMod 2)) :
    rank A ≤ 2 * r := by
  have hle : (point F).restrictScalars (ZMod 2) ≤ fixedSpace binaryNatural A := by
    rw [← pointRadical_natural_fixedSpace]
    intro x hx g
    exact hx ⟨g.val,hA g.property⟩
  have hnle : ¬ fixedSpace binaryNatural A ≤ (point F).restrictScalars (ZMod 2) :=
    fun hh => hex (le_antisymm hh hle)
  obtain ⟨x,hx,hxp⟩ := SetLike.not_le_iff_exists.mp hnle
  obtain ⟨u,v,z,hg,hv⟩ := point_outside_plane_parameters hA hn
  have hfix := (point_element_fixed_iff u v z x).mp (hx ⟨_,hg⟩)
  have hc : x (.inr 0) = 0 := (mul_eq_zero.mp hfix.2.2).resolve_left hv
  have hd : x (.inr 1) ≠ 0 := by
    intro hd
    have he := hfix.1
    rw [hc,hd,mul_zero,mul_zero,add_zero,add_zero] at he
    have hb : x (.inl 1) = 0 := (mul_eq_zero.mp he).resolve_left hv
    apply hxp
    exact (mem_point_iff x).mpr ⟨hb,by intro i; fin_cases i <;> assumption⟩
  let f : A → F × F := fun a =>
    (a.val.val (.inl 0) (.inl 1), a.val.val (.inl 0) (.inr 0))
  have hf : Function.Injective f := by
    intro a b hab
    obtain ⟨ua,va,za,ha⟩ := (mem_pointRadical_iff a.val).mp (hA a.property)
    obtain ⟨ub,vb,zb,hb⟩ := (mem_pointRadical_iff b.val).mp (hA b.property)
    have he : (va,za) = (vb,zb) := by
      change (a.val.val (.inl 0) (.inl 1), a.val.val (.inl 0) (.inr 0)) =
        (b.val.val (.inl 0) (.inl 1), b.val.val (.inl 0) (.inr 0)) at hab
      rw [← ha, ← hb] at hab
      exact hab
    have hfa := (point_element_fixed_iff ua va za x).mp (by rw [ha]; exact hx a)
    have hfb := (point_element_fixed_iff ub vb zb x).mp (by rw [hb]; exact hx b)
    obtain ⟨hvab,hzab⟩ := Prod.mk.inj he
    have huab : ua = ub := by
      apply (mul_left_inj' hd).mp
      apply add_left_cancel (a := va * x (.inl 1) + za * x (.inr 0))
      rw [hfa.1,hvab,hzab,hfb.1]
    apply Subtype.ext
    rw [← ha, ← hb, huab,hvab,hzab]
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,hF,← pow_add] at hcard
  have hrank := Nat.log_mono_right (b := 2) hcard
  rw [Nat.log_pow (by decide : 1 < 2)] at hrank
  change rank A ≤ r + r at hrank
  omega

/-- The valid replacement for the source's overstrong codimension-3r assertion. -/
lemma point_outside_plane_rank_le_fixedCodim {r : ℕ} (hF : Nat.card F = 2 ^ r)
    {A : Subgroup (Sp F)} (hA : A ≤ SymplecticConjugatePair.pointRadical)
    (hn : ¬ A ≤ planeRadical) : rank A ≤ fixedCodim binaryNatural A := by
  by_cases he : fixedSpace binaryNatural A = (point F).restrictScalars (ZMod 2)
  · have hc := fixedCodim_add_finrank (binaryNatural (F := F)) A
    rw [he, finrank_binary_point hF, finrank_vector hF] at hc
    have hr := Nat.log_mono_right (b := 2) (Subgroup.card_le_of_le hA)
    change rank A ≤ rank (SymplecticConjugatePair.pointRadical (F := F)) at hr
    rw [rank_pointRadical hF] at hr
    omega
  · exact (point_extra_fixed_rank_le hF hA hn he).trans
      (point_outside_plane_fixedCodim hF hA hn)

/-- A point-radical subgroup with ratio below one lies in the plane radical. -/
lemma point_small_ratio_le_plane {r : ℕ} (hF : Nat.card F = 2 ^ r)
    {A : Subgroup (Sp F)} (hA : A ≤ SymplecticConjugatePair.pointRadical)
    (hE : IsElementaryTwo A) (hlt : actionRatio binaryNatural A < 1) : A ≤ planeRadical := by
  by_contra hn
  have hc : fixedCodim (binaryNatural (F := F)) A < rank A :=
    (actionRatio_lt_one_iff (binaryNatural (F := F)) hE).mp hlt
  exact (not_lt_of_ge (point_outside_plane_rank_le_fixedCodim hF hA hn)) hc

/-- Every elementary actor of ratio below one is conjugate into a plane radical. -/
lemma elementary_small_ratio_conjugate_plane {r : ℕ}
    (hF : Nat.card F = 2 ^ r) (hr : 0 < r)
    {A : Subgroup (Sp F)} (hA : IsElementaryTwo A)
    (hlt : actionRatio binaryNatural A < 1) :
    ∃ g : Sp F, A.map (MulAut.conj g).toMonoidHom ≤ planeRadical := by
  let := hA.2
  obtain ⟨g,hg | hg⟩ := elementary_conjugate_radical hF hr A
  · refine ⟨g,point_small_ratio_le_plane hF hg ?_ ?_⟩
    · refine ⟨?_,IsElementaryAbelian.map _⟩
      exact (A.map_eq_bot_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective).not.mpr hA.1
    · simpa only [actionRatio,rank_map_conj,fixedCodim_map_conj] using hlt
  · exact ⟨g,hg⟩


/-- Integral form of the natural ratio lower bound for every elementary actor. -/
lemma elementary_natural_bound {r : ℕ} (hF : Nat.card F = 2 ^ r) (hr : 0 < r)
    {A : Subgroup (Sp F)} (hA : IsElementaryTwo A) :
    2 * rank A ≤ 3 * fixedCodim binaryNatural A := by
  let := hA.2
  obtain ⟨g,hg | hg⟩ := elementary_conjugate_radical hF hr A
  · by_cases hp : A.map (MulAut.conj g).toMonoidHom ≤ planeRadical
    · have hne := (A.map_eq_bot_iff_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).not.mpr hA.1
      have hh := plane_subgroup_natural_bound hF hp hne
      rwa [rank_map_conj, fixedCodim_map_conj] at hh
    · have hc := point_outside_plane_rank_le_fixedCodim hF hg hp
      rw [rank_map_conj, fixedCodim_map_conj] at hc
      omega
  · have hne := (A.map_eq_bot_iff_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).not.mpr hA.1
    have hh := plane_subgroup_natural_bound hF hg hne
    rwa [rank_map_conj, fixedCodim_map_conj] at hh

/-- Every nontrivial elementary subgroup has natural action ratio at least 2/3. -/
lemma elementary_natural_ratio_lower {r : ℕ} (hF : Nat.card F = 2 ^ r) (hr : 0 < r)
    {A : Subgroup (Sp F)} (hA : IsElementaryTwo A) :
    (2 : ℝ≥0∞) / 3 ≤ actionRatio binaryNatural A := by
  have hn : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast hA.rank_pos.ne'
  have hb := elementary_natural_bound hF hr hA
  rw [actionRatio, ENNReal.le_div_iff_mul_le (Or.inl hn) (Or.inl (by simp)),
    div_eq_mul_inv, mul_right_comm _ (3 : ℝ≥0∞)⁻¹, ← div_eq_mul_inv,
    ENNReal.div_le_iff (by norm_num) (by simp)]
  exact_mod_cast (show 2 * rank A ≤ fixedCodim binaryNatural A * 3 by omega)

end SymplecticConjugatePair.NaturalBounds
