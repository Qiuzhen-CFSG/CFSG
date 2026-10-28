module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Basic
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.LocalStructure
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.PSL2.RankOneRoots

/-!
# Marked coordinates for the linear Section 16 model

Sylow conjugacy and the characteristic-two SL₂–PSL₂ equivalence put the actual
Sylow subgroup at the upper root group. A triangular change of basis then
puts the chosen outside involution at the Weyl matrix. The resulting map
identifies the actual Sylow normalizer with the Borel.

The additive-field model proves the omega and center assertions. Involution
centralizers are Sylow two-subgroups, so two involutions in different Sylow
normalizers have trivial common centralizer. Root generation follows from the
upper-root overgroup calculation, without subgroup classification.

Source: GLS IV, Chapter 4, Lemma 3.2(b,h,j), Lemma 3.4(b,f), and Chapter 2,
Lemmas 16.2–16.4 and Proposition 16.5. The triangular matrix calculation is
extracted from `LocalStructure/LinearBorel.lean`, without its ambient ZD imports.
-/

public section

open Subgroup BenderSuzuki.Converse BenderSuzuki.MatrixGroups
open BenderSuzuki.PFAppendixIII BenderSuzuki.PFchapter1section1
open scoped Pointwise
namespace BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry
variable {G : Type*} [Group G] [Finite G] {n : ℕ}

noncomputable def sylowEquivAdditive (e : G ≃* PSL2BinaryMatrixGroup n)
    (P : Sylow 2 G) : Multiplicative (BinaryGaloisField n) ≃* P := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let f : P ≃* Q := by
    rw [show (Q : Subgroup _) = (P : Subgroup G).map e.toMonoidHom from Sylow.coe_mapSurjective e.surjective P]
    exact (P : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective
  exact (Linear.psl2SylowEquivAdditive Q).trans f.symm

theorem sylow_elementary (e : G ≃* PSL2BinaryMatrixGroup n) (P : Sylow 2 G) :
    IsElementaryAbelian 2 P := by
  let f := sylowEquivAdditive e P
  refine { toIsMulCommutative := IsMulCommutative.of_comm ?_, exponent_dvd_p := ?_ }
  · intro x y
    apply f.symm.injective
    simp only [map_mul, mul_comm]
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply f.symm.injective
    rw [map_pow, map_one]
    change 2 • (f.symm x).toAdd = 0
    exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _)

theorem sylow_card (hn : 0 < n) (e : G ≃* PSL2BinaryMatrixGroup n) (P : Sylow 2 G) :
    Nat.card P = 2 ^ n := by
  rw [← Nat.card_congr (sylowEquivAdditive e P).toEquiv]
  exact card_binaryGaloisField n (by omega)

theorem sylow_omega_eq (e : G ≃* PSL2BinaryMatrixGroup n) (P : Sylow 2 G) :
    omegaOneAmbient (P : Subgroup G) = (P : Subgroup G) := by
  let := sylow_elementary e P
  exact omegaOneAmbient_eq_self _

theorem sylow_center_eq (e : G ≃* PSL2BinaryMatrixGroup n) (P : Sylow 2 G) :
    (center P).map (P : Subgroup G).subtype = (P : Subgroup G) := by
  let := sylow_elementary e P
  rw [Subgroup.center_eq_top, ← MonoidHom.range_eq_map, range_subtype]

variable {F : Type*} [Field F]
theorem unip_eq_upper : Unip F = Matrix.SpecialLinearGroup.upperUnipotent F := by
  ext g
  rw [mem_Unip_iff, Matrix.SpecialLinearGroup.mem_upperUnipotent]
  have ht (t : F) : Matrix.SpecialLinearGroup.transvection
      (i := (0 : Fin 2)) (j := 1) zero_ne_one t = uni t := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.transvection_coe]
  simp only [ht, eq_comm]

theorem unip_normalizer : normalizer (Unip F : Set (SL2 F)) = Borel F := by
  rw [unip_eq_upper]
  ext g
  exact (Matrix.SpecialLinearGroup.mem_rankOneBorel_iff g).trans (mem_Borel_iff g).symm

theorem exists_sylow_coordinates (e : G ≃* PSL2BinaryMatrixGroup n) (P : Sylow 2 G) :
    ∃ f : G ≃* SL2 (BinaryGaloisField n),
      (P : Subgroup G).map f.toMonoidHom = Unip (BinaryGaloisField n) := by
  let q := e.trans (Linear.sl2QuotientEquiv (BinaryGaloisField n)).symm
  let Q := P.mapSurjective (f := q.toMonoidHom) q.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL2 (BinaryGaloisField n)) Q
    (Matrix.SpecialLinearGroup.upperUnipotentSylow (BinaryGaloisField n) 2)
  refine ⟨q.trans (MulAut.conj g), ?_⟩
  have hh := congrArg (fun S : Sylow 2 (SL2 (BinaryGaloisField n)) => (S : Subgroup (SL2 (BinaryGaloisField n)))) hg
  change ((P : Subgroup G).map q.toMonoidHom).map (MulAut.conj g).toMonoidHom =
    Matrix.SpecialLinearGroup.upperUnipotent (BinaryGaloisField n) at hh
  rw [Subgroup.map_map, ← unip_eq_upper] at hh
  exact hh

variable [Finite F] [CharP F 2]

theorem exists_borel_conj_weyl {x : SL2 F} (hx : PFAppendixIII.IsInvolution x)
    (hB : x ∉ Borel F) : ∃ b : Borel F, MulAut.conj (b : SL2 F) (weyl F) = x := by
  have hc : x.val 1 0 ≠ 0 := by simpa only [mem_Borel_iff] using hB
  have hdiag : x.val 1 1 = x.val 0 0 := by
    have hh := congrArg (fun a : SL2 F => a.val 1 0) hx.sq_eq_one
    have he : x.val 1 0 * (x.val 0 0 + x.val 1 1) = 0 := by
      simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two, mul_add, mul_comm] using hh
    have hh := (mul_eq_zero.mp he).resolve_left hc
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hh
  have hd : x.val 0 0 ^ 2 + x.val 0 1 * x.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two, hdiag, ← pow_two, sub_eq_add_neg, CharTwo.neg_eq]
      using x.property
  obtain ⟨d, hdc⟩ := isSquare_of_charTwo' (x.val 1 0)
  have hd0 : d ≠ 0 := by intro h; simp [h] at hdc; exact hc hdc
  let b : SL2 F := ⟨!![d⁻¹, x.val 0 0 / d; 0, d], by
    simp [Matrix.det_fin_two, hd0]⟩
  have hb : b ∈ Borel F := by rw [mem_Borel_iff]; rfl
  have hmul : b * weyl F = x * b := by
    apply Subtype.ext
    ext i j
    change (b.val * (weyl F).val) i j = (x.val * b.val) i j
    fin_cases i <;> fin_cases j <;>
      simp [b, Matrix.mul_apply, Fin.sum_univ_two, hdiag, hdc, div_eq_mul_inv,
        mul_assoc, hd0, CharTwo.add_self_eq_zero]
    · field_simp
      rw [hdc] at hd
      linear_combination -hd
    · convert (CharTwo.add_self_eq_zero (x.val 0 0 * d)).symm using 1
      field_simp
  exact ⟨⟨b, hb⟩, by rw [MulAut.conj_apply, hmul, mul_assoc, mul_inv_cancel, mul_one]⟩

theorem exists_marked_coordinates (e : G ≃* PSL2BinaryMatrixGroup n) (P : Sylow 2 G)
    {t : G} (ht : IsInvolution t) (htB : t ∉ normalizer ((P : Subgroup G) : Set G)) :
    ∃ f : G ≃* SL2 (BinaryGaloisField n),
      (P : Subgroup G).map f.toMonoidHom = Unip (BinaryGaloisField n) ∧
      (normalizer ((P : Subgroup G) : Set G)).map f.toMonoidHom = Borel (BinaryGaloisField n) ∧
      f t = weyl (BinaryGaloisField n) := by
  obtain ⟨q, hq⟩ := exists_sylow_coordinates e P
  have hqB : (normalizer ((P : Subgroup G) : Set G)).map q.toMonoidHom = Borel (BinaryGaloisField n) := by
    rw [map_equiv_normalizer_eq, hq, unip_normalizer]
  have htq : q t ∉ Borel (BinaryGaloisField n) := by
    rw [← hqB, mem_map_equiv]
    simpa using htB
  obtain ⟨b, hb⟩ := exists_borel_conj_weyl
    (BenderSuzuki.IsInvolution.map_of_injective ht q.toMonoidHom q.injective) htq
  let f := q.trans (MulAut.conj (b : SL2 (BinaryGaloisField n))⁻¹)
  have hf : (P : Subgroup G).map f.toMonoidHom = Unip (BinaryGaloisField n) := by
    change (P : Subgroup G).map
      ((MulAut.conj (b : SL2 (BinaryGaloisField n))⁻¹).toMonoidHom.comp q.toMonoidHom) = _
    rw [← Subgroup.map_map, hq]
    apply (mem_normalizer_iff_map_conj_eq).mp
    rw [unip_normalizer]
    exact (Borel _).inv_mem b.property
  refine ⟨f, hf, ?_, ?_⟩
  · rw [map_equiv_normalizer_eq, hf, unip_normalizer]
  · change (b : SL2 (BinaryGaloisField n))⁻¹ * q t *
      (b : SL2 (BinaryGaloisField n))⁻¹⁻¹ = _
    change MulAut.conj (b : SL2 (BinaryGaloisField n)) (weyl _) = q t at hb
    rw [← hb, MulAut.conj_apply]
    simp [mul_assoc]

/-- A nonidentity element of P has centralizer exactly P. -/
theorem centralizer_involution (e : G ≃* PSL2BinaryMatrixGroup n) (P : Sylow 2 G)
    {z : G} (hz : IsInvolution z) (hzP : z ∈ P) : centralizer {z} = (P : Subgroup G) := by
  let := sylow_elementary e P
  have hz2 : orderOf (e z) = 2 := by
    exact (orderOf_injective e.toMonoidHom e.injective z).trans
      (orderOf_eq_prime hz.sq_eq_one hz.ne_one)
  obtain ⟨_, _, _, _, _, hC⟩ := Theory.PSL2.involution_root_geometry (e z) hz2
  have hce : centralizer {z} = (centralizer {e z}).comap e.toMonoidHom := by
    ext x
    simp only [mem_centralizer_singleton_iff, mem_comap, MulEquiv.coe_toMonoidHom]
    exact ⟨fun h => by simpa only [map_mul] using congrArg e h,
      fun h => e.injective (by simpa only [map_mul] using h)⟩
  apply P.is_maximal'
  · rw [hce]
    exact hC.comap_of_injective _ e.injective
  · intro x hx
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : (P : Subgroup G)) ⟨z, hzP⟩)

/-- A root subgroup and any element outside its normalizer generate the group. -/
theorem rootGenerated_eq_top (e : G ≃* PSL2BinaryMatrixGroup n) (P : Sylow 2 G)
    {t : G} (htB : t ∉ normalizer ((P : Subgroup G) : Set G)) :
    rootGenerated (P : Subgroup G) t = ⊤ := by
  rw [rootGenerated, sylow_omega_eq e P]
  obtain ⟨f, hf⟩ := exists_sylow_coordinates e P
  have hB : (normalizer ((P : Subgroup G) : Set G)).map f.toMonoidHom = Borel (BinaryGaloisField n) := by
    rw [map_equiv_normalizer_eq, hf, unip_normalizer]
  let H := ((P : Subgroup G) ⊔ zpowers t).map f.toMonoidHom
  have htop : H = ⊤ := by
    by_contra hne
    have hU : Matrix.SpecialLinearGroup.upperUnipotent (BinaryGaloisField n) ≤ H := by
      rw [← unip_eq_upper, ← hf]
      exact Subgroup.map_mono le_sup_left
    have hle := Matrix.SpecialLinearGroup.overgroup_le_rankOneBorel hU hne
    have ht : f t ∈ Borel (BinaryGaloisField n) :=
      (mem_Borel_iff _).mpr ((Matrix.SpecialLinearGroup.mem_rankOneBorel_iff _).mp
        (hle (Subgroup.mem_map_of_mem _ ((show zpowers t ≤ (P : Subgroup G) ⊔ zpowers t from le_sup_right) (mem_zpowers t)))))
    rw [← hB, mem_map_equiv] at ht
    exact htB (by simpa using ht)
  apply top_unique
  intro x _
  have hx : f x ∈ H := htop ▸ mem_top _
  have hh := mem_map_equiv.mp hx
  simpa using hh

/-- Two root involutions in different Sylow normalizers have trivial common centralizer. -/
theorem common_centralizer_eq_bot (e : G ≃* PSL2BinaryMatrixGroup n) (P : Sylow 2 G)
    {z t : G} (hz : IsInvolution z) (hzP : z ∈ P)
    (htB : t ∉ normalizer ((P : Subgroup G) : Set G)) :
    centralizer {z} ⊓ centralizer {t} = ⊥ := by
  let := sylow_elementary e P
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro x hx
  have hxP : x ∈ P := by
    rw [centralizer_involution e P hz hzP] at hx
    exact hx.1
  by_contra hne
  have hxi : IsInvolution x := ⟨hne, elemPow_eq_one_of_isElementaryAbelian x hxP⟩
  have ht : t ∈ centralizer {x} := by
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.mp hx.2).symm
  rw [centralizer_involution e P hxi hxP] at ht
  exact htB (Subgroup.le_normalizer ht)

theorem common_centralizer_odd (e : G ≃* PSL2BinaryMatrixGroup n) (P : Sylow 2 G)
    {z t : G} (hz : IsInvolution z) (hzP : z ∈ P)
    (htB : t ∉ normalizer ((P : Subgroup G) : Set G)) :
    Odd (Nat.card (centralizer {z} ⊓ centralizer {t} : Subgroup G)) := by
  rw [common_centralizer_eq_bot e P hz hzP htB]
  simp

/-- Fixing both marked involutions forces an inner automorphism to be the identity. -/
theorem inner_fixing_eq_one (e : G ≃* PSL2BinaryMatrixGroup n) (P : Sylow 2 G)
    {z t : G} (hz : IsInvolution z) (hzP : z ∈ P)
    (htB : t ∉ normalizer ((P : Subgroup G) : Set G))
    (a : MulAut G) (hinner : ∃ b : G, a = MulAut.conj b)
    (haz : a z = z) (hat : a t = t) : a = 1 := by
  obtain ⟨b, rfl⟩ := hinner
  have hb : b ∈ centralizer {z} ⊓ centralizer {t} := by
    exact ⟨mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp haz),
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hat)⟩
  rw [common_centralizer_eq_bot e P hz hzP htB, mem_bot] at hb
  simp [hb]
end BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry
