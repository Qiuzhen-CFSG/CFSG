module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePointImages
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixThompsonImage
public import Theory.Representation.BinaryPermutation.CoreFixedLine

/-!
# Thompson and Baumann images in the augmentation plane radical

Near-maximum containment bounds every actual maximum elementary image by two.
A nontrivial such image is a single pair transposition. The Thompson subgroup
is inherited by the full plane preimage, so the even rotation of its three
pairs forces all three transpositions into the Thompson image. The fixed
three-space in the augmentation core has precisely the plane radical as its
pointwise stabilizer inside the Sylow image. Thus the Baumann image is the
same radical, and the original action is onto S6.

Two opposite radicals generate S6; their fixed codimensions on the actual
five-dimensional module are two, against four for the two-residual. No
all-subgroup no-strong-offender bound is asserted. The original plane
consumer is FixedCoreSource.Amalgam.PlaneBaumann.
Source: Aschbacher--Smith B.3.4(2), C.1.37, and13.2.2(10),
printed pp.84--85,142--143,878.
-/

public noncomputable section
open Subgroup Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.Offenders.SixCorePlane
open BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
abbrev S := Equiv.Perm (Fin 6)
abbrev W := core (Fin 6)
abbrev rho := coreRepresentation (Fin 6)

theorem cube_eq : Theory.SpecificGroups.SymmetricSix.BinaryFlags.D = Offenders.D 6 := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x (rfl | rfl | rfl)
    · exact pairSwap_mem (n := 6) 0 (by decide)
    · exact pairSwap_mem (n := 6) 1 (by decide)
    · exact pairSwap_mem (n := 6) 2 (by decide)
  · apply (closure_le _).mpr
    rintro x ⟨i,hi,rfl⟩
    fin_cases i <;> exact subset_closure (by simp [pairSwap, swap01, swap23, swap45])

theorem small_offender {A : Subgroup S} (hA : A ≤ Offenders.D 6)
    (hb : IsOffender rho A) (hc : Nat.card A ≤ 2) :
    A = Six.dLattice 1 ∨ A = Six.dLattice 2 ∨ A = Six.dLattice 4 := by
  obtain ⟨r,rfl⟩ := (Six.subgroup_le_D_iff A).mp hA
  have hb := (Six.caseBFamily_dLattice_iff r).mp ((Six.isOffender_core_iff _).mp hb)
  rw [Six.card_dLattice] at hc
  have hcert : ∀ r : Fin 16,
      (r = 1 ∨ r = 2 ∨ r = 4 ∨ 8 ≤ r.val) → (Six.dLatticeIndices r).card ≤ 2 →
      r = 1 ∨ r = 2 ∨ r = 4 := by decide
  rcases hcert r hb hc with rfl | rfl | rfl <;> simp

theorem rotation_generation (N : Subgroup S)
    (hn : pairRotation ∈ normalizer (N : Set S))
    (hs : Six.dLattice 1 ≤ N ∨ Six.dLattice 2 ≤ N ∨ Six.dLattice 4 ≤ N) :
    Offenders.D 6 ≤ N := by
  have hrot {x : S} (hx : x ∈ N) : pairRotation*x*pairRotation⁻¹ ∈ N :=
    (mem_normalizer_iff.mp hn x).mp hx
  have h01_23 : pairRotation*swap01*pairRotation⁻¹ = swap23 := by decide
  have h23_45 : pairRotation*swap23*pairRotation⁻¹ = swap45 := by decide
  have h45_01 : pairRotation*swap45*pairRotation⁻¹ = swap01 := by decide
  have hs1 : swap01 ∈ N ∨ swap23 ∈ N ∨ swap45 ∈ N := by
    rcases hs with hs | hs | hs
    · exact Or.inl (hs (by apply (Six.mem_dLattice_iff _ _).mpr; exact ⟨1, by decide, rfl⟩))
    · exact Or.inr (Or.inl (hs (by apply (Six.mem_dLattice_iff _ _).mpr; exact ⟨2, by decide, rfl⟩)))
    · exact Or.inr (Or.inr (hs (by apply (Six.mem_dLattice_iff _ _).mpr; exact ⟨4, by decide, rfl⟩)))
  have h01 : swap01 ∈ N := by
    rcases hs1 with hs | hs | hs
    · exact hs
    · exact h45_01 ▸ hrot (h23_45 ▸ hrot hs)
    · exact h45_01 ▸ hrot hs
  have h23 : swap23 ∈ N := h01_23 ▸ hrot h01
  have h45 : swap45 ∈ N := h23_45 ▸ hrot h23
  rw [←cube_eq,Theory.SpecificGroups.SymmetricSix.BinaryFlags.D,closure_le]
  rintro x (rfl | rfl | rfl) <;> assumption

theorem core_cube_fixer :
    subspaceKernel rho (fixedSpace rho (Offenders.D 6)) Six.sylowCarrier ≤ Offenders.D 6 := by
  intro g hg
  let v01 : W := ⟨![1,1,0,0,0,0],by rw [mem_core];decide⟩
  let v23 : W := ⟨![0,0,1,1,0,0],by rw [mem_core];decide⟩
  have hv01 : v01 ∈ fixedSpace rho (Offenders.D 6) := by
    apply (mem_fixedSpace_closure_iff rho _ v01).mpr
    rintro a ⟨i,hi,rfl⟩
    fin_cases i <;> decide
  have hv23 : v23 ∈ fixedSpace rho (Offenders.D 6) := by
    apply (mem_fixedSpace_closure_iff rho _ v23).mpr
    rintro a ⟨i,hi,rfl⟩
    fin_cases i <;> decide
  have h01 := hg.2 v01 hv01
  have h23 := hg.2 v23 hv23
  obtain ⟨i,rfl⟩ := (Six.mem_sylowCarrier_iff g).mp hg.1
  have hcert : ∀ i : Fin 16, rho (Six.sylowWords i) v01 = v01 →
      rho (Six.sylowWords i) v23 = v23 →
      ∃ j : Fin 8, Six.sylowWords i = Six.dWords j := by decide
  obtain ⟨j,hj⟩ := hcert i h01 h23
  rw [hj]
  exact (Six.mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨j,rfl⟩


/-- An even permutation carrying the syntheme to an opposite one. -/
abbrev opposite : S := Equiv.swap 1 2 * Equiv.swap 2 4

theorem opposite_even : opposite ∈ alternatingGroup (Fin 6) := by decide

theorem cube_generation : Offenders.D 6 ⊔
    (Offenders.D 6).map (MulAut.conj opposite).toMonoidHom = ⊤ := by
  let I := Offenders.D 6 ⊔ (Offenders.D 6).map (MulAut.conj opposite).toMonoidHom
  have h01 : swap01 ∈ I := mem_sup_left (pairSwap_mem (n := 6) (m := 3) 0 (by decide))
  have h23 : swap23 ∈ I := mem_sup_left (pairSwap_mem (n := 6) (m := 3) 1 (by decide))
  have h45 : swap45 ∈ I := mem_sup_left (pairSwap_mem (n := 6) (m := 3) 2 (by decide))
  have h02 : Equiv.swap 0 2 ∈ I := mem_sup_right
    ⟨swap01,pairSwap_mem (n := 6) (m := 3) 0 (by decide),by decide⟩
  have h34 : Equiv.swap 3 4 ∈ I := mem_sup_right
    ⟨swap23,pairSwap_mem (n := 6) (m := 3) 1 (by decide),by decide⟩
  have h12 : Equiv.swap 1 2 ∈ I := by
    have hh : swap01 * Equiv.swap 0 2 * swap01 = Equiv.swap 1 2 := by decide
    exact hh ▸ I.mul_mem (I.mul_mem h01 h02) h01
  apply top_unique
  rw [←closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5),closure_le]
  rintro x ⟨i,rfl⟩
  fin_cases i
  · exact h01
  · exact h12
  · exact h23
  · exact h34
  · exact h45

private theorem alternating_codim : fixedCodim rho (alternatingGroup (Fin 6)) = 4 := by
  have hf : fixedSpace rho (alternatingGroup (Fin 6)) = coreConstants := by
    ext v
    exact core_fixed_iff_constant (by simp) v
  have hd := fixedCodim_add_finrank rho (alternatingGroup (Fin 6))
  have he : Module.finrank (ZMod 2) (coreConstants (Ω := Fin 6)) = 1 := by
    change Module.finrank (ZMod 2) ((constants (Fin 6)).comap (core (Fin 6)).subtype) = 1
    rw [(Submodule.comapSubtypeEquivOfLe
      ((constants_le_core_iff (Fin 6)).mpr (by decide))).finrank_eq,finrank_constants]
  rw [hf,he,finrank_core] at hd
  change fixedCodim rho (alternatingGroup (Fin 6)) + 1 = 5 at hd
  omega

variable {H : Type*} [Group H] [Finite H]
variable (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
  (q : H →* S) (e : V ≃* Multiplicative W)
  (he : ∀ g v, (e (MulAut.conjNormal g v)).toAdd = rho (q g) (e v).toAdd)

include he

/-- Small actual maximum images force the full plane Thompson image. -/
theorem thompson_image (T : Sylow 2 H) (hVT : V ≤ T)
    (hk : q.ker = pCore 2 H) (hY : alternatingGroup (Fin 6) ≤ q.range)
    (hT : (T : Subgroup H).map q = Six.sylowCarrier ⊓ q.range)
    (hr : 1 < twoRank (T : Subgroup H))
    (hJ : (thompsonJ (T : Subgroup H) 1).map q ≤ Offenders.D 6)
    (hne : (elementaryAbelianMaxJ (T : Subgroup H)).map q ≠ ⊥) :
    (elementaryAbelianMaxJ (T : Subgroup H)).map q = Offenders.D 6 := by
  let R := (Offenders.D 6).comap q
  let J := elementaryAbelianMaxJ (T : Subgroup H)
  have hJ1 : J ≤ thompsonJ (T : Subgroup H) 1 := by
    change elementaryAbelianMaxJ (T : Subgroup H) ≤ _
    rw [←thompsonJ_zero]
    exact lemma_B_2_3_1 _ (by decide) hr
  have hJD : J.map q ≤ Offenders.D 6 := (map_mono hJ1).trans hJ
  have hJR : J ≤ R := map_le_iff_le_comap.mp hJD
  have hRT : R ≤ (T : Subgroup H) := by
    have hkT : q.ker ≤ (T : Subgroup H) := hk ▸ pCore_isPGroup.le_sylow_of_normal T
    rw [←comap_map_eq_self hkT,hT]
    intro x hx
    exact ⟨Six.D_le_sylowCarrier hx,⟨x,rfl⟩⟩
  have hJRe : J = elementaryAbelianMaxJ R := by
    simpa only [thompsonJ_zero] using
      lemma_B_2_3_3 (T : Subgroup H) R (i := 0) (by omega)
        (show thompsonJ (T : Subgroup H) 0 ≤ R by simpa only [thompsonJ_zero] using hJR) hRT
  have hrot : pairRotation ∈ normalizer (J.map q : Set S) := by
    have hy : pairRotation ∈ q.range := hY (by change Equiv.Perm.sign _ = 1; decide)
    obtain ⟨g,hg⟩ := hy
    have hgn : g ∈ normalizer (R : Set H) := by
      apply mem_normalizer_iff.mpr
      intro x
      change q x ∈ Offenders.D 6 ↔ q (g*x*g⁻¹) ∈ Offenders.D 6
      rw [map_mul,map_mul,map_inv,hg,←cube_eq]
      exact mem_normalizer_iff.mp (H2_normalizes_D pairRotation_mem_H2) (q x)
    have hgJ : g ∈ normalizer (J : Set H) := by
      rw [hJRe]
      apply mem_normalizer_iff_map_conj_eq.mpr
      change (elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom = _
      rw [←elementaryAbelianMaxJ_map_equiv]
      exact congrArg elementaryAbelianMaxJ (show R.map (MulAut.conj g).toMonoidHom = R from
        mem_normalizer_iff_map_conj_eq.mp hgn)
    exact hg ▸ J.le_normalizer_map q (mem_map_of_mem q hgJ)
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup H), A.map q ≠ ⊥ := by
    by_contra! hn
    apply hne
    apply (Subgroup.map_eq_bot_iff _).mpr
    exact sSup_le fun A hA => (Subgroup.map_eq_bot_iff _).mp (hn A hA)
  obtain ⟨A,hA,hnA⟩ := hex
  have hAJ : A.map q ≤ J.map q := map_mono (le_sSup hA)
  have hsm := small_offender (hAJ.trans hJD)
    (SixCorePoint.maximum_image_isOffender V q e he (T : Subgroup H) A hVT hA hnA)
    (maximum_image_le_two_of_thompson_one_image_le_D T q hr hY hT hJ A hA)
  apply le_antisymm hJD (rotation_generation _ hrot ?_)
  rcases hsm with hh | hh | hh
  · exact Or.inl (hh ▸ hAJ)
  · exact Or.inr (Or.inl (hh ▸ hAJ))
  · exact Or.inr (Or.inr (hh ▸ hAJ))

/-- The centralizer of the fixed three-space has precisely the same image. -/
theorem baumann_image (T : Sylow 2 H) (hVT : V ≤ T)
    (hT : (T : Subgroup H).map q ≤ Six.sylowCarrier)
    (hJ : (elementaryAbelianMaxJ (T : Subgroup H)).map q = Offenders.D 6) :
    (baumann (T : Subgroup H)).map q = Offenders.D 6 := by
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    apply core_cube_fixer
    refine ⟨hT (mem_map_of_mem q ha.1),?_⟩
    intro w hw
    let v : V := e.symm (Multiplicative.ofAdd w)
    have hvcoord : (e v).toAdd = w := e.apply_symm_apply _
    have hv : (v : H) ∈ V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup H) : Set H) := by
      refine ⟨v.property,fun b hb => ?_⟩
      have hfix : rho (q b) w = w := hw ⟨q b,hJ ▸ mem_map_of_mem q hb⟩
      have heq : MulAut.conjNormal b v = v := by
        apply e.injective
        apply Multiplicative.toAdd.injective
        rw [he,hvcoord,hfix]
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val heq)
    have hva : (v : H) ∈ thompsonAlpha (T : Subgroup H) := by
      have hh := (BaumannArgument.alpha_inf_eq_fixed V (T : Subgroup H) hVT).symm ▸ hv
      exact hh.1
    have hcomm : (v : H)*a = a*(v : H) := ha.2 v hva
    have hfix : MulAut.conjNormal a v = v := by
      apply Subtype.ext
      change a*(v : H)*a⁻¹ = (v : H)
      rw [←hcomm,mul_inv_cancel_right]
    rw [←hvcoord,←he,hfix]
  · rw [←hJ]
    exact map_mono (elementaryAbelianMaxJ_le_baumann _)

omit he [Finite H] in
/-- The noncentral small-image plane branch is necessarily the full S6 action. -/
theorem onto_of_thompson_image (hY : alternatingGroup (Fin 6) ≤ q.range)
    (T : Subgroup H) (hJ : (elementaryAbelianMaxJ T).map q = Offenders.D 6) :
    Function.Surjective q := by
  have ht : swap01 ∈ q.range := map_le_range q _ (hJ.symm ▸ (show swap01 ∈ Offenders.D 6 from pairSwap_mem (n := 6) (m := 3) 0 (by decide)))
  have hi : q.range.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le hY
  rcases (Nat.dvd_prime Nat.prime_two).mp hi with hh | hh
  · exact MonoidHom.range_eq_top.mp (index_eq_one.mp hh)
  · rw [Equiv.Perm.eq_alternatingGroup_of_index_eq_two hh] at ht
    have hn : swap01 ∉ alternatingGroup (Fin 6) := by decide
    exact (hn ht).elim
private def linearCoordinates : Additive V ≃ₗ[ZMod 2] W := by
  let a : Additive V ≃+ W := {
    toFun := fun v => (e v.toMul).toAdd
    invFun := fun w => Additive.ofMul (e.symm (Multiplicative.ofAdd w))
    left_inv := fun v => e.symm_apply_apply v
    right_inv := fun w => e.apply_symm_apply (Multiplicative.ofAdd w)
    map_add' := fun v w => e.map_mul v.toMul w.toMul }
  exact { a with map_smul' := ZMod.map_smul a }

private theorem fixedCodim_eq_model (A : Subgroup H) :
    BaumannArgument.fixedCodim V A = fixedCodim rho (A.map q) := by
  let q0 := q.rangeRestrict
  have hq0 := q.rangeRestrict_surjective
  have hk0 : q0.ker = centralizer (V : Set H) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact SixCorePoint.kernel_centralizer V q e he
  let r := Representation.NormalElementaryQuotient.representation V q0 hq0 hk0
  have heq (a : q.range) (v : Additive V) :
      linearCoordinates V e (r a v) = rho a.val (linearCoordinates V e v) := by
    obtain ⟨a,rfl⟩ := hq0 a
    have h := Representation.NormalElementaryQuotient.representation_apply V q0 hq0 hk0 a v
    have hh : (r (q0 a) v).toMul = MulAut.conjNormal a v.toMul := Subtype.ext h
    change (e _).toAdd = rho (q a) (e v.toMul).toAdd
    rw [hh]
    exact he a v.toMul
  rw [BaumannArgument.fixedCodim_eq_centralizer_quotient V q0 hq0 hk0]
  have hh := fixedCodim_map_equivariant r rho q.range.subtype (linearCoordinates V e) heq (A.map q0)
  rw [map_map] at hh
  exact hh

/-- The two opposite Thompson images each cost two dimensions, whereas the
residual costs four, on the actual augmentation module. -/
theorem fixed_codimensions (hq : Function.Surjective q) (T : Subgroup H)
    (hJ : (elementaryAbelianMaxJ T).map q = Offenders.D 6) :
    BaumannArgument.fixedCodim V (elementaryAbelianMaxJ T) = 2 ∧
      BaumannArgument.fixedCodim V (pResidual 2 H) = 4 := by
  rw [fixedCodim_eq_model V q e he,fixedCodim_eq_model V q e he,
    hJ,map_pResidual_of_surjective 2 q hq,Equiv.Perm.twoResidual_eq_alternating]
  exact ⟨Six.fixedCodim_D.2.2.1,alternating_codim⟩
end CFSG.Quasithin.ChapterB.Offenders.SixCorePlane
