module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesRankOne

/-!
# Normal opposite images and individual involution displacement

The faithful projection kills U, hence W. The decomposition S = W Wᵍ
therefore identifies the opposite image with the image of S itself.
Since the original T normalizes I and S, that image is normal under the
original Sylow image.

Every nonidentity opposite-image element has square-zero displacement
and moves a vector outside the image of S₂. Its displacement on S₂ has
rank at most one, by the conjugate-point commutator bound. Rank-nullity
then bounds its total displacement by rank(A*)+1, using the exact source
index. This uses neither middle-layer fixedness nor [S,S] ≤ V.

Source: Aschbacher--Smith G.2.3 and 5.1.23, printed pp.333--334 and
645--646, refs/quasithin.pdf. These bounds supplement the remaining
ambient abelian-span obstruction; they do not assert its exclusion.
-/

public noncomputable section
open Submodule Module
section Linear
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

private theorem rank_one_middle (f : V →ₗ[k] V) (S : Submodule k V)
    (hr : finrank k (S.map f) ≤ 1) (hf : ∀ v, f (f v) = 0)
    (v : V) (hv : f v ∉ S) (n : ℕ)
    (hS : finrank k S + (n + 1) = finrank k V) :
    finrank k f.range ≤ n + 1 := by
  have hlt : S ⊓ f.ker < f.ker := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro he
    have hm : f v ∈ S ⊓ f.ker := he.symm ▸ (show f v ∈ f.ker from hf v)
    exact hv hm.1
  have hd := (f.domRestrict S).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict] at hd
  have he : ((f.domRestrict S).ker).map S.subtype = S ⊓ f.ker := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hfx⟩
      exact ⟨⟨x,hx⟩,hfx,rfl⟩
  have hk : finrank k (f.domRestrict S).ker = finrank k (S ⊓ f.ker : Submodule k V) := by
    rw [← he, Submodule.finrank_map_subtype_eq]
  rw [hk] at hd
  have hh := Submodule.finrank_lt_finrank_of_lt hlt
  have ht := f.finrank_range_add_finrank_ker
  omega
end Linear

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
open ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

/-- The opposite image is the image of the whole original core. In particular
it is normalized by the original Sylow image, even though the opposite subgroup
itself need not be Sylow invariant. -/
theorem binary_opposite_image_core_and_normalizer
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    let E := ((conjugate (D.W g) g).subgroupOf D.H).map (projection h)
    let P := (D.T.subgroupOf D.H).map (projection h)
    E = ((D.S g).subgroupOf D.H).map (projection h) ∧
      E ≤ P ∧ P ≤ normalizer (E : Set (Actor h)) := by
  intro E P
  have hUT := h.U_normal_in_T.1
  obtain ⟨hI,_,hnorm,hindex,hgI⟩ := binary_source_inputs h b hUT g hgL hgN
  obtain ⟨_,_,_,_,hS,_⟩ :=
    D.binary_source_clauses_three_to_seven h b hUT h.frattini_U_le_point
      g hgL hgN hI (binarySourceCoreEquiv h b hUT g hgL hgN) hnorm hindex
  have hST : D.S g ≤ D.T :=
    (binary_S_le_LT_core hUT g hgL (binaryStarEquiv h.toBaseHypothesis b hUT)
      (binary_source_star_generation h b hUT g hgL hgN)).trans
        h.toBaseHypothesis.binary_core_le_T
  have hTH : D.T ≤ D.H := le_sup_right.trans h.local_le
  have hSH : D.S g ≤ D.H := hST.trans hTH
  have hWH : D.W g ≤ D.H := inf_le_right.trans hSH
  have hAH : conjugate (D.W g) g ≤ D.H := le_sup_right.trans (hS.ge.trans hSH)
  have hWker : (D.W g).subgroupOf D.H ≤ (projection h).ker := by
    intro x hx
    apply (projection_eq_one_iff h x).mpr
    intro u hu
    exact h.commutator_U_core_le_point
      (commutator_mem_commutator hu (h.U_le_core hx.1))
  have hE : E = ((D.S g).subgroupOf D.H).map (projection h) := by
    rw [hS,subgroupOf_sup hWH hAH,Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff _).mpr hWker,bot_sup_eq]
  have hTU : D.T ≤ normalizer (D.U : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hUT).mp h.U_normal_in_T.2
  have hTI : D.T ≤ normalizer (D.I g : Set G) := by
    rw [hI]
    exact (le_inf h.T_normalizes_L hTU).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hTS : D.T ≤ normalizer (D.S g : Set G) := hTI.trans
    (normalizer_le_normalizer_characteristic_image (D.I g) (pCore 2 (D.I g)))
  refine ⟨hE,?_,?_⟩
  · rw [hE]
    exact Subgroup.map_mono (Subgroup.comap_mono hST)
  · rw [hE]
    exact (Subgroup.map_mono ((Subgroup.comap_mono hTS).trans
      ((D.S g).le_normalizer_comap D.H.subtype))).trans
        (((D.S g).subgroupOf D.H).le_normalizer_map (projection h))

private theorem middle_displacement_rank
    (h : D.Hypothesis) (b : D.BinaryNaturalData) (g : G)
    (x : D.H) (hx : (x : G) ∈ conjugate (D.W g) g) :
    Module.finrank (ZMod 2)
      (((conjugationSection h).imageSpace (D.S₂ g)).map (representation h (projection h x) - 1)) ≤ 1 := by
  let c := conjugationSection h
  let ρ := representation h
  let S := c.imageSpace (D.S₂ g)
  let f := ρ (projection h x) - (1 : Module.End (ZMod 2) (Additive (moduleSubgroup h)))
  have hmap : S.map f ≤ c.imageSpace (conjugate D.V₁ g) := by
    rintro _ ⟨v,hv,rfl⟩
    obtain ⟨u,hu,rfl⟩ := (c.mem_imageSpace_iff (D.S₂ g) v).mp hv
    let w : D.U := (⟨(x:G)*u*(x:G)⁻¹,
      (mem_normalizer_iff.mp (c.normalized x.property) u).mp u.property⟩ : D.U)*u⁻¹
    apply (c.mem_imageSpace_iff _ _).mpr
    refine ⟨w,binary_opposite_middle_commutator_conjugate_point h g (commutator_mem_commutator hx hu),?_⟩
    change (c.coordinates (_ * u⁻¹)).toAdd = _
    rw [map_mul,map_inv]
    change (c.coordinates ⟨(x:G)*u*(x:G)⁻¹,_⟩).toAdd + -(c.coordinates u).toAdd = _
    rw [c.equivariant]
    change ρ (projection h x) (c.coordinates u).toAdd + -(c.coordinates u).toAdd = _
    exact (sub_eq_add_neg _ _).symm
  change Module.finrank (ZMod 2) (S.map f) ≤ 1
  have hpoint : Nat.card (conjugate D.V₁ g) = 2 := by
    rw [conjugate,card_map_of_injective (MulAut.conj g⁻¹).injective,b.point_card]
  have hc : Nat.card (c.imageSpace (conjugate D.V₁ g)) ≤ 2 := by
    have hc := c.imageSpace_card_le_relative_index (conjugate D.V₁ g) ⊥ bot_le
    rwa [relIndex_bot_left,hpoint] at hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := c.imageSpace (conjugate D.V₁ g)),Nat.card_zmod] at hc
  have hd : Module.finrank (ZMod 2) (c.imageSpace (conjugate D.V₁ g)) ≤ 1 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [pow_one] using hc
  exact (Submodule.finrank_mono hmap).trans hd

private theorem square_zero_displacement {X M : Type*} [Group X]
    [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) X M) (a : X) (haa : a * a = 1) :
    ∀ v, (ρ a - 1) ((ρ a - 1) v) = 0 := by
  have hneg (v : M) : -v = v := by
    apply neg_eq_of_add_eq_zero_left
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]
  intro v
  change ρ a (ρ a v - v) - (ρ a v - v) = 0
  apply sub_eq_zero.mpr
  rw [map_sub]
  have hh : ρ a (ρ a v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, haa, map_one, Module.End.one_apply]
  rw [hh]
  simp only [sub_eq_add_neg,hneg,add_comm]

set_option backward.isDefEq.respectTransparency false in
/-- Every nonidentity element of the literal opposite image has displacement
at most one more than the rank of that image. No fixed middle layer is assumed. -/
theorem binary_opposite_involution_displacement
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    let E := ((conjugate (D.W g) g).subgroupOf D.H).map (projection h)
    ∀ a ∈ E, a ≠ 1 →
      Module.finrank (ZMod 2) (LinearMap.range (representation h a - 1)) ≤ rank E + 1 := by
  intro E a ha ha1
  obtain ⟨x,hx,rfl⟩ := ha
  let c := conjugationSection h
  let ρ := representation h
  let S := c.imageSpace (D.S₂ g)
  obtain ⟨he,_⟩ := binary_opposite_image h b g hgL hgN
  let : IsElementaryAbelian 2 E := he
  have haa : projection h x * projection h x = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (projection h x) (show projection h x ∈ E from mem_map_of_mem _ hx)
  let f := ρ (projection h x) - (1 : Module.End (ZMod 2) (Additive (moduleSubgroup h)))
  have hfsq : ∀ v, f (f v) = 0 := square_zero_displacement ρ (projection h x) haa
  have hxE : (x : G) ∉ D.S₂ g := by
    intro hh
    have hkx : x ∈ (projection h).ker ⊓ (conjugate (D.W g) g).subgroupOf D.H := by
      rw [binary_opposite_kernel h b g hgL hgN]
      exact hh
    exact ha1 hkx.1
  obtain ⟨u,hu,humove⟩ := binary_opposite_quotient_moves h b g hgL hgN x hx hxE
  have hVS := (binary_opposite_commutator_filtration h b g hgL hgN).2.2.2.2
  have hv : f (c.coordinates ⟨u,hu⟩).toAdd ∉ S := by
    intro hh
    have hh' : ((ρ.comp (projection h)) x - 1) (c.coordinates ⟨u,hu⟩).toAdd ∈
        c.imageSpace (D.S₂ g) := by exact hh
    have hxu := (c.displacement_mem_imageSpace_iff (D.S₂ g) inf_le_left x ⟨u,hu⟩).mp hh'
    rw [sup_eq_left.mpr (h.point_le.trans hVS)] at hxu
    exact humove (by simpa only [commutatorElement_inv] using (D.S₂ g).inv_mem hxu)
  have hsmall : Module.finrank (ZMod 2) (S.map f) ≤ 1 :=
    middle_displacement_rank h b g x hx
  exact rank_one_middle f S hsmall hfsq (c.coordinates ⟨u,hu⟩).toAdd hv (rank E)
    (binary_opposite_middle_codimension h b g hgL hgN)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
