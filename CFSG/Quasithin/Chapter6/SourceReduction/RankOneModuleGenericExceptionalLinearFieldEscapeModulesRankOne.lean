module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesFiltration
public import Theory.Frattini.Intersection
public import Theory.Representation.BinaryConjugationSection.DisplacementBound
public import Theory.Representation.BinaryConjugationSection.DisplacementPreimage
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# The rank-one opposite actor on the original span

The conjugate Frattini bound places [A,S₂] in V₁ᵍ. The natural G.2.3
coordinates also show that every nonidentity opposite-image element moves
U/S₂. If this image has rank one, its displacement squares to zero and
has rank at most one on S₂. A displacement outside S₂ then supplies an
extra fixed vector, giving fixed codimension at most two on U/V₁.

All images use the original faithful projection. The Chapter 12 consumer
reduces the missing strict-rank case to this concrete quadratic offender
in field degree two. This does not identify V₁ᵍ with V₁ or establish the
middle-layer fixedness required by the cubic argument.

Source: Aschbacher--Smith G.2.3 and 5.1.23, printed pp.333--334,645,
refs/quasithin.pdf.
-/

public noncomputable section
open Submodule Module
section Linear
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

private theorem rank_one_middle (f : V →ₗ[k] V) (S : Submodule k V)
    (hr : finrank k (S.map f) ≤ 1) (hf : ∀ v, f (f v) = 0)
    (v : V) (hv : f v ∉ S) :
    finrank k S ≤ finrank k f.ker := by
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
  omega
end Linear

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
open ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

/-- The Frattini bound gives the conjugate point line, not the original point. -/
theorem binary_opposite_middle_commutator_conjugate_point (h : D.Hypothesis) (g : G) :
    ⁅conjugate (D.W g) g,D.S₂ g⁆ ≤ conjugate D.V₁ g := by
  have hd : ⁅D.U,D.U⁆ ≤ D.V₁ := by
    let : Fact (IsPGroup 2 D.U) := ⟨h.U_isPGroup⟩
    rw [← D.U.map_subtype_commutator]
    exact (Subgroup.map_mono (commutator_le_frattini_of_isPGroup (p := 2))).trans
      h.frattini_U_le_point
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hd
  rw [map_commutator] at hh
  exact (commutator_mono (map_mono inf_le_left) inf_le_right).trans hh

/-- Every element outside the literal kernel moves the quotient by S₂. -/
theorem binary_opposite_quotient_moves (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁)
    (x : G) (hx : x ∈ conjugate (D.W g) g) (hxE : x ∉ D.S₂ g) :
    ∃ u ∈ D.U, ⁅u,x⁆ ∉ D.S₂ g := by
  have hUT := h.U_normal_in_T.1
  obtain ⟨hI, he, hnorm, hindex, hgI⟩ := binary_source_inputs h b hUT g hgL hgN
  obtain ⟨hN, hA, σ, d, hS, hprod, hVE, hES, hVC, hVN, hEN,
    hEC, hEE, hcoord, hfinite, hcompl, htensor, hcard, hmarks, hfix⟩ :=
    D.binary_source_clauses_three_to_seven h b hUT h.frattini_U_le_point
      g hgL hgN hI (binarySourceCoreEquiv h b hUT g hgL hgN) hnorm hindex
  let := hN
  let := hA
  have hXS : conjugate (D.W g) g ≤ D.S g := le_sup_right.trans hS.ge
  have hUneW : ¬ D.U ≤ D.W g := by
    intro hu
    have heq : D.W g = D.U := le_antisymm inf_le_left hu
    rw [heq, relIndex_self] at hindex
    omega
  obtain ⟨u, hu, huw⟩ := SetLike.not_le_iff_exists.mp hUneW
  refine ⟨u,hu,fun hcomm => hxE ?_⟩
  let ui : D.I g := ⟨u, mem_sup_left hu⟩
  let xs : D.S g := ⟨x, hXS hx⟩
  have hxc : (d.coordinates xs).toAdd ∈ d.imageSpace (conjugate (D.W g) g) :=
    (d.mem_imageSpace_iff _ _).mpr ⟨xs, hx, rfl⟩
  have hxf : σ (D.binaryCoreProjection g
      (binarySourceCoreEquiv h b hUT g hgL hgN) ui) (d.coordinates xs).toAdd =
      (d.coordinates xs).toAdd := by
    let xa : D.S g := ⟨u * x * u⁻¹,
      (mem_normalizer_iff.mp (d.normalized ui.property) x).mp xs.property⟩
    have hz := (d.coordinates_eq_one_iff (xa * xs⁻¹)).mpr hcomm
    rw [map_mul, map_inv, mul_inv_eq_one] at hz
    exact (d.equivariant ui xs).symm.trans (congrArg Multiplicative.toAdd hz)
  have hxw : (d.coordinates xs).toAdd ∈ d.imageSpace (D.W g) := by
    rw [← (hmarks ui hu huw).1]
    exact sub_eq_zero.mpr hxf
  exact (d.coordinates_eq_one_iff xs).mp (hcompl.disjoint.le_bot ⟨hxw,hxc⟩)

/-- Rank one supplies a concrete quadratic actor of fixed codimension at most two. -/
theorem binary_opposite_rank_one_offender (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁)
    (hrank : rank (((conjugate (D.W g) g).subgroupOf D.H).map (projection h)) = 1) :
    let E := ((conjugate (D.W g) g).subgroupOf D.H).map (projection h)
    IsElementaryTwo E ∧ IsQuadratic (representation h) E ∧
      fixedCodim (representation h) E ≤ 2 := by
  let E := ((conjugate (D.W g) g).subgroupOf D.H).map (projection h)
  let c := conjugationSection h
  let ρ := representation h
  let S := c.imageSpace (D.S₂ g)
  obtain ⟨he,_⟩ := binary_opposite_image h b g hgL hgN
  let : IsElementaryAbelian 2 E := he
  have hn : E ≠ ⊥ := by
    intro hh
    change rank E = 1 at hrank
    simp [hh] at hrank
  have hE : IsElementaryTwo E := ⟨hn,he⟩
  have hcard : Nat.card E = 2 := by
    rw [hE.card_eq_two_pow_rank,hrank,pow_one]
  obtain ⟨a,ha,hall⟩ := (Nat.card_eq_two_iff' (1 : E)).mp hcard
  have hall' (x : Actor h) (hx : x ∈ E) : x = 1 ∨ x = (a : Actor h) := by
    by_cases h₁ : x = 1
    · exact Or.inl h₁
    · exact Or.inr (congrArg Subtype.val (hall ⟨x,hx⟩ (fun hh => h₁ (congrArg Subtype.val hh))))
  have ha1 : (a : Actor h) ≠ 1 := fun hh => ha (Subtype.ext hh)
  have haa : (a : Actor h) * a = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : Actor h) a.property
  have hneg (v : Additive (moduleSubgroup h)) : -v = v := by
    apply neg_eq_of_add_eq_zero_left
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]
  have hf (v : Additive (moduleSubgroup h)) : ρ a (ρ a v - v) = ρ a v - v := by
    rw [map_sub]
    have hh : ρ a (ρ a v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, haa, map_one, Module.End.one_apply]
    rw [hh]
    simp only [sub_eq_add_neg,hneg,add_comm]
  have hquad : IsQuadratic ρ E := by
    intro x hx y hy v
    rcases hall' x hx with rfl | rfl
    · simp
    rcases hall' y hy with rfl | rfl
    · simp
    exact hf v
  let f := ρ (a : Actor h) - (1 : Module.End (ZMod 2) (Additive (moduleSubgroup h)))
  have hfsq (v : Additive (moduleSubgroup h)) : f (f v) = 0 :=
    sub_eq_zero.mpr (hf v)
  have hk : f.ker = fixedSpace ρ E := by
    ext v
    constructor
    · intro hv x
      change ρ (x : Actor h) v = v
      rcases hall' x x.property with heq | heq
      · rw [heq,map_one,Module.End.one_apply]
      · rw [heq]
        exact sub_eq_zero.mp hv
    · intro hv
      exact sub_eq_zero.mpr (hv a)
  obtain ⟨x,hx,hxa⟩ := a.property
  have hxE : (x : G) ∉ D.S₂ g := by
    intro hh
    have hkx : x ∈ (projection h).ker ⊓ (conjugate (D.W g) g).subgroupOf D.H := by
      rw [binary_opposite_kernel h b g hgL hgN]
      exact hh
    exact ha1 (hxa.symm.trans hkx.1)
  obtain ⟨u,hu,humove⟩ := binary_opposite_quotient_moves h b g hgL hgN x hx hxE
  have hVS := (binary_opposite_commutator_filtration h b g hgL hgN).2.2.2.2
  have hv : f (c.coordinates ⟨u,hu⟩).toAdd ∉ S := by
    intro hh
    have hh' : ((ρ.comp (projection h)) x - 1) (c.coordinates ⟨u,hu⟩).toAdd ∈
        c.imageSpace (D.S₂ g) := by simpa only [MonoidHom.comp_apply,hxa] using hh
    have hxu := (c.displacement_mem_imageSpace_iff (D.S₂ g) inf_le_left x ⟨u,hu⟩).mp hh'
    rw [sup_eq_left.mpr (h.point_le.trans hVS)] at hxu
    exact humove (by simpa only [commutatorElement_inv] using (D.S₂ g).inv_mem hxu)
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
    rw [hxa]
    exact (sub_eq_add_neg _ _).symm
  have hsmall : Module.finrank (ZMod 2) (S.map f) ≤ 1 := by
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
  have hker := rank_one_middle f S hsmall hfsq (c.coordinates ⟨u,hu⟩).toAdd hv
  rw [hk] at hker
  have hdim := binary_opposite_middle_codimension h b g hgL hgN
  dsimp only at hdim
  rw [hrank] at hdim
  have hcodim := fixedCodim_add_finrank ρ E
  refine ⟨hE,hquad,?_⟩
  change Module.finrank (ZMod 2) S + (1 + 1) = _ at hdim
  change fixedCodim ρ E ≤ 2
  omega

/-- The rank-one branch gives the global quadratic bound on this same action. -/
theorem binary_opposite_quadraticRatio_le_two_of_rank_one
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁)
    (hrank : rank (((conjugate (D.W g) g).subgroupOf D.H).map (projection h)) = 1) :
    quadraticRatio (representation h) ≤ 2 := by
  obtain ⟨he,hq,hc⟩ := binary_opposite_rank_one_offender h b g hgL hgN hrank
  apply (quadraticRatio_le_two_iff (representation h)).mpr
  refine ⟨_,he,hq,?_⟩
  simpa only [hrank,Nat.mul_one] using hc

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
