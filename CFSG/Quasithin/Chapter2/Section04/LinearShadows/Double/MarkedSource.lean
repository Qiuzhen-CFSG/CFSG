module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.HallSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.FixedSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.Geometry
/-!
# The marked outside element and the trivial torus fixed subgroup

Hall conjugacy adjusts the original outside element by an element of
J(S), preserving both marked conjugate modules. The common torus fixed
subgroup centralizes the two blocks; the source supplement makes it
normal in H. The original 2.4.4 normalizer barrier therefore makes it
trivial. The actual core decomposition retains its central factor until
this step.

Source: Aschbacher--Smith, Section 2.4, printed p.540.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.LinearDouble
open ChapterC.Section05.ConjugateSource LinearShadows.Double
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
private theorem right_conjugate_eq_of_normalizer_mul
    (U : Subgroup G) {r x y : G} (hr : r ∈ normalizer (U : Set G)) (he : r*x=y) :
    U.map (MulAut.conj x⁻¹).toMonoidHom = U.map (MulAut.conj y⁻¹).toMonoidHom := by
  have hi := mem_normalizer_iff_map_conj_eq.mp ((normalizer (U : Set G)).inv_mem hr)
  change U.map (MulAut.conj r⁻¹).toMonoidHom = U at hi
  have hf : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj r⁻¹).toMonoidHom =
      (MulAut.conj y⁻¹).toMonoidHom := by
    ext z
    rw [←he]
    simp [mul_assoc]
  have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hi
  rw [Subgroup.map_map,hf] at hh
  exact hh.symm

/-- The central factor in the core is already contained in J(S). -/
theorem source_core_decomposition
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    {M₀ : Subgroup G} {n : ℕ} (c : DoubleLinearSourceSetup d M₀ n) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    twoCore d.H = (sourceModule (d.block.map d.H.subtype) ⊔ sourceModule c.second) ⊔
      (R ⊓ centralizer ((d.block.map d.H.subtype ⊔ c.second : Subgroup G) : Set G)) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  have hR : R ≤ S := sSup_le fun _ h => h.1
  have hQ := d.core_source hG T hST
  have hQR : twoCore d.H ≤ R := le_sSup hQ.2.2
  have hCR : S ⊓ centralizer (d.L0.map d.H.subtype : Set G) ≤ R :=
    (le_sup_right.trans_eq hQ.2.1.symm).trans hQR
  have he : S ⊓ centralizer (d.L0.map d.H.subtype : Set G) =
      R ⊓ centralizer (d.L0.map d.H.subtype : Set G) :=
    le_antisymm (le_inf hCR inf_le_right) (inf_le_inf hR le_rfl)
  change twoCore d.H = (sourceModule (d.block.map d.H.subtype) ⊔ sourceModule c.second) ⊔
    (R ⊓ centralizer ((d.block.map d.H.subtype ⊔ c.second : Subgroup G) : Set G))
  rw [c.join,←he,←(d.two_block_closures c.second c.permutes c.exchange).2]
  exact hQ.2.1

/-- A Hall adjustment inside J(S) preserves both marked conjugate modules.
The original 2.4.4 normalizer equality then kills the complete fixed subgroup. -/
theorem source_marked_fixed_free_torus
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    {M₀ : Subgroup G} {n : ℕ} (c : DoubleLinearSourceSetup d M₀ n)
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀) (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (b : PairedBorelData M ((d.S : Subgroup d.H).map d.H.subtype)
      (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
      (d.block.map d.H.subtype) c.second d.H n) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    ∃ x ∈ M₀, x ∉ S ∧ x ∈ normalizer (R : Set G) ∧ x ∈ normalizer (b.torus : Set G) ∧
      (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom =
        (sourceModule (d.block.map d.H.subtype)).map (MulAut.conj c.x⁻¹).toMonoidHom ∧
      (sourceModule c.second).map (MulAut.conj x⁻¹).toMonoidHom =
        (sourceModule c.second).map (MulAut.conj c.x⁻¹).toMonoidHom ∧
      (twoCore d.H).map (MulAut.conj x⁻¹).toMonoidHom =
        (twoCore d.H).map (MulAut.conj c.x⁻¹).toMonoidHom ∧
      R ⊓ centralizer (b.torus : Set G) = ⊥ := by
  let := c.field₁_field
  let := c.field₂_field
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let L₁ := d.block.map d.H.subtype
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hBR : ChapterB.baumann S = R := (c.core_span hi).1
  have hSQ : S ≤ normalizer (twoCore d.H : Set G) := (map_subtype_le _).trans (le_normalizer_twoCore _)
  have hcS : c.x ∉ S := by
    intro hx
    have he := mem_normalizer_iff_map_conj_eq.mp (hSQ (S.inv_mem hx))
    exact (c.family_members_distinct hi).1 he.symm
  have hMR : M₀ ≤ normalizer (R : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change R.map (MulAut.conj x).toMonoidHom = R
    have hs : S.map (MulAut.conj x).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp (c.original.R_normal hx)
    rw [←Stellmacher.elementaryAbelianMaxJ_map_equiv,hs]
  have hfrat := source_torus_frattini d hG T hM hTM hu hST c hL hSM hMT hi b
  have hc : c.x ∈ (R : Set G) * ((M₀ ⊓ normalizer (b.torus : Set G) : Subgroup G) : Set G) :=
    hfrat ▸ c.x_mem
  obtain ⟨r,hr,x,hx,he⟩ := hc
  have hxS : x ∉ S := by
    intro hs
    exact hcS (he ▸ S.mul_mem (hRS hr) hs)
  have hU₁ : R ≤ normalizer (sourceModule L₁ : Set G) := by
    rw [←hBR]
    exact c.marked₁.coordinates.normalizes
  have hU₂ : R ≤ normalizer (sourceModule c.second : Set G) := by
    rw [←hBR]
    exact c.marked₂.coordinates.normalizes
  have hdec := (source_decomposition d hG T hST c hL hSM hMT hi).1
  obtain ⟨hc₁,hc₂⟩ := factor_core_central_bounds d hG T hST c
  have hfix := paired_fixed_centralizes R L₁ c.second
    (R ⊓ centralizer ((L₁ ⊔ c.second : Subgroup G) : Set G)) b.first.torus b.second.torus
    hL c.second_type hc₁ hc₂ b.first.sylow b.second.sylow b.first.sylow_eq b.second.sylow_eq
    c.commutes inf_le_right hdec (b.first.le_intersection.trans inf_le_right)
    (b.second.le_intersection.trans inf_le_right) b.first.odd b.second.odd
    b.first.nontrivial b.second.nontrivial
  have hNR : S ⊓ normalizer (b.torus : Set G) ≤ normalizer (R : Set G) :=
    (inf_le_left.trans hSM).trans hMR
  have hz := centralizer_eq_bot_of_source_generation d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl
    T hST.le R b.torus (L₁ ⊔ c.second) (S ⊓ normalizer (b.torus : Set G))
    hRS b.supplement hNR inf_le_right hfix x (hMT hx.1) hxS (hMR hx.1) hx.2
  exact ⟨x,hx.1,hxS,hMR hx.1,hx.2,
    right_conjugate_eq_of_normalizer_mul _ (hU₁ hr) he,
    right_conjugate_eq_of_normalizer_mul _ (hU₂ hr) he,
    right_conjugate_eq_of_normalizer_mul _ (hSQ (hRS hr)) he,hz⟩
end CFSG.Quasithin.Chapter2.LinearDouble
