module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceExteriorTensor
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.PointObstruction
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.CubicObstruction
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSeedNormalizer
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.EarlierGeometry

/-!
# Critical geometry from the original tensor seed

The point-normalizer obstruction applies to any conjugate of V_H with
nontrivial image in H/O₂(H). Natural transitivity and the actual two-core
correct its line to the line chosen by the original tensor conjugator g.
The same conjugation carries V_H, so the constructed intersection U₀ and
index eight force K to centralize H_C/V_H, contradicting chief movement.

The original first-tensor inputs construct the compatible exterior action
and both needed indices. If A₁ lies in U_H, line alignment centralizes the
two U-groups; the earlier 13.8.27(3) case-one implication then gives the
nontrivial image needed by the point obstruction. This excludes case (1).
Applying the same obstruction at the inverse of the critical conjugator
also excludes V₁ from Uγ. The source edge cores and seed normalizer then
give all three conclusions of 13.8.32, including the literal intersections.
No reciprocal excluded line, exterior marking or critical index is assumed.

The final consumer takes three noncentral factors on the literal
L₀-intersection with H_C/V_H. It derives chief movement and the prohibition
of a unique four-dimensional factor, then applies the full terminal
chief-section argument. H_C/V_H is not assumed elementary abelian.

The compatible extra-line movement and nine-factor/three-factor lower bound
remain to be proved by this owner. The original setup, factor maps, natural
marking, core bounds and 13.8.27(3) implication retain their earlier-source
producers; qt-d-1381-source owns their final discharge. This conditional
consumer does not establish the complete source Theorem 13.8.28.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.27(3),13.8.29(3),(5),13.8.31--32 and the terminal contradiction,
printed pp.963--966. Right source conjugation is represented by conjBy g⁻¹.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open BinaryLinear.OuterCyclic CriticalGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The point obstruction applies to any actual conjugate with nontrivial
image, using the original tensor conjugator for comparison. -/
theorem source_conjugate_line_not_le_of_movement
    (H K V V1 V2 V3 : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V3) V1 ρ)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hact : ∀ h w, ρ h w = e (QuotientGroup.mk' (pCore 2 H) h) w)
    (hH : H = normalizer (V1 : Set G)) (hV1 : Nat.card V1 = 2)
    (hcomm : ⁅Source.UH H V3,H.pCoreIn 2⁆ ≤ V1)
    (hseed : ⁅V3,H.pCoreIn 2⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : IsPPerfect 2 K)
    (hVH : Source.VH H V ≤ H) (hpVH : IsPGroup 2 (Source.VH H V))
    (h12 : V1 ≤ V2) (h2U : V2 ≤ Source.UH H V3)
    (g : G2 V2) (hg : (g:G) ∉ H)
    (hintersection : Source.VH H V ⊓ (Source.VH H V).conjBy ((g:G)⁻¹) =
      U0 (Source.UH H V3) V2)
    (hindex : (U0 (Source.UH H V3) V2).relIndex
      ((Source.VH H V).conjBy ((g:G)⁻¹)) = 8)
    (hmovement : ¬ ⁅Source.HC H V3,K⁆ ≤ Source.VH H V)
    (y : G) (hγH : (Source.VH H V).conjBy y ≤ H)
    (hγQ : ¬ (Source.VH H V).conjBy y ≤ H.pCoreIn 2) :
    ¬ V1.conjBy y ≤ Source.UH H V3 := by
  intro hA
  let A := V1.conjBy y
  let B := V1.conjBy ((g:G)⁻¹)
  have hHQ : H ≤ normalizer (H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 H).le_normalizer_map H.subtype
  have hHZ : H ≤ centralizer (V1 : Set G) := by
    rw [hH]
    exact normalizer_le_centralizer_of_card_two V1 hV1
  have hmove : ⁅Source.UH H V3,H.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    exact hseed (bot_unique ((commutator_mono (le_conjugateSpanBy V3 H) le_rfl).trans_eq he))
  have htrans : ∀ u v : Fin 4 → ZMod 2, u ≠ 0 → v ≠ 0 → ∃ h : H, ρ h u = v := by
    intro u v hu hv
    obtain ⟨a,ha⟩ := exists_linearEquiv_apply_eq hu hv
    obtain ⟨h,hh⟩ := QuotientGroup.mk'_surjective (pCore 2 H) (e.symm a)
    exact ⟨h,by rw [hact,hh,e.apply_symm_apply]; exact ha⟩
  have hcA : Nat.card A = 2 :=
    (card_map_of_injective (MulAut.conj y).injective).trans hV1
  have hcB : Nat.card B = 2 :=
    (card_map_of_injective (MulAut.conj ((g:G)⁻¹)).injective).trans hV1
  have hAZ : ¬ A ≤ V1 := by
    intro hh
    have he : A = V1 := eq_of_le_of_card_ge hh (by rw [hcA,hV1])
    have hy : y ∈ H := hH ▸ mem_normalizer_iff_map_conj_eq.mpr he
    have hfix : (Source.VH H V).conjBy y = Source.VH H V :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy V H hy)
    apply hγQ
    rw [hfix]
    exact le_pCoreIn_of_normalizes hpVH hVH (le_normalizer_conjugateSpanBy V H)
  have hBU : B ≤ Source.UH H V3 := by
    rintro _ ⟨x,hx,rfl⟩
    exact h2U ((mem_normalizer_iff.mp g⁻¹.property x).mp (h12 hx))
  have hBZ : ¬ B ≤ V1 := by
    intro hh
    have he : B = V1 := eq_of_le_of_card_ge hh (by rw [hcB,hV1])
    have hn : (g:G)⁻¹ ∈ H := hH ▸ mem_normalizer_iff_map_conj_eq.mpr he
    exact hg (H.inv_mem_iff.mp hn)
  obtain ⟨k,hk⟩ := d.exists_line_conjugator_of_transitive_binary_kernel
    (H.pCoreIn 2) (pCoreIn_le 2 H) hHQ
    (le_centralizer_iff.mp ((pCoreIn_le 2 H).trans hHZ))
    hV1 hcomm hmove htrans A B hcA hcB hA hBU hAZ hBZ
  have hconj : ((Source.VH H V).conjBy y).conjBy (k:G) =
      (Source.VH H V).conjBy ((g:G)⁻¹) := by
    rw [conjBy_conjBy]
    apply conjugates_eq_of_line_conjugates_eq V1 _
      (hH ▸ le_normalizer_conjugateSpanBy V H)
    exact (conjBy_conjBy V1 _ _).symm.trans hk
  have hBH : (Source.VH H V).conjBy ((g:G)⁻¹) ≤ H := by
    rw [←hconj]
    exact (map_mono hγH).trans_eq (mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer k.property))
  have hBQ : ¬ (Source.VH H V).conjBy ((g:G)⁻¹) ≤ H.pCoreIn 2 := by
    intro hh
    rw [←hconj] at hh
    have hm := map_mono (f := (MulAut.conj ((k:G)⁻¹)).toMonoidHom) hh
    change (((Source.VH H V).conjBy y).conjBy (k:G)).conjBy ((k:G)⁻¹) ≤ (H.pCoreIn 2).conjBy ((k:G)⁻¹) at hm
    have hn : (H.pCoreIn 2).conjBy ((k:G)⁻¹) = H.pCoreIn 2 :=
      mem_normalizer_iff_map_conj_eq.mp (hHQ (H.inv_mem k.property))
    rw [conjBy_inv,hn] at hm
    exact hγQ hm
  exact hmovement (source_aligned_conjugate_centralizes H K V V1 V2 V3 ρ d e hact
    hH hV1 hcomm hseed hKH hK hVH hpVH h12 h2U g hg hBH hBQ hintersection hindex)

omit [Finite G] in
/-- The same natural matrix quotient yields the linear-group equivalence
used by line conjugacy, commuting with the original quotient map. -/
theorem source_natural_quotient_marking
    (H : Subgroup G) (π : H →* SL(4,ZMod 2))
    (hker : π.ker = (Source.QH H).subgroupOf H) (honto : Function.Surjective π) :
    ∃ e : (H ⧸ pCore 2 H) ≃* LinearGroup 4,
      ∀ h w, e (QuotientGroup.mk' (pCore 2 H) h) w = Matrix.mulVec (π h).val w := by
  have hk : π.ker = pCore 2 H := hker.trans
    (comap_map_eq_self_of_injective H.subtype_injective _)
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective π honto).trans (slEquivLinear 4))
  exact ⟨e,fun h w => slEquivLinear_apply 4 (π h) w⟩

open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BinaryParabolicExteriorSquare SingularPresentation
open PlaneSpan (pointSpace firstSpace planeSpace)
open BinaryLinear.FlagCoordinates
open Theory.LinearAlgebra BinaryFivePointStabilizer
variable {K U : Type*} [Group K]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The constructed first tensor and exterior action give both excluded
critical lines, excludes case (1), and gives all three clauses of 13.8.32.
The chief movement and the earlier 13.8.27(3) implication remain explicit. -/
theorem source_critical_geometry_from_original_tensor_seed
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hHeq : H = normalizer (V₁:Set G))
    (A L2 : Subgroup G)
    (hK : ((K2 H V₂).subgroupOf (G2 V₂)).Normal)
    (hG : G2 V₂ = K2 H V₂ ⊔ L2 ⊔ (T:Subgroup G))
    (hV : L2 ⊔ (T:Subgroup G) ≤ normalizer (V:Set G))
    (π : G2 V₂ →* K × Equiv.Perm (Fin 3)) (hπ : Function.Surjective π)
    (hπker : π.ker = pCore 2 (G2 V₂)) (hcore : Q2 V₂ ≤ H)
    (σ : Representation (ZMod 2) K U)
    (κ : ↥(H ⊓ G2 V₂) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V₂) (Source.UH H V₃) V₂ (σ.comp κ))
    (hκker : κ.ker = pCore 2 ↥(H ⊓ G2 V₂))
    (hκ : Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V₂))))
    (hπK : ∀ k : K2 H V₂,
      π (inclusion ((K2_le_localNormalizer H V₂).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V₂) k),1))
    (eI : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hAcore : A.pCoreIn 2 = A ⊓ centralizer (V₂:Set G))
    (hALT : A ≤ L ⊔ (T:Subgroup G)) (hVA : V ≤ A) (hAG : A ≤ G2 V₂)
    (hπI : ∀ a : A, π (inclusion hAG a) = (1,eI (QuotientGroup.mk' (pCore 2 A) a)))
    (hgen : Source.UH H V₃ = conjugateSpanBy V₃ (K2 H V₂))
    (hdim : Module.finrank (ZMod 2) U = 3)
    (g : A) (hg : (g:G) ∉ H)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π₄ : H →* SL(4,ZMod 2))
    (hker : π₄.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π₄)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π₄ h).val w)
    (hpoint : d.imageSpace V₂ = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hplane : d.imageSpace V₃ = plane)
    (eU : QuotientSpace (Pi.single 0 1 : Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U)
    (hcoords : ∀ u : Source.UH H V₃, (dU.coordinates u).toAdd =
      eU ((line (Pi.single 0 1)).mkQ (d.coordinates u).toAdd))
    (hUcard : Nat.card (Source.UH H V₃) = 32)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T:Subgroup G) ≤ N → N = M)
    (hgenerate : L ⊔ (T:Subgroup G) ≤ H ⊔ zpowers (g:G))
    (hF : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T:Subgroup G) H V) (hb : 3 ≤ c.path.length)
    (Kc : Subgroup G) (hKcH : Kc ≤ H) (hKc : IsPPerfect 2 Kc)
    (hseedQ : ⁅V₃,Source.QH H⁆ ≠ ⊥)
    (hseed : ⁅centralizer (V₃:Set G),V⁆ ≤ V₁)
    (hmove : ¬ ⁅Source.HC H V₃,Kc⁆ ≤ Source.VH H V)
    (hcaseone : (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃ ∨
        Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃) →
      c.Aone V₁ ≤ Source.UH H V₃ ∧ ¬ c.Vgamma ≤ Source.QH H) :
    (¬ c.Aone V₁ ≤ Source.UH H V₃) ∧ (¬ V₁ ≤ c.Ugamma V₃) ∧
      Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃ ∧
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃ ∧
      (Source.QH H).relIndex (c.Ugamma V₃) = 2 ∧
      8 ≤ Nat.card (c.Ugamma V₃ ⊓ Source.VH H V : Subgroup G) ∧
      c.Aone V₁ ≤ Source.VH H V := by
  let F := Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let ds := s.toLocalSetup hab
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := ds.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.2.1)
  obtain ⟨p₆,hpV,hpU,hpS,hi64,hintersection⟩ :=
    source_exterior_geometry_from_original_seed s hab h hH hcentral hHeq A L2 hK hG hV
      π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hALT hVA hAG hπI hgen hdim g hg
      ρ d π₄ hker honto hnatural hpoint hplane eU hcoords hUcard hu hgenerate
  let : IsElementaryAbelian 2 (Source.UH H V₃) := IsElementaryAbelian.of_le p₆.kernel_le
  have hUV : U0 (Source.UH H V₃) V₂ ≤ Source.VH H V :=
    hintersection.symm.le.trans inf_le_left
  have hfirst : (Source.UH H V₃).relIndex (U0 (Source.UH H V₃) V₂) = 8 := by
    rw [←p₆.imageSpace_card_eq_relIndex _ hUV,hpU,
      Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,PlaneSpan.firstSpace_finrank]
    decide
  have hsix : (Source.UH H V₃).relIndex (Source.VH H V) = 64 := by
    rw [←p₆.imageSpace_card_eq_relIndex _ le_rfl,p₆.imageSpace_self,
      Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod]
    norm_num [Six]
  have hindex0 : (U0 (Source.UH H V₃) V₂).relIndex (Source.VH H V) = 8 := by
    have hm := relIndex_mul_relIndex (Source.UH H V₃) (U0 (Source.UH H V₃) V₂)
      (Source.VH H V) (UH_le_U0 _ _) hUV
    rw [hfirst,hsix] at hm
    omega
  have hindex : (U0 (Source.UH H V₃) V₂).relIndex
      ((Source.VH H V).conjBy ((g:G)⁻¹)) = 8 := by
    have hi := relIndex_map_map_of_injective (f := (MulAut.conj ((g:G)⁻¹)).toMonoidHom)
      (U0 (Source.UH H V₃) V₂) (Source.VH H V) (MulAut.conj ((g:G)⁻¹)).injective
    change ((U0 (Source.UH H V₃) V₂).conjBy ((g:G)⁻¹)).relIndex
      ((Source.VH H V).conjBy ((g:G)⁻¹)) = _ at hi
    have hn : (U0 (Source.UH H V₃) V₂).conjBy ((g:G)⁻¹) = U0 (Source.UH H V₃) V₂ :=
      mem_normalizer_iff_map_conj_eq.mp
        (G2_normalizes_U0 (Source.UH H V₃) V₂ (hAG g⁻¹.property))
    rw [hn,hindex0] at hi
    exact hi
  obtain ⟨e,he⟩ := source_natural_quotient_marking H π₄ hker honto
  have hact : ∀ a w, ρ a w = e (QuotientGroup.mk' (pCore 2 H) a) w :=
    fun a w => (hnatural a w).trans (he a w).symm
  have hcomm : ⁅Source.UH H V₃,H.pCoreIn 2⁆ ≤ V₁ := by
    rw [commutator_comm]
    exact source_natural_kernel_commutator H (Source.UH H V₃) V₁ (Source.QH H)
      ρ d π₄ hker hnatural (pCoreIn_le 2 H)
  have hcontrol := source_seed_normalizer_le_LT s h hH hcentral ρ d π₄ hker hnatural
  have hforward : c.Vgamma ≤ H := by
    have hh := (SourceCompletion.f9_endpoint_edge_cores F hF c hb).2.trans
      ((pCoreIn_le 2 _).trans inf_le_left)
    rwa [vertexGroup_base] at hh
  have hback : (Source.VH H V).conjBy (c.gb:G)⁻¹ ≤ H :=
    (source_inverse_critical_seed_core F hF c hb hcontrol).trans
      ((pCoreIn_le 2 _).trans inf_le_left)
  have hdisj : V₁ ⊓ c.Aone V₁ = ⊥ :=
    f9_lines_disjoint F hF c hb (fun y hy => s.intersecting_conjugates_commute hab y hy)
  have hline : ¬ c.Aone V₁ ≤ Source.UH H V₃ := by
    intro hA
    have hc := (source_critical_line_forces_centralization L (T:Subgroup G) H V V₁ V₂ V₃ c
      ρ d e hact hHeq s.line_card hcomm hseedQ hA hdisj s.line_le_plane dU.kernel_le
      hUV (inclusion hAG g) hg).2
    have hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃ := by
      apply le_antisymm (commutatorPreimage_le _ _ _)
      apply le_commutatorPreimage le_rfl
      rw [commutator_comm,hc]
      exact bot_le
    exact source_conjugate_line_not_le_of_movement H Kc V V₁ V₂ V₃ ρ d e hact
      hHeq s.line_card hcomm hseedQ hKcH hKc p₆.section_le (IsElementaryAbelian.isPGroup 2 _)
      s.line_le_plane dU.kernel_le (inclusion hAG g) hg hintersection hindex hmove
      (c.gb:G) hforward (hcaseone (Or.inl hDγ)).2 hA
  have hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃ :=
    lt_of_le_of_ne (commutatorPreimage_le _ _ _) (fun he => hline (hcaseone (Or.inr he)).1)
  have hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃ :=
    lt_of_le_of_ne (commutatorPreimage_le _ _ _) (fun he => hline (hcaseone (Or.inl he)).1)
  have houtside : ¬ c.Ugamma V₃ ≤ Source.QH H := by
    intro hh
    apply hDγ.ne
    apply le_antisymm (commutatorPreimage_le _ _ _)
    apply le_commutatorPreimage le_rfl
    rw [commutator_comm]
    exact (commutator_mono le_rfl hh).trans hcomm
  have hbackoutside := source_inverse_critical_image_nontrivial H (Source.UH H V₃) V₁
    (Source.QH H) ρ d π₄ hker hnatural s.line_card (c.gb:G)
    ((map_mono p₆.kernel_le).trans hforward) ((map_mono p₆.kernel_le).trans hback) houtside hline
  have hreverse := source_conjugate_line_not_le_of_movement H Kc V V₁ V₂ V₃ ρ d e hact
    hHeq s.line_card hcomm hseedQ hKcH hKc p₆.section_le (IsElementaryAbelian.isPGroup 2 _)
    s.line_le_plane dU.kernel_le (inclusion hAG g) hg hintersection hindex hmove
    (c.gb:G)⁻¹ hback (fun hh => hbackoutside ((map_mono p₆.kernel_le).trans hh))
  have hbackline : ¬ V₁ ≤ c.Ugamma V₃ := by
    intro hh
    have hm := map_mono (f := (MulAut.conj (c.gb:G)⁻¹).toMonoidHom) hh
    change V₁.conjBy (c.gb:G)⁻¹ ≤ ((Source.UH H V₃).conjBy (c.gb:G)).conjBy (c.gb:G)⁻¹ at hm
    rw [conjBy_inv] at hm
    exact hreverse hm
  let : IsElementaryAbelian 2 (Source.VH F.H F.V) := inferInstanceAs
    (IsElementaryAbelian 2 (Source.VH H V))
  exact ⟨hline,hbackline,hDH,hDγ,source_critical_pair_geometry_of_original_seed F hF V₂ M G₁ s
    h hH hcentral c hb ρ d π₄ hker honto hnatural (action π₄) p₆ (fun _ _ => rfl)
    hseed houtside hline hbackline⟩


/-- Original-input terminal consumer of the three-chief-factor lower bound.
Both excluded critical lines, all 13.8.32 indices, the natural/exterior
section alignment and the unique-four-dimensional-factor obstruction are
proved internally. The remaining chief count is on the literal H_C/V_H
intersection with D; the whole H_C/V_H need not be elementary abelian. -/
theorem source_linear_four_exclusion_from_original_tensor_seed
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hHeq : H = normalizer (V₁:Set G))
    (A L2 : Subgroup G)
    (hK : ((K2 H V₂).subgroupOf (G2 V₂)).Normal)
    (hG : G2 V₂ = K2 H V₂ ⊔ L2 ⊔ (T:Subgroup G))
    (hV : L2 ⊔ (T:Subgroup G) ≤ normalizer (V:Set G))
    (π : G2 V₂ →* K × Equiv.Perm (Fin 3)) (hπ : Function.Surjective π)
    (hπker : π.ker = pCore 2 (G2 V₂)) (hcore : Q2 V₂ ≤ H)
    (σ : Representation (ZMod 2) K U)
    (κ : ↥(H ⊓ G2 V₂) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V₂) (Source.UH H V₃) V₂ (σ.comp κ))
    (hκker : κ.ker = pCore 2 ↥(H ⊓ G2 V₂))
    (hκ : Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V₂))))
    (hπK : ∀ k : K2 H V₂,
      π (inclusion ((K2_le_localNormalizer H V₂).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V₂) k),1))
    (eI : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hAcore : A.pCoreIn 2 = A ⊓ centralizer (V₂:Set G))
    (hALT : A ≤ L ⊔ (T:Subgroup G)) (hVA : V ≤ A) (hAG : A ≤ G2 V₂)
    (hπI : ∀ a : A, π (inclusion hAG a) = (1,eI (QuotientGroup.mk' (pCore 2 A) a)))
    (hgen : Source.UH H V₃ = conjugateSpanBy V₃ (K2 H V₂))
    (hdim : Module.finrank (ZMod 2) U = 3)
    (g : A) (hg : (g:G) ∉ H)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π₄ : H →* SL(4,ZMod 2))
    (hker : π₄.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π₄)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π₄ h).val w)
    (hpoint : d.imageSpace V₂ = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hplane : d.imageSpace V₃ = plane)
    (eU : QuotientSpace (Pi.single 0 1 : Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U)
    (hcoords : ∀ u : Source.UH H V₃, (dU.coordinates u).toAdd =
      eU ((line (Pi.single 0 1)).mkQ (d.coordinates u).toAdd))
    (hUcard : Nat.card (Source.UH H V₃) = 32)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T:Subgroup G) ≤ N → N = M)
    (hgenerate : L ⊔ (T:Subgroup G) ≤ H ⊔ zpowers (g:G))
    (hF : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T:Subgroup G) H V) (hb : 3 ≤ c.path.length)
    (Kc : Subgroup G) (hKcH : Kc ≤ H) (hKc : IsPPerfect 2 Kc)
    (hseedQ : ⁅V₃,Source.QH H⁆ ≠ ⊥)
    (hseed : ⁅centralizer (V₃:Set G),V⁆ ≤ V₁)
    (hcaseone : (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃ ∨
        Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃) →
      c.Aone V₁ ≤ Source.UH H V₃ ∧ ¬ c.Vgamma ≤ Source.QH H)
    (D : Subgroup G) (hDK : D ≤ Kc)
    (Vn Cn : NoncentralChiefRefinement.NormalNode D)
    (hVn : Vn.val = (Source.VH H V).subgroupOf D)
    (hCn : Cn.val = (Source.HC H V₃).subgroupOf D)
    (hthree : ∀ t : NoncentralChiefRefinement.ChiefSeries D,
      t.head = Vn → t.last = Cn → 3 ≤ t.noncentralTwoCount)
    (Q R : Subgroup G) (hQR : Source.QH H ≤ R) (hindex : Q.relIndex R = 4)
    (hcent : Q ⊓ Source.QH H ≤ centralizer (V₃:Set G))
    (hQV : Q ≤ centralizer (V:Set G))
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (hKonto : Function.Surjective
      ((QuotientGroup.mk' (pCore 2 H)).comp (Kc.subgroupOf H).subtype)) : False := by
  let F := Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let ds := s.toLocalSetup hab
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := ds.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.2.1)
  let : IsElementaryAbelian 2 (Source.VH F.H F.V) := inferInstanceAs
    (IsElementaryAbelian 2 (Source.VH H V))
  obtain ⟨p₆,_,_,_,_,_⟩ := source_exterior_geometry_from_original_seed s hab h hH hcentral hHeq
    A L2 hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hALT hVA hAG hπI
    hgen hdim g hg ρ d π₄ hker honto hnatural hpoint hplane eU hcoords hUcard hu hgenerate
  have hVC : Source.VH H V ≤ Source.HC H V₃ := le_inf p₆.section_le
    ((commutator_eq_bot_iff_le_centralizer.mp (commutator_self_eq_bot_iff.mpr
      (inferInstance : IsMulCommutative (Source.VH H V)))).trans (centralizer_le p₆.kernel_le))
  have hmove := source_component_moves_of_three_factors D Kc (Source.VH H V) (Source.HC H V₃)
    hDK Vn Cn hVn hCn hVC hthree
  obtain ⟨hline,hbackline,_,_,hstar,_,_⟩ := source_critical_geometry_from_original_tensor_seed
    s hab h hH hcentral hHeq A L2 hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK eI
    hAcore hALT hVA hAG hπI hgen hdim g hg ρ d π₄ hker honto hnatural hpoint hplane
    eU hcoords hUcard hu hgenerate hF c hb Kc hKcH hKc hseedQ hseed hmove hcaseone
  have houtside : ¬ c.Ugamma V₃ ≤ Source.QH H := by
    intro hh
    have hi := relIndex_eq_one.mpr hh
    omega
  obtain ⟨e,_⟩ := source_natural_quotient_marking H π₄ hker honto
  apply source_linear_four_exclusion_of_original_seed F hF V₂ M G₁ s h hH hcentral c hb
    Q R Kc ρ d π₄ hker honto hnatural (action π₄) p₆ (fun _ _ => rfl) hHeq hseed hseedQ
    houtside hline hbackline hQR hindex hcent hQV hcover e hKcH hKc hmove hKonto
  intro t ht0 ht1 _ hone i hi
  apply source_ambient_no_unique_four_of_three H Kc D (Source.VH H V) (Source.HC H V₃)
    hKcH hDK ?_ t ht0 ht1 hone i hi
  intro r hr0 hr1
  exact hthree r (Subtype.ext (hr0.trans hVn.symm)) (Subtype.ext (hr1.trans hCn.symm))

end CFSG.Quasithin.Chapter13.Section08.LinearFour
