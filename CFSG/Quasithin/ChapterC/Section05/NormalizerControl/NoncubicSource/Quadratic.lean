module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.Natural
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.Alternating
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFamilyKernel
/-!
# The original conjugate module acts quadratically on the auxiliary span

The actual C.5.6 commutator and fixed-space equalities identify the displacement
of Uˣ on V₁ with E=U∩Uˣ. Since E lies in the elementary actor Uˣ, the second
commutator vanishes. The same E is the actor's centralizer kernel and its
intersection with V₁. Both original noncubic markings supply these conclusions;
no new pair or quadratic-action assumption is introduced.
Source: Aschbacher–Smith C.5.13, printed p.162, using C.5.6(2).
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem relative_pair_displacement (U B V N : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 B]
    (hUV : U ≤ V) (hNV : N ≤ normalizer (V : Set G)) (hBN : B ≤ N)
    (hVB : V ≤ normalizer (B : Set G))
    (hp : ⁅U,B⁆ = U ⊓ B) (hc : B ⊓ centralizer (U : Set G) = U ⊓ B) :
    ⁅V,B⁆ = U ⊓ B ∧ B ⊓ centralizer (V : Set G) = U ⊓ B ∧
      B ⊓ V = U ⊓ B ∧ ⁅⁅V,B⁆,B⁆ = ⊥ := by
  have hVC : V ≤ centralizer (U : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hUV)
  have hBV : B ⊓ V = U ⊓ B := le_antisymm
    ((inf_le_inf_left _ hVC).trans_eq hc) (le_inf inf_le_right (inf_le_left.trans hUV))
  have hcomm : ⁅V,B⁆ = U ⊓ B := le_antisymm
    ((le_inf (le_normalizer_iff_commutator_le_right.mp hVB)
      (le_normalizer_iff_commutator_le_left.mp (hBN.trans hNV))).trans_eq hBV)
    (hp.symm.trans_le (commutator_mono hUV le_rfl))
  refine ⟨hcomm,le_antisymm ((inf_le_inf_left B (centralizer_le hUV)).trans_eq hc)
    (le_inf inf_le_right ((inf_le_left.trans hUV).trans
      (le_centralizer_iff_isMulCommutative.mpr inferInstance))),hBV,?_⟩
  rw [hcomm]
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_right.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))
omit [Finite G] in
private theorem conjugate_module_control (K T : Subgroup G)
    (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G)) {x : G}
    (hx : x ∈ normalizer (T : Set G)) :
    (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ T ∧
      T ≤ normalizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
  have he : T.map (MulAut.conj x⁻¹).toMonoidHom = T :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (T : Set G)).inv_mem hx)
  refine ⟨(map_mono hUT).trans_eq he,?_⟩
  rw [← map_equiv_normalizer_eq,← he]
  exact map_mono (hTK.trans (normalizer_le_normalizer_characteristic_image K (blockU K)))
/-- The full natural central-cover actor gives the exact source displacement,
fixed intersection, and quadratic action on V₁. -/
theorem natural_source_omega_displacement {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let B := (U K).map (MulAut.conj x⁻¹).toMonoidHom
    B ≤ N ∧ ⁅V,B⁆ = U K ⊓ B ∧ B ⊓ centralizer (V : Set G) = U K ⊓ B ∧
      B ⊓ V = U K ⊓ B ∧ ⁅⁅V,B⁆,B⁆ = ⊥ := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  let B := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  obtain ⟨he,_hVN,hNV,hUV,hVT,_⟩ := natural_source_omega_span h hn hT hTK P hP X hA hAX
  let : IsElementaryAbelian 2 V := he
  let : IsElementaryAbelian 2 (U K) := h.elementary
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hAN : K ⊔ T ≤ N := le_inf hAX ((K ⊔ T).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G))))
  have hb := conjugate_module_control K T (h.module_le.trans inf_le_left) hTK hx
  have hBN := hb.1.trans (le_sup_right.trans hAN)
  exact ⟨hBN,relative_pair_displacement (U K) B V N hUV hNV hBN (hVT.trans hb.2)
    (h.commutator_eq_fixed hx hnc).2 (h.conjugate_fixed_intersection hx hnc)⟩
/-- The original A₅ actor gives the same precise source displacement and
quadratic action, with its genuine C.5.6 pair identities discharged. -/
theorem alternating_five_source_omega_displacement {K T L : Subgroup G}
    (h : AlternatingPairSetup T K L) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let B := (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom
    B ≤ N ∧ ⁅V,B⁆ = sourceModule K ⊓ B ∧ B ⊓ centralizer (V : Set G) = sourceModule K ⊓ B ∧
      B ⊓ V = sourceModule K ⊓ B ∧ ⁅⁅V,B⁆,B⁆ = ⊥ := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  let B := (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom
  obtain ⟨he,_hVN,hNV,hUV,hVT,_⟩ := alternating_five_source_omega_span h hTK P hP X hA hAX
  let : IsElementaryAbelian 2 V := he
  let : IsElementaryAbelian 2 (sourceModule K) := h.block.2.1.elementary.map K.subtype
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hAN : K ⊔ T ≤ N := le_inf hAX ((K ⊔ T).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G))))
  have hb := conjugate_module_control K T (h.module_le.trans inf_le_left) hTK hx
  have hBN := hb.1.trans (le_sup_right.trans hAN)
  exact ⟨hBN,relative_pair_displacement (sourceModule K) B V N hUV hNV hBN (hVT.trans hb.2)
    (h.commutator_eq_fixed x hx hnc).2 (h.conjugate_fixed_eq_intersection x hx hnc)⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
