module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorLocal

/-!
# Generation from the original local tensor module

The local module equals its seed and is normal in the prescribed Sylow group.
The tensor-normalizer rank gap and B.2.4 make J_j(T) centralize this module
whenever j+1<n. Its original TI property, local-core centralizer and maximal
local uniqueness establish E.6.1. The actual ambient seed automizer inherits
the tensor displacement bound, so E.6.3 gives r(G,V°) >= n. E.6.26 then gives
n(H) >= n-1 for the unchanged H-star subgroup.

This uses E.6.1 in its TI form and does not require seed = V_M. The final
Hall alternative retains the actual quotient and both component markings.
The Cartan placement and field/fixed-space comparison of 9.2.5--7 remain
necessary to exclude the tensor and finish the Hall exponent theorem.
Source: Aschbacher--Smith 9.2.1--4, printed p.730, using H.1.1(2), B.2.4,
E.6.3 and E.6.26; 10.2.3, p.745, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary

private def seedSylowHom (hs : (T : Subgroup G) ≤ normalizer (D.seed : Set G)) :
    T →* linearNormalizer (originalSeedAction D) :=
  (originalSeedAmbientNormalizerHom D).comp ((T : Subgroup G).subtype.codRestrict
    (D.maximalLocal ⊓ normalizer (D.seed : Set G))
    (fun a => ⟨le_normalizer_componentOrbit L T a.property,hs a.property⟩))

private theorem seedSylowHom_ker
    (hs : (T : Subgroup G) ≤ normalizer (D.seed : Set G))
    (hST : D.seed ≤ (T : Subgroup G)) :
    (seedSylowHom D hs).ker = centralizer (D.seed.subgroupOf T : Set T) := by
  ext a
  constructor
  · intro ha v hv
    have hh := congrArg (fun x : linearNormalizer (originalSeedAction D) =>
      x.val.val (Additive.ofMul (⟨v,hv⟩ : D.seed))) ha
    have he := congrArg (fun w : Additive D.seed => (w.toMul : G)) hh
    change (a:G)*(v:G)*(a:G)⁻¹ = (v:G) at he
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro ha
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    have he := congrArg Subtype.val (ha ⟨v.toMul,hST v.toMul.property⟩ v.toMul.property)
    change (v.toMul:G)*(a:G) = (a:G)*(v.toMul:G) at he
    change (a:G)*(v.toMul:G)*(a:G)⁻¹ = (v.toMul:G)
    rw [←he,mul_inv_cancel_right]

private theorem seedSylowHom_thompson_bound
    (hs : (T : Subgroup G) ≤ normalizer (D.seed : Set G))
    (hST : D.seed ≤ (T : Subgroup G))
    (j : ℕ) (A : Subgroup T) (hA : A ∈ ChapterB.thompsonFamily ⊤ j)
    (hne : A.map (seedSylowHom D hs) ≠ ⊥) :
    fixedCodim (normalizerRepresentation (originalSeedAction D))
        (A.map (seedSylowHom D hs)) ≤ rank (A.map (seedSylowHom D hs)) + j := by
  let U := D.seed.subgroupOf (T : Subgroup G)
  let : U.Normal := normal_subgroupOf_of_le_normalizer hs
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hST
  let : IsElementaryAbelian 2 A := hA.2.1
  let e := subgroupOfEquivOfLe hST
  let E : Additive U ≃ₗ[ZMod 2] Additive D.seed :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  let ρ := NoncentralChiefRefinement.normalRepresentation U
  have hE (a : T) (v : Additive U) : E (ρ a v) =
      normalizerRepresentation (originalSeedAction D) (seedSylowHom D hs a) (E v) := rfl
  have hb := ChapterB.lemma_B_2_4_1 (⊤ : Subgroup T) U A le_top le_top j
    (by rw [hA.2.2.2,Nat.log_pow (by decide : 1 < 2)]; rfl)
    (seedSylowHom D hs) (seedSylowHom_ker D hs hST) hne
  rw [←NoncentralChiefRefinement.normalRepresentation_fixedCodim_eq_rank_difference U A] at hb
  have he := fixedCodim_map_equivariant ρ (normalizerRepresentation (originalSeedAction D))
    (seedSylowHom D hs) E hE A
  change fixedCodim ρ A - j ≤ rank (A.map (seedSylowHom D hs)) at hb
  rw [he] at hb
  omega

/-- The higher Thompson subgroup centralizes the literal local tensor module.
No assertion about the full M-orbit is required. -/
theorem original_even_local_thompson_centralizes
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (j : ℕ) (hj : j+1 < n) :
    ChapterB.thompsonJ (T : Subgroup G) j ≤ centralizer (D.moduleSubgroup : Set G) := by
  have heq := original_even_module_eq_seed D c n hn e ht htn hsep
  have hs : (T : Subgroup G) ≤ normalizer (D.seed : Set G) := heq ▸ D.sylow_normalizes_module
  have hST : D.seed ≤ (T : Subgroup G) := heq ▸ D.module_le_sylow
  rw [heq]
  have htop : (⊤ : Subgroup T).map (T : Subgroup G).subtype = (T : Subgroup G) := by
    rw [←MonoidHom.range_eq_map,Subgroup.range_subtype]
  rw [←htop,ChapterB.thompsonJ_map_injective _ (T : Subgroup G).subtype_injective]
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro A hA
  let : IsElementaryAbelian 2 A := hA.2.1
  have hz : A.map (seedSylowHom D hs) = ⊥ := by
    by_contra hne
    let : IsElementaryAbelian 2 (A.map (seedSylowHom D hs)) := IsElementaryAbelian.map _
    have hl := (original_even_seed_normalizer_bounds D c n hn e ht htn hsep
      (A.map (seedSylowHom D hs)) ⟨hne,inferInstance⟩).2.1
    have hu := seedSylowHom_thompson_bound D hs hST j A hA hne
    omega
  intro a ha v hv
  have hak : a ∈ (seedSylowHom D hs).ker := (Subgroup.map_eq_bot_iff A).mp hz ha
  rw [seedSylowHom_ker D hs hST] at hak
  exact congrArg Subtype.val (hak ⟨v,hST hv⟩ hv)

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules

namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 ChapterE
open Representation.BinaryOffender.NaturalTensor
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary

variable {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))

include c hn e ht htn hsep

/-- E.6.1 on the original seed as a TI subgroup normal in T. -/
theorem original_even_seed_hypothesisE61 :
    ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T D.maximalLocal D.seed := by
  have hu := D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)
  have heq := original_even_module_eq_seed D c n hn e ht htn hsep
  have hs : (T : Subgroup G) ≤ normalizer (D.seed : Set G) := heq ▸ D.sylow_normalizes_module
  have hST : D.seed ≤ (T : Subgroup G) := heq ▸ D.module_le_sylow
  have hJ : localJoin T L ≤ normalizer (D.seed : Set G) := heq ▸ D.join_normalizes_module
  have hc : D.seed ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
    apply bot_unique
    intro v hv
    have hvF : v ∈ D.fullModule :=
      ((le_componentOrbit D.seed T).trans (le_componentOrbit _ _)) hv.1
    have hmem : (⟨v,hvF⟩ : D.fullModule) ∈ D.fullCentralizer := hv.2
    rw [fullCentralizer_eq_bot_of_central_hstar D c] at hmem
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hmem))
  refine ⟨D.simpleQTKE,hu.1,le_sup_right.trans hu.2.1,D.seed_ne_bot,inferInstance,hST,
    normal_subgroupOf_of_le_normalizer hs,?_,?_⟩
  · intro g hg
    exact D.seed_ti_under_maximalLocal (source_module_nonsolvable_uniqueness D) hc ⟨g,hg⟩
  · intro N hN hle
    apply hu.2.2 N hN
    apply le_trans _ hle
    refine le_inf (le_inf hu.2.1 hJ) ?_
    change localJoin T L ≤ normalizer (((T : Subgroup G) ⊓ centralizer (D.seed : Set G) : Subgroup G) : Set G)
    rw [←heq,D.sylow_centralizer_module (source_module_nonsolvable_uniqueness D)]
    exact (localJoin T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (localJoin T L) (pCore 2 (localJoin T L)))

/-- The actual ambient seed automizer has minimum involution displacement at least n. -/
theorem original_even_seed_localM_ge : n ≤ ChapterE.localM D.seed := by
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  have hnormal := (original_even_seed_hypothesisE61 D c n hn e ht htn hsep).normalizer_le
  apply le_csInf ⟨_,Set.mem_insert _ _⟩
  rintro k (rfl | ⟨a,ha,rfl⟩)
  · have hd := original_nonseparated_even_seed_finrank_eq D c n hn e ht htn hsep
    omega
  · obtain ⟨m,hm⟩ := D.seed.normalizerMonoidHom.rangeRestrict_surjective a
    have he : originalSeedNormalizerAction D m = automizerRepresentation D.seed a := by
      rw [←hm]
      rfl
    have hmove : originalSeedNormalizerAction D m ≠ 1 := by
      rw [he]
      intro hz
      have hane : a ≠ 1 := by intro he; simp [he] at ha
      apply hane
      apply automizerRepresentation_injective D.seed
      simpa only [map_one] using hz
    have hd := original_even_seed_ambient_displacement_ge D c n hn e ht htn hsep
      m (hnormal m.property) m.property hmove
    rw [he] at hd
    exact hd.trans (operatorFixedCodim_le_fixedCodim (automizerRepresentation D.seed)
      (zpowers a) (mem_zpowers a))

/-- E.6.3 supplies the ambient corank bound for the local tensor seed. -/
theorem original_even_seed_globalR_ge :
    (n : ℕ∞) ≤ ChapterE.globalR D.seed := by
  have hm := original_even_seed_localM_ge D c n hn e ht htn hsep
  have hh := ChapterE.Section06.FrobeniusReduction.lower_bound_knownSimple
    (original_even_seed_hypothesisE61 D c n hn e ht htn hsep) (by omega)
  exact (ENat.natCast_le_natCast.mpr hm).trans hh.1

/-- Source 9.2.4(1), specialized to the original central Hall tensor branch.
E.6.26 is applied to the TI local module, with all its premises discharged. -/
theorem original_even_generation_ge : n-1 ≤ generationParameter H := by
  by_contra! hgen
  have hjpos : 0 < n-2 := by omega
  have hTH : (T : Subgroup G) ≤ H := c.hstar.1.1.2
  have hs : ((T.subtype hTH : Sylow 2 H) : Subgroup H).map H.subtype = T :=
    map_subgroupOf_eq_of_le hTH
  have hr : ((n-2 : ℕ) : ℕ∞) < globalR D.seed :=
    (ENat.natCast_lt_natCast.mpr (by omega : n-2 < n)).trans_le
      (original_even_seed_globalR_ge D c n hn e ht htn hsep)
  have hJ := original_even_local_thompson_centralizes D c n hn e ht htn hsep (n-2) (by omega)
  rw [original_even_module_eq_seed D c n hn e ht htn hsep] at hJ
  have hh := ChapterE.Section06.FixedPointBounds.SylowThompson.source_E_6_26_knownSimple
    (original_even_seed_hypothesisE61 D c n hn e ht htn hsep) hjpos H (T.subtype hTH)
    (Chapter3.sqtk_of_mem_H D.simpleQTKE c.hstar.1.1.1) (by omega : generationParameter H ≤ n-2)
    (by rw [hs]; exact inf_le_left) (by rw [hs]) hr (by rwa [hs])
  exact c.hstar.1.2 hh.1

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules

namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 ChapterE
open scoped MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary

/-- The literal Hall alternative now carries local tensor equality and the
source generation lower bound. Its original quotient and both factor markings
remain in the tensor and determinant coordinates. -/
theorem original_hall_conclusion_or_natural_tensor_generation
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
        ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
          ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
            D.seed ≤ centralizer (L : Set G)) ∧
          OriginalEvenNaturalTensorAnalysis D ht n e ∧
          OriginalEvenSeedDeterminantCoordinates D ht n e ∧
          D.moduleSubgroup = D.seed ∧
          ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T D.maximalLocal D.seed ∧
          n ≤ ChapterE.localM D.seed ∧ (n : ℕ∞) ≤ ChapterE.globalR D.seed ∧
          (∀ j : ℕ, j+1 < n →
            ChapterB.thompsonJ (T : Subgroup G) j ≤ centralizer (D.moduleSubgroup : Set G)) ∧
          n-1 ≤ generationParameter H := by
  rcases original_hall_conclusion_or_natural_tensor_displacement D c with hh |
    ⟨t,ht,htn,n,hn,e,hsep,ha,hdet,_hm,_hdisp⟩
  · exact Or.inl hh
  · exact Or.inr ⟨t,ht,htn,n,hn,e,hsep,ha,hdet,
      original_even_module_eq_seed D c n hn e ht htn hsep,
      original_even_seed_hypothesisE61 D c n hn e ht htn hsep,
      original_even_seed_localM_ge D c n hn e ht htn hsep,
      original_even_seed_globalR_ge D c n hn e ht htn hsep,
      original_even_local_thompson_centralizes D c n hn e ht htn hsep,
      original_even_generation_ge D c n hn e ht htn hsep⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
