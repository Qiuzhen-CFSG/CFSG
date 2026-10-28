module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CentralDisplacement
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.BlockDisplacement
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.FullCentralizer

/-!
# The actual natural-cover application of Sylow averaging

The full image of Uˣ agrees with that of S. Thus each element of the original
Sylow S∩K has the same module action as a literal element of Uˣ; their
quotient belongs to C_R(U). The central-displacement theorem now gives
an actual K-fixed representative in every coset Uc for c∈C_R(UUˣ).

Source: Aschbacher–Smith, C.5.6(7), printed p.159.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G}
variable {E F : Type*} [Field E] [Field F]

theorem Setup.natural_common_centralizer_le
    (h : Setup R K E) (d : FullNaturalModel R K F)
    (hSylow : ∃ T : Sylow 2 K, (T : Subgroup K).map K.subtype = S R ⊓ K)
    {x : G} (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (hNK : R ⊓ centralizer (U K : Set G) ≤ normalizer (K : Set G)) :
    (R ⊓ centralizer (U K : Set G)) ⊓
        centralizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) ≤
      U K ⊔ (R ⊓ centralizer (K : Set G)) := by
  let N := normalizer (K : Set G)
  let P := R ⊓ centralizer (U K : Set G)
  let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  have hVS : V ≤ S R := h.conjugate_le hx
  have hVN : V ≤ N := hVS.trans d.normalizes
  have hQN : Q R K ≤ N := (h.core ▸ inf_le_left).trans d.normalizes
  have hQimage : ((Q R K).subgroupOf N).map d.action = ⊥ := by
    apply (map_eq_bot_iff ((Q R K).subgroupOf N)).mpr
    rw [d.action_kernel]
    exact subgroupOf_mono N (h.core ▸ inf_le_right)
  have hVi : (V.subgroupOf N).map d.action = ((S R).subgroupOf N).map d.action := by
    rw [(h.factorization hx hnc).span,subgroupOf_sup hVN hQN,Subgroup.map_sup,hQimage,sup_bot_eq]
  have hKU : K ≤ normalizer (U K : Set G) := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (blockU K))
  obtain ⟨T,hT⟩ := hSylow
  let := h.elementary
  rintro c ⟨hc,hcV⟩
  let ρ := d.action.comp (inclusion K.le_normalizer)
  have hρ (k : K) (u : U K) : ρ k (d.projection u) =
      d.projection ((U K).normalizerMonoidHom (inclusion hKU k) u) :=
    d.equivariant (inclusion K.le_normalizer k) u
  have hmatch (k : K) (hk : k ∈ T) : ∃ v : G, Commute v c ∧ (k : G)*v⁻¹ ∈ P := by
    have hkS : (k : G) ∈ S R := (hT ▸ mem_map_of_mem K.subtype hk).1
    have hm : d.action (inclusion K.le_normalizer k) ∈ (V.subgroupOf N).map d.action := by
      rw [hVi]
      exact mem_map_of_mem d.action hkS
    obtain ⟨v,hv,he⟩ := hm
    refine ⟨v,hcV v hv,?_⟩
    have hkρ : inclusion K.le_normalizer k * v⁻¹ ∈ d.action.ker := by
      change d.action _ = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    rw [d.action_kernel] at hkρ
    exact ⟨R.mul_mem ((show S R ≤ R from inf_le_left) hkS) (R.inv_mem (hVS.trans inf_le_left hv)),hkρ⟩
  obtain ⟨u,hu,huc⟩ := fixed_coset_mod_central_kernel_of_sylow K (U K) P hKU h.short.twoPerfect
    inf_le_right (block_fixer_displacement h.short hNK inf_le_right)
    d.projection d.surjective d.kernel ρ hρ T c hc hmatch
  have hh : u⁻¹*(u*c) ∈ U K ⊔ (R ⊓ centralizer (K : Set G)) := mul_mem_sup
    ((U K).inv_mem hu) ⟨R.mul_mem (h.module_le.trans inf_le_left hu) hc.1,huc⟩
  simpa only [inv_mul_cancel_left] using hh
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
