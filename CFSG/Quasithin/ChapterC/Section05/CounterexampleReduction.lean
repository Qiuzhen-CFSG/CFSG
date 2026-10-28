module
public import Theory.GroupTheory.HalfSylowResidual
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.RelativeSylowNormalizer
public import Theory.GroupTheory.SubgroupConjugation
public import Stellmacher.OmegaOneCenterMap

/-!
# The source counterexample reductions in C.5.8

The original central-involution orbit rules out a common normal subgroup
for the reduced quadruple. Transfer constructs the actual residual section
T₁O²(N_G(T₁)); its index two excludes a larger Sylow subgroup in X when X
preserves the constructed V. The same residual section gives the final
contradiction once the genuine C.5.12 normalizer bound has been established.

These reductions preserve the actual ambient subgroups. The construction
of V and the C.5.12–13 block-enlargement argument remain earlier source
obligations; this file does not assert the complete common-normal theorem.
Source: Aschbacher–Smith, C.5.9–12, printed pp.160–163.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleReduction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem omega_center_le_core (T : Sylow 2 G) (A : Subgroup G)
    (hTA : (T : Subgroup G) ≤ A) (hA : A ∈ Chapter1.He G) :
    omegaOneCenterAmbient (T : Subgroup G) ≤ A.pCoreIn 2 := by
  have hcore : A.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow A (T.subtype hTA)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTA] at hh
  intro z hz
  have hh := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz
  exact hA ⟨hTA hh.1,fun c hc => hh.2.2 c (hcore hc)⟩

/-- The original central involution orbit rules out a common normal subgroup
for the actual reduced quadruple (N_G(T₁),T₁,T₁,K₁T₁). -/
theorem reduced_common_normal_eq_bot
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    (H K₁ K₂ T₁ U₁ : Subgroup G)
    (hT₁T : T₁ ≤ (T : Subgroup G)) (hindex : T₁.relIndex (T : Subgroup G) = 2)
    (hH : H = (K₁ ⊔ K₂) ⊔ (T : Subgroup G))
    (t : G) (ht : t ∈ (T : Subgroup G)) (hKt : K₁.conjBy t = K₂)
    (hU : U₁ ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)
    (hcoreU : H.pCoreIn 2 ≤ centralizer (U₁ : Set G))
    (x : G) (hx : x ∈ normalizer (T₁ : Set G))
    (hxH : U₁.map (MulAut.conj x⁻¹).toMonoidHom ≤ H)
    (hnc : ¬ U₁.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U₁ : Set G))
    (N : Subgroup G) (hNT : N ≤ T₁)
    (hYN : normalizer (T₁ : Set G) ≤ normalizer (N : Set G))
    (hKN : K₁ ⊔ T₁ ≤ normalizer (N : Set G)) : N = ⊥ := by
  let Y := normalizer (T₁ : Set G)
  let A := Y ⊔ (K₁ ⊔ T₁)
  have hTn : (T₁.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hindex
  have hTY : (T : Subgroup G) ≤ Y := (normal_subgroupOf_iff_le_normalizer hT₁T).mp hTn
  have hTA : (T : Subgroup G) ≤ A := hTY.trans le_sup_left
  have hK₁A : K₁ ≤ A := le_sup_left.trans le_sup_right
  have hK₂A : K₂ ≤ A := by
    rw [← hKt]
    exact (map_mono hK₁A).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (A.le_normalizer (hTA ht)))
  have hHA : H ≤ A := hH ▸ sup_le (sup_le hK₁A hK₂A) hTA
  have hAN : A ≤ normalizer (N : Set G) := sup_le hYN hKN
  have hNA : N ≤ A := hNT.trans (hT₁T.trans hTA)
  by_contra hN
  have hNcore : N ≤ A.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le (hNT.trans hT₁T)) hNA hAN
  have hcoreNe : A.pCoreIn 2 ≠ ⊥ := fun he => hN (bot_unique (he ▸ hNcore))
  have hAe : A ∈ Chapter1.He G := Chapter1.lemma_1_1_4_6 T hE ⟨hcoreNe,hTA⟩
  have hUcore : U₁ ≤ A.pCoreIn 2 := hU.trans (conjugateSpanBy_le
    (omega_center_le_core T A hTA hAe)
    (hHA.trans (A.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))))
  have hxcore : U₁.map (MulAut.conj x⁻¹).toMonoidHom ≤ A.pCoreIn 2 :=
    (map_mono hUcore).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_characteristic_image A (pCore 2 A)
        (A.le_normalizer (mem_sup_left (Y.inv_mem hx)))))
  have hi : A.pCoreIn 2 ⊓ H ≤ H.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 A).to_le inf_le_left) inf_le_right
    exact (le_inf (hHA.trans (A.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))) H.le_normalizer).trans
        inf_normalizer_le_normalizer_inf
  exact hnc ((le_inf hxcore hxH).trans (hi.trans hcoreU))

/-- An outside module mover excludes an enlarged Sylow subgroup in X.
Only the actual index-two residual section of Y is used; no dihedral
recognition of Y/T₁ is required. -/
private theorem reduced_sylow
    (T₁ X N U V : Subgroup G)
    (hNX : N ≤ X) (hNY : N ≤ normalizer (T₁ : Set G))
    (hindex : N.relIndex (normalizer (T₁ : Set G)) = 2)
    (hSylow : ∃ P : Sylow 2 N, (P : Subgroup N).map N.subtype = T₁)
    (hUX : X ≤ normalizer (V : Set G)) (hUV : U ≤ V)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G))
    (hmove : ¬ U.map (MulAut.conj x⁻¹).toMonoidHom ≤ V) :
    X ⊓ normalizer (T₁ : Set G) = N ∧
      ∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = T₁ := by
  have hxX : x ∉ X := by
    intro h
    exact hmove ((map_mono hUV).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (hUX (X.inv_mem h))))
  have hxN : x ∉ N := fun h => hxX (hNX h)
  have hXN : X ⊓ normalizer (T₁ : Set G) ≤ N := by
    rintro g ⟨hgX,hgY⟩
    by_contra hgN
    have hi : (N.subgroupOf (normalizer (T₁ : Set G))).index = 2 := hindex
    have hprod : g⁻¹ * x ∈ N := (mul_mem_iff_of_index_two hi
      (a := (⟨g⁻¹,(normalizer (T₁ : Set G)).inv_mem hgY⟩ : normalizer (T₁ : Set G)))
      (b := (⟨x,hx⟩ : normalizer (T₁ : Set G)))).mpr
        (iff_of_false (fun h => hgN (by simpa using N.inv_mem h)) hxN)
    exact hxX (by simpa only [mul_inv_cancel_left] using X.mul_mem hgX (hNX hprod))
  exact ⟨le_antisymm hXN (le_inf hNX hNY),exists_sylow_eq_of_relative_normalizer_le hSylow hNX hXN⟩
end CFSG.Quasithin.ChapterC.Section05.CounterexampleReduction



namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleReduction
variable {G : Type*} [Group G] [Finite G]

/-- The actual subgroup T₁O²(N_G(T₁)) has index two and has Sylow subgroup T₁. -/
theorem normalizer_residual_section (T : Sylow 2 G) (T₁ : Subgroup G)
    (hT₁T : T₁ ≤ (T : Subgroup G)) (hhalf : T₁.relIndex (T : Subgroup G) = 2) :
    let Y := normalizer (T₁ : Set G)
    let N := T₁ ⊔ (pResidual 2 Y).map Y.subtype
    N.relIndex Y = 2 ∧ ∃ P : Sylow 2 N, (P : Subgroup N).map N.subtype = T₁ := by
  dsimp only
  let Y := normalizer (T₁ : Set G)
  let Q := T₁.subgroupOf Y
  have hQ : Q.map Y.subtype = T₁ := map_subgroupOf_eq_of_le T₁.le_normalizer
  have hTn : (T₁.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hhalf
  have hTY : (T : Subgroup G) ≤ Y := (normal_subgroupOf_iff_le_normalizer hT₁T).mp hTn
  let S := T.subtype hTY
  let : Q.Normal := (normal_subgroupOf_iff_le_normalizer T₁.le_normalizer).mpr le_rfl
  have hQS : Q ≤ (S : Subgroup Y) := by
    change T₁.subgroupOf Y ≤ (T : Subgroup G).subgroupOf Y
    exact fun _ h => hT₁T h
  have hQSidx : Q.relIndex (S : Subgroup Y) = 2 := by
    have hi := relIndex_map_map_of_injective Q (S : Subgroup Y) Y.subtype_injective
    rw [hQ,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTY] at hi
    exact hi.symm.trans hhalf
  obtain ⟨hi,P,hP⟩ := normal_half_sylow_residual S Q hQS hQSidx
  let N₀ := Q ⊔ pResidual 2 Y
  have hNmap : N₀.map Y.subtype = T₁ ⊔ (pResidual 2 Y).map Y.subtype := by
    rw [Subgroup.map_sup,hQ]
  have hidx : (N₀.map Y.subtype).relIndex Y = 2 := by
    have hh := relIndex_map_map_of_injective N₀ ⊤ Y.subtype_injective
    simpa only [← MonoidHom.range_eq_map,Y.range_subtype,relIndex_top_right] using hh.trans (by simpa only [relIndex_top_right] using hi)
  let e := N₀.equivMapOfInjective Y.subtype Y.subtype_injective
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP' : (P' : Subgroup (N₀.map Y.subtype)).map (N₀.map Y.subtype).subtype = T₁ := by
    change ((P : Subgroup N₀).map e.toMonoidHom).map (N₀.map Y.subtype).subtype = T₁
    rw [Subgroup.map_map]
    change (P : Subgroup N₀).map (Y.subtype.comp N₀.subtype) = T₁
    rw [← Subgroup.map_map,hP,hQ]
  rw [← hNmap]
  exact ⟨hidx,P',hP'⟩

/-- The literal C.5.11 application with its residual section constructed from T₁. -/
theorem source_reduced_sylow (T : Sylow 2 G) (T₁ K₁ U₁ V : Subgroup G)
    (hT₁T : T₁ ≤ (T : Subgroup G)) (hhalf : T₁.relIndex (T : Subgroup G) = 2)
    (hUV : U₁ ≤ V)
    (hn : ((pResidual 2 (normalizer (T₁ : Set G))).map (normalizer (T₁ : Set G)).subtype ⊔
      (K₁ ⊔ T₁)) ≤ normalizer (V : Set G))
    (x : G) (hx : x ∈ normalizer (T₁ : Set G))
    (hmove : ¬ U₁.map (MulAut.conj x⁻¹).toMonoidHom ≤ V) :
    let X := (pResidual 2 (normalizer (T₁ : Set G))).map (normalizer (T₁ : Set G)).subtype ⊔
      (K₁ ⊔ T₁)
    X ⊓ normalizer (T₁ : Set G) = T₁ ⊔
      (pResidual 2 (normalizer (T₁ : Set G))).map (normalizer (T₁ : Set G)).subtype ∧
      ∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = T₁ := by
  obtain ⟨hi,hP⟩ := normalizer_residual_section T T₁ hT₁T hhalf
  exact reduced_sylow T₁ _ _ U₁ V
    (sup_le (le_sup_right.trans le_sup_right) le_sup_left)
    (sup_le T₁.le_normalizer (map_subtype_le _)) hi hP hn hUV x hx hmove
end CFSG.Quasithin.ChapterC.Section05.CounterexampleReduction

namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleReduction
variable {G : Type*} [Group G] [Finite G]

/-- C.5.12 suffices: the actual residual section normalizes both original modules,
and its join with T is the whole normalizer of T₁. -/
private theorem residual_control_contradiction (T : Sylow 2 G) (T₁ U₁ U₂ : Subgroup G)
    (hT₁T : T₁ ≤ (T : Subgroup G)) (hhalf : T₁.relIndex (T : Subgroup G) = 2)
    (hTU : (T : Subgroup G) ≤ normalizer ((U₁ ⊔ U₂ : Subgroup G) : Set G))
    (t : G) (ht : t ∈ (T : Subgroup G)) (hUt : U₁.conjBy t = U₂)
    (hcomm : U₁ ⊔ U₂ ≤ centralizer (U₁ : Set G))
    (hcontrol : T₁ ⊔ (pResidual 2 (normalizer (T₁ : Set G))).map
      (normalizer (T₁ : Set G)).subtype ≤ normalizer (U₁ : Set G))
    (x : G) (hx : x ∈ normalizer (T₁ : Set G))
    (hnc : ¬ U₁.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U₁ : Set G)) : False := by
  let Y := normalizer (T₁ : Set G)
  let N := T₁ ⊔ (pResidual 2 Y).map Y.subtype
  have hTn : (T₁.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hhalf
  have hTY : (T : Subgroup G) ≤ Y := (normal_subgroupOf_iff_le_normalizer hT₁T).mp hTn
  have hi : N.relIndex Y = 2 := (normalizer_residual_section T T₁ hT₁T hhalf).1
  have hYN : Y ≤ normalizer (N : Set G) :=
    (le_inf le_rfl (Y.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image Y (pResidual 2 Y)))).trans
      (T₁.normalizer_inf_normalizer_le_normalizer_sup _)
  have hNU₂ : N ≤ normalizer (U₂ : Set G) := by
    have hh := (map_mono hcontrol).trans (U₁.le_normalizer_map (MulAut.conj t).toMonoidHom)
    change N.map (MulAut.conj t).toMonoidHom ≤ normalizer (U₁.conjBy t : Set G) at hh
    have he : N.map (MulAut.conj t).toMonoidHom = N :=
      mem_normalizer_iff_map_conj_eq.mp (hYN (hTY ht))
    rw [he] at hh
    change N ≤ normalizer (U₁.conjBy t : Set G) at hh
    rwa [hUt] at hh
  have hNU : N ≤ normalizer ((U₁ ⊔ U₂ : Subgroup G) : Set G) :=
    (le_inf hcontrol hNU₂).trans (U₁.normalizer_inf_normalizer_le_normalizer_sup U₂)
  have hTnotN : ¬ (T : Subgroup G) ≤ N := by
    intro hTN
    have hd := relIndex_dvd_of_le_left Y hTN
    rw [hi] at hd
    exact (T.subtype hTY).not_dvd_index hd
  obtain ⟨a,haT,haN⟩ := Set.not_subset.mp hTnotN
  have hYNsup : Y ≤ N ⊔ (T : Subgroup G) := by
    intro y hy
    by_cases hyN : y ∈ N
    · exact mem_sup_left hyN
    have hm : y * a⁻¹ ∈ N := (mul_mem_iff_of_index_two hi
      (a := (⟨y,hy⟩ : Y)) (b := (⟨a⁻¹,Y.inv_mem (hTY haT)⟩ : Y))).mpr
      (iff_of_false hyN (fun h => haN (by simpa using N.inv_mem h)))
    have hh := (N ⊔ (T : Subgroup G)).mul_mem (mem_sup_left hm) (mem_sup_right haT)
    simpa only [inv_mul_cancel_right] using hh
  have hYU := hYNsup.trans (sup_le hNU hTU)
  exact hnc (((map_mono (show U₁ ≤ U₁ ⊔ U₂ from le_sup_left)).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (hYU (Y.inv_mem hx)))).trans hcomm)

/-- The literal C.5.8 contradiction after the genuine C.5.12 normalizer bound.
The preceding source inputs are the constructed V and the original two-block
orbit, and the residual section and Sylow conclusion are derived here. -/
theorem source_normalizer_control_contradiction (T : Sylow 2 G)
    (T₁ K₁ U₁ U₂ V : Subgroup G)
    (hT₁T : T₁ ≤ (T : Subgroup G)) (hhalf : T₁.relIndex (T : Subgroup G) = 2)
    (hTU : (T : Subgroup G) ≤ normalizer ((U₁ ⊔ U₂ : Subgroup G) : Set G))
    (t : G) (ht : t ∈ (T : Subgroup G)) (hUt : U₁.conjBy t = U₂)
    (hcomm : U₁ ⊔ U₂ ≤ centralizer (U₁ : Set G))
    (hUV : U₁ ≤ V)
    (hXV : ((pResidual 2 (normalizer (T₁ : Set G))).map (normalizer (T₁ : Set G)).subtype ⊔
      (K₁ ⊔ T₁)) ≤ normalizer (V : Set G))
    (hcontrol : ((pResidual 2 (normalizer (T₁ : Set G))).map
      (normalizer (T₁ : Set G)).subtype ⊔ (K₁ ⊔ T₁)) ⊓ normalizer (T₁ : Set G) ≤
        normalizer (U₁ : Set G))
    (x : G) (hx : x ∈ normalizer (T₁ : Set G))
    (hmove : ¬ U₁.map (MulAut.conj x⁻¹).toMonoidHom ≤ V)
    (hnc : ¬ U₁.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U₁ : Set G)) : False := by
  have hXN := (source_reduced_sylow T T₁ K₁ U₁ V hT₁T hhalf hUV hXV x hx hmove).1
  rw [hXN] at hcontrol
  exact residual_control_contradiction T T₁ U₁ U₂ hT₁T hhalf hTU t ht hUt hcomm hcontrol x hx hnc
end CFSG.Quasithin.ChapterC.Section05.CounterexampleReduction
