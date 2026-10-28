module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureInnerBlockCore
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Bounds
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.FixedIndex

/-!
# Three cubic chief layers in the original point residual

Every cubic in the original L1 fixes V1 inside U, so its movement on U
has at most two binary chief layers. The proved whole-core commutator
identity gives the same bound inside O2(K). The vector-stabilizer marking
bounds the remaining two-core quotient by a Sylow of S4, adding at most
one layer. This bounds every complete chief series of the literal L1.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation NoncentralChiefRefinement
open NoncentralChiefRefinement.CubicComparison
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The genuine original cubic point residual has at most three noncentral
binary chief factors; the original actor and every complete series are retained. -/
theorem original_tripleSix_central_closure_inner_chief_budget
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K)
    (s : ChiefSeries (tripleSixWeightFourResidual K z)) (h0 : s.head=⊥) (h1 : s.last=⊤) :
    s.noncentralTwoCount≤3 := by
  let L := tripleSixWeightFourResidual K z
  let C := K ⊓ centralizer ({(z:G)} : Set G)
  let V1 := tripleSixPoint D a z
  let Q := K.pCoreIn 2
  have hl := original_tripleSix_weightFour_cubic_residual D a z hz hzT
  have hLK : L≤K := hl.1.trans inf_le_left
  have hLC : L≤C := map_subtype_le _
  have hcardL : Nat.card (L ⧸ pCore 2 L)=3 := hl.2.2.2.1
  have hd : 3∣Nat.card L := by
    rw [←hcardL,←index_eq_card]
    exact (pCore 2 L).index_dvd_card
  obtain ⟨A,hA⟩ := Sylow.exists_subgroup_card_pow_prime (G:=L) 3 (n:=1) (by simpa using hd)
  have hA3 : Nat.card A=3 := by simpa using hA
  have hpA : IsPGroup 3 A := IsPGroup.of_card hA
  let AG := A.map L.subtype
  have hAGL : AG≤L := map_subtype_le _
  have hAGK : AG≤K := hAGL.trans hLK
  have hAU : AG≤normalizer (U : Set G) := hAGK.trans D.normalizes
  have hAQ : AG≤normalizer (Q : Set G) := hAGK.trans
    (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have hp := tripleSixPoint_properties D a z hz
  have hVfix : V1≤centralizer (AG : Set G) :=
    le_centralizer_iff.mp (hAGL.trans (hl.1.trans inf_le_right))
  have hVindex : V1.relIndex U=16 := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup G) V1 U bot_le hp.2.1
    rw [relIndex_bot_left,relIndex_bot_left,hp.2.2.1,
      Nat.card_congr (tripleSixPointCoordinates D a).toEquiv] at hm
    change 4*V1.relIndex U=Nat.card Atlas.Codes.hexacode at hm
    rw [Atlas.Codes.hexacode_card] at hm
    omega
  have hUlength : conjugationCubicLength AG U≤2 := by
    have hi := relIndex_le_of_le_left hVfix (V1.subgroupOf U).index_ne_zero_of_finite
    rw [hVindex] at hi
    exact (Nat.log_mono_right hi).trans (by decide : Nat.log 4 16≤2)
  have hUQ : U≤Q := D.le_componentCore
  let : (U.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 K).trans D.normalizes)
  have hQtwo : IsPGroup 2 Q := pCore_isPGroup.map K.subtype
  have hcore := (original_tripleSix_central_closure_inner_block_core
    h structural D a z hz hzT hnot hinner).1
  have hcomm : ⁅Q,AG⁆≤U := (commutator_mono
    (pCoreIn_mono_of_normalizes le_sup_left (sup_le K.le_normalizer D.sylow_normalizes_component))
      hAGK).trans_eq hcore
  have hQlength : conjugationCubicLength AG Q≤2 := by
    rw [←length_eq_of_commutator_le AG Q U (hpA.map L.subtype) hQtwo hUQ hAQ hAU hcomm]
    exact hUlength
  let π := (tripleSixPointCentralizerProjection D a z).comp (inclusion hLC)
  let N := π.ker
  have hN : N=(pCore 2 K).comap (inclusion hLK) := by
    rw [show N=π.ker from rfl,←MonoidHom.comap_ker,tripleSixPointCentralizerProjection_ker,comap_comap]
    rfl
  have hpN : IsPGroup 2 N := by
    rw [hN]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hNcore : N≤pCore 2 L := le_sSup ⟨inferInstance,hpN⟩
  have hNQ : N.map L.subtype≤Q := by
    rintro _ ⟨x,hx,rfl⟩
    rw [hN] at hx
    exact ⟨⟨x,hLK x.property⟩,hx,rfl⟩
  have hNlength : conjugationCubicLength A N≤2 := by
    rw [←length_map_injective L.subtype L.subtype_injective]
    exact (conjugationCubicLength_mono AG hNQ).trans hQlength
  let ψ := π.comp (pCore 2 L).subtype
  have hψker : ψ.ker=N.subgroupOf (pCore 2 L) := rfl
  have hψtwo : IsPGroup 2 ψ.range :=
    pCore_isPGroup.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  obtain ⟨S,hS⟩ := hψtwo.exists_le_sylow
  have hScard : Nat.card (S : Subgroup (Hexacode.fullWeightVectorStabilizer
      (tripleSixPointCoordinates D a z).toAdd))=8 := by
    rw [S.card_eq_multiplicity,Hexacode.weightFourVectorStabilizer_card _
      (tripleSix_sylow_fixed_weightFour D a z hz hzT)]
    decide +kernel
  have hquot : Nat.card (pCore 2 L ⧸ N.subgroupOf (pCore 2 L))≤8 := by
    rw [←hψker,Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact (Nat.card_le_card_of_injective (inclusion hS) (inclusion_injective _)).trans_eq hScard
  have hsection := (section_length_le_log_card A (pCore 2 L) N hpA pCore_isPGroup hNcore
    le_normalizer_of_normal le_normalizer_of_normal).trans (Nat.log_mono_right hquot)
  norm_num at hsection
  rw [count_of_core_quotient_card_three hcardL A hA3 s h0 h1]
  unfold sectionCubicLength at hsection
  omega

end CFSG.Quasithin.Chapter12.Section07
