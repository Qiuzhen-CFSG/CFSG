module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryBorelQuotient
public import Theory.SpecificGroups.Triality.BinaryCentralFixedSubgroup
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryQuadratic
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryCore

/-!
# The original binary omega-span lies in the retained two-core

In the literal X = CT quotient, the full original Sylow normalizes the
omega-span image and the original Cartan fixes it. The actual residual
image is the perfect arms parabolic. Cartan escape makes its solvable
Sylow join a central parabolic section. The central-parabolic fixed
subgroup calculation therefore kills the omega-span image, proving
U ≤ O₂(X) without discarding that core or changing the original module W.

Consequently the retained kernel E is all of U, the original perfect
seven-centralizer normalizes E, and U acts trivially on the SAME N/Φ(N).
The independent component action and large span remain: this result
does not assert SourceLocalCartanEscape or the binary-triality exclusion.
The internal import shares the quotient-order calculations of this proof
family while preserving their public boundary.

Source: Aschbacher--Smith 5.1.10--13, printed pp.634--638, and the binary
seven-centralizer calculation in 5.2.2, printed pp.648--649, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]

/-- The original omega-span has trivial image in the literal CT two-core
quotient. Neither the original chosen module nor the quotient map is changed. -/
theorem original_binary_triality_omega_le_core
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L ≤
      (C.map Y.subtype ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let q := QuotientGroup.mk' (pCore 2 X)
  let R := (residual H).subgroupOf X
  let Rbar := R.map q
  let Abar := (A.subgroupOf X).map q
  let Ubar := (U.subgroupOf X).map q
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  obtain ⟨hXY,hXH,hAX,hesc,hx,_,_,_,_⟩ := original_binary_triality_core_bound
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨hKR,_,hr⟩ := LocalSieve.binaryTriality_residual_section h.qtke hKH
    hH.1.1.2 hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨hu,_,_,_,_⟩ := original_binary_triality_fixed_omega_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hRX : residual H ≤ X := (hKR ▸ hKC).trans le_sup_left
  have hUX : U ≤ X := hu.reduced_le_sylow.trans le_sup_right
  let ar := ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (subgroupOfEquivOfLe hRX).symm
  let arq := QuotientGroup.congr _ _ ar (pCore_map_iso 2 ar)
  have hrR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 := hr.of_mulEquiv arq.symm
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK
  let : Group.IsPerfect (residual H) := hKR ▸ (inferInstance : Group.IsPerfect K)
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRX).symm.toMonoidHom) (subgroupOfEquivOfLe hRX).symm.surjective
  let : Group.IsPerfect Rbar := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective R)
  let r := q.subgroupMap R
  have hk : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let b := r.pCoreQuotientEquiv (q.subgroupMap_surjective R) hk
  have hrc : Nat.card (Rbar ⧸ pCore 2 Rbar) = 504 :=
    (Nat.card_congr b.symm.toEquiv).trans (psl_eight_card hrR)
  have hproper : Rbar ≠ ⊤ := by
    intro he
    let a : Rbar ≃* (X ⧸ pCore 2 X) :=
      (MulEquiv.subgroupCongr he).trans (topEquiv (G := X ⧸ pCore 2 X))
    let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    have hcard := Nat.card_congr aq.toEquiv
    rw [pCore_quotient_pCore_eq_bot 2,
      Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
      Nat.card_congr hx.some.toEquiv,binary_card,hrc] at hcard
    omega
  have hns : ¬ Group.IsSolvable Rbar := by
    have hnq : Nontrivial (Rbar ⧸ pCore 2 Rbar) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hrc]; decide)
    let : Nontrivial Rbar := Function.Surjective.nontrivial
      (QuotientGroup.mk'_surjective (pCore 2 Rbar))
    exact Group.IsPerfect.not_isSolvable Rbar
  have hRN : (S : Subgroup X) ≤ normalizer (R : Set X) := by
    rw [←subgroupOf_normalizer_eq hRX]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_residual H))
  have hPN : (P : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (Rbar : Set _) :=
    (map_mono hRN).trans (le_normalizer_map q)
  have hAR : ¬ Abar ≤ normalizer (Rbar : Set _) := by
    intro hh
    exact hesc ((LocalSieve.residual_escape_twoCore_iff
      h.qtke h.sylow_normalizes hH hgen hXH.2).mp hh)
  have hUN : (S : Subgroup X) ≤ normalizer (U.subgroupOf X : Set X) := by
    rw [←subgroupOf_normalizer_eq hUX]
    exact comap_mono (le_sup_right.trans (reduced_normalizes hu.reduced))
  let : Group.IsSolvable (Abar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) : Subgroup _) :=
    h.cartan_sylow_action_isSolvable c (show (T : Subgroup G) ≤ X from le_sup_right) q
  have hzero := Triality.Standard.BinaryCentralFixedSubgroup.marked_fixed_subgroup_eq_bot
    hx.some P Rbar Abar Ubar hproper hns hPN hAR
    (map_mono (show U.subgroupOf X ≤ (S : Subgroup X) from comap_mono hu.reduced_le_sylow))
    ((map_mono hUN).trans (le_normalizer_map q))
    (original_binary_triality_omega_image_cartan_fixed
      h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm)
  intro u hu
  have hz : q (⟨u,hUX hu⟩ : X) = 1 :=
    mem_bot.mp (hzero ▸ mem_map_of_mem q (show (⟨u,hUX hu⟩ : X) ∈ U.subgroupOf X from hu))
  exact mem_map_of_mem X.subtype ((QuotientGroup.eq_one_iff _).mp hz)


/-- Core containment identifies the retained kernel with the original whole
omega-span, and the original perfect seven-centralizer normalizes that kernel. -/
theorem original_binary_triality_kernel_eq_omega
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let E := U ⊓ X.pCoreIn 2
    E = U ∧ residual (L ⊓ centralizer (B : Set G)) ≤ normalizer (E : Set G) := by
  have hc := original_binary_triality_omega_le_core
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  exact ⟨inf_eq_left.mpr hc,
    (original_binary_triality_kernel_span
      h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm).2.2.mpr hc⟩

/-- The original omega-span's conjugation action on the retained span's
Frattini quotient is trivial. The independent component action is retained. -/
theorem original_binary_triality_omega_frattini_action_trivial
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let E := U ⊓ X.pCoreIn 2
    let N := conjugateSpanBy E X
    ∀ a : U →* MulAut N,
      (∀ (u : U) (v : N), ((a u v : N) : G) =
        (u : G) * (v : G) * (u : G)⁻¹) →
      (quotientAut (frattini N)).comp a = 1 := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  let N := conjugateSpanBy E X
  change ∀ a : U →* MulAut N,
    (∀ (u : U) (v : N), ((a u v : N) : G) =
      (u : G) * (v : G) * (u : G)⁻¹) →
    (quotientAut (frattini N)).comp a = 1
  intro a ha
  have hEU : E = U := (original_binary_triality_kernel_eq_omega
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm).1
  have hUN : U ≤ N := hEU.symm.le.trans (le_conjugateSpanBy E X)
  have hNQ := (original_binary_triality_kernel_large_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm).2.2.1
  have hk := Subgroup.FrattiniSeed.frattini_conjugation_kernel N U
    ((isPGroup_pCoreIn 2 X).to_le hNQ) a ha
  apply MonoidHom.ext
  intro u
  exact hk (show u ∈ N.subgroupOf U from hUN u.property)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
