module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryArms
public import Theory.SpecificGroups.Triality.BinaryThreeFreeSylow
public import Theory.SpecificGroups.Triality.SylowParabolicExtensions
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryArms

/-!
# The binary-triality local Cartan row has even left degree

Assume the literal image of A ∩ Y in Y/O₂(Y) has order prime to three.
Its permuting product with the full Sylow image is then also prime to
three. Binary triality Sylow control for this solvable product preserves
the component Sylow. The marked arms parabolic is invariant under every
automorphism preserving that Sylow, so the original residual image is
fixed. The established two-core lift contradicts the original escape.

Consequently three divides the literal Cartan image. Since the original
left Cartan has order 2ⁿ − 1, n is even. This excludes all odd left degrees;
it does not identify n with the degree three of the residual PSL₂(8).
The complete seed reduction retains every preceding exclusion and marks
the same residual, Sylow, containing component and actual arms action.
The Chapter12 application uses the original chosen whole module.

The even-degree binary case, paired J₁, remaining normal containing rows,
and construction of the source inverted cubic remain with this local
classification. No inhabitant of SourceLocalCartanEscape is asserted.
Source: Aschbacher--Smith 5.1.12--13, printed pp.635--638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

private theorem three_free_permuting_join
    (A S : Subgroup G) (hS : IsPGroup 2 S) (hA : ¬ 3 ∣ Nat.card A)
    (hperm : (A : Set G) * S = (S : Set G) * A) :
    ¬ 3 ∣ Nat.card (A ⊔ S : Subgroup G) := by
  have he := card_set_mul_mul_card_inf A S
  rw [←coe_sup_of_set_mul_comm A S hperm] at he
  change Nat.card (A ⊔ S : Subgroup G) * Nat.card (A ⊓ S : Subgroup G) =
    Nat.card A * Nat.card S at he
  intro hd
  have hd' : 3 ∣ Nat.card A * Nat.card S := he ▸ dvd_mul_of_dvd_left hd _
  rcases Nat.prime_three.dvd_mul.mp hd' with hh | hh
  · exact hA hh
  · obtain ⟨k,hk⟩ := hS.exists_card_eq
    rw [hk] at hh
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hh)

/-- A binary-triality container in the original escaping configuration forces
a factor of three in the literal image of A ∩ Y in Y/O₂(Y). -/
theorem binaryTriality_escape_three_dvd_cartan_image
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
    3 ∣ Nat.card ((A.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) := by
  classical
  by_contra hthree
  obtain ⟨hKR,hCn,e,hS,hR,_,_⟩ := binaryTriality_residual_arms h.qtke hKH hH.1.1.2
    hK hKT horbit hY hescape C hC hKC hm
  let q := QuotientGroup.mk' (pCore 2 Y)
  let Cbar := C.map q
  let Rbar := ((residual H).subgroupOf Y).map q
  let Abar := (A.subgroupOf Y).map q
  have hTY := hH.1.1.2.trans hY.2
  let Q := (T.subtype hTY).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let J := Abar ⊔ (Q : Subgroup (Y ⧸ pCore 2 Y))
  let : Cbar.Normal := Subgroup.Normal.map hCn q (QuotientGroup.mk'_surjective _)
  have hRCY : (residual H).subgroupOf Y ≤ C := by
    intro x hx
    obtain ⟨z,hz,he⟩ := hKC (hKR.symm ▸ hx)
    exact (show z = x from Subtype.ext he) ▸ hz
  have hRC : Rbar ≤ Cbar := map_mono hRCY
  let : Group.IsSolvable J := h.cartan_sylow_action_isSolvable c hTY q
  have hJthree : ¬ 3 ∣ Nat.card J := three_free_permuting_join Abar Q Q.isPGroup' hthree
    (c.image_intersection_permutes_sylow h.sylow_normalizes hTY q)
  obtain ⟨U,hU⟩ := Q.exists_subgroupOf_eq_of_normal Cbar
  have hUJ : (U : Subgroup Cbar).map Cbar.subtype ≤ J := by
    rw [hU,subgroupOf_map_subtype]
    exact inf_le_left.trans le_sup_right
  have hn := Triality.Standard.BinaryThreeFreeSylow.normalizes_layer_sylow Cbar J e U
    (by rw [normalizer_eq_top]; exact le_top) hUJ hJthree
  apply hescape
  apply (residual_escape_twoCore_iff h.qtke h.sylow_normalizes hH hgen hY.2).mp
  intro d hd
  let a : MulAut Cbar := MulAut.conjNormal d
  have haU : (U : Subgroup Cbar).map a.toMonoidHom = U := by
    apply map_injective Cbar.subtype_injective
    have he : ((U : Subgroup Cbar).map a.toMonoidHom).map Cbar.subtype =
        ((U : Subgroup Cbar).map Cbar.subtype).map (MulAut.conj d).toMonoidHom := by
      rw [map_map,map_map]
      rfl
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp (hn (mem_sup_left hd))
  have hmark : (U : Subgroup Cbar).map e.toMonoidHom =
      Triality.Standard.Parabolics.unipotent (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) := by
    rw [hU]
    change ((((T : Subgroup G).subgroupOf Y).map q).subgroupOf Cbar).map e.toMonoidHom = _
    exact hS
  have htransport : ((U : Subgroup Cbar).map a.toMonoidHom).map e.toMonoidHom =
      ((U : Subgroup Cbar).map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    ext x
    simp [MulAut.congr_apply]
  have hfixed : (Triality.Standard.Parabolics.unipotent
      (Triality.Standard.binaryParameters 1 Nat.zero_lt_one)).map
      (MulAut.congr e a).toMonoidHom =
        Triality.Standard.Parabolics.unipotent (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) := by
    rw [←hmark,←htransport,haU]
  apply normalizes_of_marked_fixed Cbar Rbar hRC e d
  rw [hR]
  exact Triality.Standard.Parabolics.parabolic_map_eq_of_unipotent_invariant
    (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) rfl .arms (MulAut.congr e a) hfixed

private theorem three_not_dvd_torus_of_odd {n : ℕ} (hn : Odd n) : ¬ 3 ∣ 2 ^ n - 1 := by
  have hpow : 2 ^ n % 3 = 2 := by
    obtain ⟨k,rfl⟩ := hn
    rw [pow_add,pow_mul]
    norm_num [Nat.mul_mod,Nat.pow_mod]
  intro hd
  have hh := Nat.mod_eq_zero_of_dvd hd
  have hp := Nat.one_le_two_pow (n := n)
  omega

/-- The binary-triality row forces the ORIGINAL left field degree to be even.
The degree of the residual PSL₂(8) quotient is not substituted for it. -/
theorem binaryTriality_escape_even_degree
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
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) : Even n := by
  have hd := binaryTriality_escape_three_dvd_cartan_image h hH hgen c hKH hK hKT horbit
    hY hescape C hC hKC hm
  have hd' : 3 ∣ Nat.card (A.subgroupOf Y) := hd.trans (card_map_dvd _ _)
  have hdA : 3 ∣ Nat.card A := by
    rw [←inf_subgroupOf_right A Y,Nat.card_congr
      (subgroupOfEquivOfLe (show A ⊓ Y ≤ Y from inf_le_right)).toEquiv] at hd'
    exact hd'.trans (card_dvd_of_le (show A ⊓ Y ≤ A from inf_le_left))
  rw [(c.left_cyclic_and_card h.sylow_normalizes h.linear).2] at hdA
  exact Nat.not_odd_iff_even.mp (fun hn => three_not_dvd_torus_of_odd hn hdA)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- All preceding exclusions are retained, and the binary-triality branch
now forces a cubic divisor in the actual Cartan image and even left degree. -/
theorem localCartan_escape_seed_binaryParity_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          Even n ∧
          3 ∣ Nat.card ((A.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) ∧
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
          BinaryArmsPlacement T H Y C ∧ BinaryArmsAction T H A B Y C) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        (C.Normal ∨ ((normalizer (C : Set Y)).index = 2 ∧
          K < residual H ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
          IsElementaryAbelian 3 B ∧ Nat.card B = 9 ∧
          Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model))) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hpair⟩ :=
    localCartan_escape_seed_binaryArms_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,?_,hprime,h25,hpair⟩
  intro hm
  have hh := hrank hm
  exact ⟨LocalSieve.binaryTriality_escape_even_degree h hH hgen c hKH hKL hKT hR
      hY hescape C hC hKC hh.2.2.1,
    LocalSieve.binaryTriality_escape_three_dvd_cartan_image h hH hgen c hKH hKL hKT hR
      hY hescape C hC hKC hh.2.2.1,hh⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
