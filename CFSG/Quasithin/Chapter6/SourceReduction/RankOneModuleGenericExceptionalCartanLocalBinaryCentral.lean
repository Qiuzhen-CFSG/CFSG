module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryParity
public import Theory.SpecificGroups.Triality.BinarySolvableCubic
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryArms

/-!
# The central parabolic and the actual cubic in binary local Cartan escape

The original Cartan--Sylow join is solvable. If its intersection with the
containing binary-triality image normalized the full Sylow intersection,
that Sylow would be the characteristic two-core of the intersection. The
whole join would then preserve the marked arms parabolic, contradicting
the original residual escape. The literal intersection is consequently the
central local factor or the full central parabolic, under the same marking
that identifies the original residual as the arms parabolic.

Hall restriction constructs a cubic in the original odd actor inside this
same component image. The two parabolics meet in a Borel of order prime to
three, so this cubic moves the arms parabolic. The odd Cartan injects through
the original two-core quotient. Lifting its cubic therefore preserves order
three; relative normality and the two-group kernel put the lift inside the
original containing component. It moves the original whole residual.

The final universal reduction retains the original module and all preceding
exclusions. Binary triality itself, paired J₁, the remaining normal containing
rows and the final local source witness remain open. The internal import
reuses the marked-normalizer transport in the same local Cartan proof family.
Source: Aschbacher--Smith 5.1.12--13, printed pp.635--638 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The actual solvable Cartan--Sylow join meets the same containing
component in the central local factor or the full central parabolic. -/
@[expose] def BinaryCentralPlacement (T : Sylow 2 G) (H A Y : Subgroup G)
    (C : Subgroup Y) : Prop :=
  let q := QuotientGroup.mk' (pCore 2 Y)
  let Cbar := C.map q
  let R := (((residual H).subgroupOf Y).map q).subgroupOf Cbar
  let S := (((T : Subgroup G).subgroupOf Y).map q).subgroupOf Cbar
  let J := (A.subgroupOf Y).map q ⊔ ((T : Subgroup G).subgroupOf Y).map q
  ∃ e : Cbar ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one,
    S.map e.toMonoidHom = Triality.Standard.Parabolics.unipotent
      (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) ∧
    R.map e.toMonoidHom = Triality.Standard.Parabolics.parabolic
      (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) .arms ∧
    ((J.subgroupOf Cbar).map e.toMonoidHom = Triality.Standard.Parabolics.localFactor
      (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) .central ∨
    (J.subgroupOf Cbar).map e.toMonoidHom = Triality.Standard.Parabolics.parabolic
      (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) .central)

namespace LocalSieve
/-- The same marking identifies the actual escaping residual as the arms
parabolic and the solvable actor intersection as a central parabolic section. -/
theorem binaryTriality_escape_central_placement
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
    BinaryCentralPlacement T H A Y C := by
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
  obtain ⟨U,hU⟩ := Q.exists_subgroupOf_eq_of_normal Cbar
  have hUJ : (U : Subgroup Cbar).map Cbar.subtype ≤ J := by
    rw [hU,subgroupOf_map_subtype]
    exact inf_le_left.trans le_sup_right
  have hnot : ¬ J ≤ normalizer ((U : Subgroup Cbar).map Cbar.subtype : Set _) := by
    intro hn
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
  have hmark : (U : Subgroup Cbar).map e.toMonoidHom =
      Triality.Standard.Parabolics.unipotent (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) := by
    rw [hU]
    exact hS
  have hcases := Triality.Standard.BinarySolvableEscape.layer_cases Cbar J U e hmark
    (by rw [normalizer_eq_top]; exact le_top) hUJ hnot
  exact ⟨e,hS,hR,hcases⟩

private theorem odd_lift_le_normal {Q : Type*} [Group Q]
    (q : G →* Q) (hq : IsPGroup 2 q.ker) (C D : Subgroup G) [C.Normal]
    (ho : Odd (Nat.card D)) (hle : D.map q ≤ C.map q) : D ≤ C := by
  let r := QuotientGroup.mk' C
  have him : D.map r ≤ q.ker.map r := by
    rintro _ ⟨d,hd,rfl⟩
    obtain ⟨c,hc,he⟩ := hle (mem_map_of_mem q hd)
    have hk : c⁻¹ * d ∈ q.ker := by
      change q (c⁻¹ * d) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    refine ⟨c⁻¹ * d,hk,?_⟩
    rw [map_mul,map_inv,show r c = 1 from (QuotientGroup.eq_one_iff c).mpr hc]
    simp
  have hd : Disjoint (D.map r) (q.ker.map r) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨k,hk⟩ := (hq.map r).exists_card_eq
    rw [hk]
    exact (ho.of_dvd_nat (card_map_dvd D r)).coprime_two_right.pow_right k
  intro d hdD
  exact (QuotientGroup.eq_one_iff d).mp
    (disjoint_def.mp hd (mem_map_of_mem r hdD) (him (mem_map_of_mem r hdD)))

/-- The original binary escape supplies a cubic inside the original left
Cartan and the actual containing component; it moves the original residual. -/
theorem binaryTriality_escape_cubic
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
    ∃ D : Subgroup G, D ≤ A ∧ D ≤ C.map Y.subtype ∧ Nat.card D = 3 ∧
      ¬ D ≤ normalizer (residual H : Set G) := by
  obtain ⟨hKR,hCn⟩ := binaryTriality_seed_eq_residual_and_normal h.qtke hKH hH.1.1.2
    hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨e,_,hR,hcases⟩ := binaryTriality_escape_central_placement h hH hgen c
    hKH hK hKT horbit hY hescape C hC hKC hm
  let q := QuotientGroup.mk' (pCore 2 Y)
  let Cbar := C.map q
  let Rbar := ((residual H).subgroupOf Y).map q
  let AY := A.subgroupOf Y
  let Abar := AY.map q
  have hTY := hH.1.1.2.trans hY.2
  let Q := (T.subtype hTY).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let : Cbar.Normal := Subgroup.Normal.map hCn q (QuotientGroup.mk'_surjective _)
  have hRCY : (residual H).subgroupOf Y ≤ C := by
    intro x hx
    obtain ⟨z,hz,he⟩ := hKC (hKR.symm ▸ hx)
    exact (show z = x from Subtype.ext he) ▸ hz
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have hoAY : Odd (Nat.card AY) := by
    change Odd (Nat.card (A.subgroupOf Y))
    rw [←inf_subgroupOf_right A Y,Nat.card_congr
      (subgroupOfEquivOfLe (show A ⊓ Y ≤ Y from inf_le_right)).toEquiv]
    exact hoA.of_dvd_nat (card_dvd_of_le (show A ⊓ Y ≤ A from inf_le_left))
  obtain ⟨Dbar,hDA,hDC,hDc,hDn⟩ := Triality.Standard.BinarySolvableEscape.marked_actor_cubic
    Cbar Rbar Abar Q e (map_mono hRCY) hR (hoAY.of_dvd_nat (card_map_dvd _ q))
    (c.image_intersection_permutes_sylow h.sylow_normalizes hTY q) hcases
  have hdis : Disjoint (pCore 2 Y) AY := by
    apply disjoint_of_coprime_natCard
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := Y)).exists_card_eq
    rw [hk]
    exact hoAY.coprime_two_left.pow_left k
  let r := q.comp AY.subtype
  have hr : Function.Injective r := by
    apply r.ker_eq_bot_iff.mp
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    apply eq_bot_iff.mpr
    intro x hx
    exact Subtype.ext (disjoint_def.mp hdis hx x.property)
  let a : AY ≃* Abar := (MonoidHom.ofInjective hr).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp,range_subtype]))
  let f := AY.subtype.comp a.symm.toMonoidHom
  let DY := (Dbar.subgroupOf Abar).map f
  have hf : Function.Injective f := AY.subtype_injective.comp a.symm.injective
  have hDYA : DY ≤ AY := by rintro _ ⟨x,_,rfl⟩; exact (a.symm x).property
  have hDYc : Nat.card DY = 3 := by
    rw [card_map_of_injective hf,Nat.card_congr (subgroupOfEquivOfLe hDA).toEquiv,hDc]
  have hDYq : DY.map q = Dbar := by
    rw [map_map]
    have he : q.comp f = Abar.subtype := by
      ext x
      exact congrArg Subtype.val (a.apply_symm_apply x)
    rw [he,map_subgroupOf_eq_of_le hDA]
  let := hCn
  have hDYC : DY ≤ C := odd_lift_le_normal q (by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) C DY
    (by rw [hDYc]; decide) (by rw [hDYq]; exact hDC)
  refine ⟨DY.map Y.subtype,?_,map_mono hDYC,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact hDYA hx
  · rw [card_map_of_injective Y.subtype_injective,hDYc]
  · intro hn
    apply hDn
    rw [←hDYq]
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq ((map_subtype_le (pResidual 2 H)).trans hY.2)]
    intro x hx
    exact hn (mem_map_of_mem Y.subtype hx)

end LocalSieve
open Chapter1.Section02.LocalModels

/-- Retain every preceding exclusion and extract an actual escaping cubic
in the original Cartan and the same binary-triality containing component. -/
theorem localCartan_escape_seed_binaryCubic_reduction
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
          BinaryArmsPlacement T H Y C ∧ BinaryArmsAction T H A B Y C ∧
          BinaryCentralPlacement T H A Y C ∧
          ∃ D : Subgroup G, D ≤ A ∧ D ≤ C.map Y.subtype ∧ Nat.card D = 3 ∧
            ¬ D ≤ normalizer (residual H : Set G)) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        (C.Normal ∨ ((normalizer (C : Set Y)).index = 2 ∧
          K < residual H ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
          IsElementaryAbelian 3 B ∧ Nat.card B = 9 ∧
          Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model))) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hpair⟩ :=
    localCartan_escape_seed_binaryParity_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,?_,hprime,h25,hpair⟩
  intro hm
  obtain ⟨hEven,hdiv,hKR,hCn,ht,hsection,hplacement,haction⟩ := hrank hm
  exact ⟨hEven,hdiv,hKR,hCn,ht,hsection,hplacement,haction,
    LocalSieve.binaryTriality_escape_central_placement h hH hgen c hKH hKL hKT hR
      hY hescape C hC hKC ht,
    LocalSieve.binaryTriality_escape_cubic h hH hgen c hKH hKL hKT hR
      hY hescape C hC hKC ht⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
