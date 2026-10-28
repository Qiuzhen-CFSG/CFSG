module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalOddUnitaryExclusion
public import Theory.SpecificGroups.Classical.LinearFiveFour
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.WreathedIntersection
/-!
# The original cubic excludes the linear four-group alternative

For the actual PSL₃(5) and SL₃(5) containing rows, retain the literal
images in Y/O₂(Y). The original right Hall B has order three and injects
through that two-core. It centralizes the residual's unique involution.
The concrete linear model calculation shows that this same B cannot
normalize any elementary four-group in the component containing that
involution. This discharges the terminal contradiction in the exceptional
four-group-normalizer alternative of 5.1.13. Producing that alternative
from the entire escaping cyclic Cartan is still required.

Source: Aschbacher--Smith 5.1.13, printed p.636, refs/quasithin.pdf.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The same original right Hall excludes every invariant four-group
through the marked residual involution, in either linear containing row. -/
theorem linear_ternary_right_hall_not_normalizes_four
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent) (_hCn : C.Normal)
    (hRC : residual H ≤ C.map Y.subtype)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨ IsSL (C ⧸ pCore 2 C) 3 p) :
    let q := QuotientGroup.mk' (pCore 2 Y)
    let Rbar := ((residual H).subgroupOf Y).map q
    let Cbar := C.map q
    let Bbar := (B.subgroupOf Y).map q
    ∀ z : Y ⧸ pCore 2 Y, z ∈ Rbar → orderOf z = 2 →
      (∀ x : Y ⧸ pCore 2 Y, x ∈ Rbar → orderOf x = 2 → x = z) →
      ∀ E : Subgroup (Y ⧸ pCore 2 Y), E ≤ Cbar →
        IsElementaryAbelian 2 E → Nat.card E = 4 → z ∈ E →
        ¬ Bbar ≤ normalizer (E : Set (Y ⧸ pCore 2 Y)) := by
  intro q Rbar Cbar Bbar z hz hz2 hu E hEC hE hE4 hzE
  have hternary : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
      ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
      IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p :=
    hm.elim Or.inl (fun hh => .inr (.inr (.inl hh)))
  obtain ⟨hp5,hfour,_⟩ := residual_section_of_odd_ternary h hH hgen hY.2 hR C hC hRC hp ho hternary
  subst p
  have hA5 : Nonempty ((residual H ⧸ pCore 2 (residual H)) ≃* alternatingGroup (Fin 5)) := by
    let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
    let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hfour
    exact ⟨eq.symm.trans (a.trans
      (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)⟩
  have hBc := right_hall_card_three_of_residual_A5 h hH hgen c hA5
  have hBY := (c.right_le.trans inf_le_right).trans hY.2
  have hBbar : Nat.card Bbar = 3 := by
    have hd : Nat.card Bbar ∣ 3 := by
      have hd := card_map_dvd (B.subgroupOf Y) q
      rwa [Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv,hBc] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with hb | hb
    · have hz : Bbar = ⊥ := eq_bot_of_card_eq _ hb
      have hle : B.subgroupOf Y ≤ pCore 2 Y := by
        simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
      obtain ⟨k,hk⟩ := (pCore_isPGroup.to_le hle).exists_card_eq
      rw [Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv,hBc] at hk
      have hh : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (by rw [←hk])
      norm_num at hh
    · exact hb
  have hBR : Bbar ≤ Rbar := map_mono (comap_mono (Global.right_cartan_le_residual c))
  have hBC : Bbar ≤ Cbar := by
    apply hBR.trans (map_mono ?_)
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hBz : Bbar ≤ centralizer ({z} : Set (Y ⧸ pCore 2 Y)) := by
    intro b hb
    have hbR := hBR hb
    have he := hu (b*z*b⁻¹) (Rbar.mul_mem (Rbar.mul_mem hbR hz) (Rbar.inv_mem hbR))
      (((MulAut.conj b).orderOf_eq z).trans hz2)
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  let a := (cComponentTwoCoreQuotientEquiv hC).symm
  let := hE
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · let ep := Matrix.SL3.equivProjectiveOfCenterEqBot F
      ((Matrix.SL3.center_eq_bot_iff_card_mod_three F).mpr (by rw [hF]; decide))
    exact Theory.SpecificGroups.Classical.LinearFiveFour.cubic_subgroup_not_normalizes_four
      Cbar E Bbar ((a.trans e).trans ep.symm) hF hEC hBC hE4 hBbar z hzE hz2 hBz
  · exact Theory.SpecificGroups.Classical.LinearFiveFour.cubic_subgroup_not_normalizes_four
      Cbar E Bbar (a.trans e) hF hEC hBC hE4 hBbar z hzE hz2 hBz
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
/-- Every elementary four in the full component Sylow is excluded by the
original right Hall. The marked involution lies in it by the wreathed model. -/
theorem linear_ternary_right_hall_not_normalizes_sylow_four
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : C.Normal)
    (hRC : residual H ≤ C.map Y.subtype)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨ IsSL (C ⧸ pCore 2 C) 3 p) :
    let q := QuotientGroup.mk' (pCore 2 Y)
    let Rbar := ((residual H).subgroupOf Y).map q
    let Cbar := C.map q
    let Tbar := ((T : Subgroup G).subgroupOf Y).map q
    let Bbar := (B.subgroupOf Y).map q
    ∀ z : Y ⧸ pCore 2 Y, z ∈ Rbar → orderOf z = 2 →
      (∀ x : Y ⧸ pCore 2 Y, x ∈ Rbar → orderOf x = 2 → x = z) →
      z ∈ Tbar → Tbar ≤ centralizer ({z} : Set (Y ⧸ pCore 2 Y)) →
      ∀ E : Subgroup (Y ⧸ pCore 2 Y), E ≤ Cbar ⊓ Tbar →
        IsElementaryAbelian 2 E → Nat.card E = 4 →
        ¬ Bbar ≤ normalizer (E : Set (Y ⧸ pCore 2 Y)) := by
  intro q Rbar Cbar Tbar Bbar z hz hz2 hu hzT hTC E hE hEab hE4
  apply linear_ternary_right_hall_not_normalizes_four h hH hgen c hY hR C hC hCn hRC hp ho hm
    z hz hz2 hu E (hE.trans inf_le_left) hEab hE4
  have hternary : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
      ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
      IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p :=
    hm.elim Or.inl (fun hh => .inr (.inr (.inl hh)))
  have hp5 := (residual_section_of_odd_ternary h hH hgen hY.2 hR C hC hRC hp ho hternary).1
  subst p
  let a := (cComponentTwoCoreQuotientEquiv hC).symm
  have hW : ∀ S : Sylow 2 Cbar, Nonempty (S ≃* WreathedThirtyTwo) := by
    intro S
    rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
    · let eC := a.trans e
      exact ⟨(eC.subgroupMap (S : Subgroup Cbar)).trans
        (Theory.SpecificGroups.Classical.SylowMarkedSL2.psl3_five_sylow_wreath hF
          (S.mapSurjective eC.surjective)).some⟩
    · let ep := Matrix.SL3.equivProjectiveOfCenterEqBot F
        ((Matrix.SL3.center_eq_bot_iff_card_mod_three F).mpr (by rw [hF]; decide))
      let eC := (a.trans e).trans ep
      exact ⟨(eC.subgroupMap (S : Subgroup Cbar)).trans
        (Theory.SpecificGroups.Classical.SylowMarkedSL2.psl3_five_sylow_wreath hF
          (S.mapSurjective eC.surjective)).some⟩
  let Q := (T.subtype (hH.1.1.2.trans hY.2)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 Y))
  let : Cbar.Normal := Subgroup.Normal.map hCn q (QuotientGroup.mk'_surjective _)
  obtain ⟨S,hS⟩ := Q.exists_subgroupOf_eq_of_normal Cbar
  have hRC' : Rbar ≤ Cbar := by
    apply map_mono
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  let zC : Cbar := ⟨z,hRC' hz⟩
  have hzS : zC ∈ S := by
    change zC ∈ (S : Subgroup Cbar)
    rw [hS]
    exact hzT
  let zS : S := ⟨zC,hzS⟩
  have hzSc : zS ∈ center S := by
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    apply Subtype.ext
    have hsT : s.val.val ∈ Tbar := by
      have hh : s.val ∈ (S : Subgroup Cbar) := s.property
      rw [hS] at hh
      exact hh
    exact mem_centralizer_singleton_iff.mp (hTC hsT)
  let E' := (E.subgroupOf Cbar).subgroupOf (S : Subgroup Cbar)
  have hES : E.subgroupOf Cbar ≤ (S : Subgroup Cbar) := by
    rw [hS]
    exact comap_mono (hE.trans inf_le_right)
  let eE := (subgroupOfEquivOfLe hES).trans (subgroupOfEquivOfLe (hE.trans inf_le_left))
  let := hEab
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.of_injective eE.toMonoidHom eE.injective
  have hh := Theory.SpecificGroups.Classical.LinearFiveFour.central_involution_mem_four_of_wreathed
    (hW S).some E' ((Nat.card_congr eE.toEquiv).trans hE4) zS
    ((orderOf_coe zS).symm.trans ((orderOf_coe zC).symm.trans hz2)) hzSc
  exact hh
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
/-- The remaining linear row admits no original right-Hall-invariant four-group
through its marked involution. All earlier restrictions remain at the same seed. -/
theorem localCartan_escape_seed_linear_four_reduction
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
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ (ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p)) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨ IsSL (C ⧸ pCore 2 C) 3 p) →
          K = residual H ∧ p = 5 ∧
            ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
            IsSL (((residual H).subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) 2 5 ∧
            Nat.card B = 3 ∧
            let q := QuotientGroup.mk' (pCore 2 Y)
            let Rbar := ((residual H).subgroupOf Y).map q
            let Cbar := C.map q
            let Tbar := ((T : Subgroup G).subgroupOf Y).map q
            ∃ z : Y ⧸ pCore 2 Y,
              z ∈ Rbar ∧ orderOf z = 2 ∧
              (∀ x : Y ⧸ pCore 2 Y, x ∈ Rbar → orderOf x = 2 → x = z) ∧
              z ∈ Tbar ∧
              Tbar ⊔ (B.subgroupOf Y).map q ≤ centralizer ({z} : Set (Y ⧸ pCore 2 Y)) ∧
              Rbar = ⁅Cbar ⊓ centralizer ({z} : Set (Y ⧸ pCore 2 Y)),
                Cbar ⊓ centralizer ({z} : Set (Y ⧸ pCore 2 Y))⁆ ∧
              (normalizer (residual H : Set G)).subgroupOf Y =
                (centralizer ({z} : Set (Y ⧸ pCore 2 Y))).comap q ∧
              (∀ E : Subgroup (Y ⧸ pCore 2 Y), E ≤ Cbar ⊓ Tbar →
                IsElementaryAbelian 2 E → Nat.card E = 4 →
                ¬ (B.subgroupOf Y).map q ≤ normalizer (E : Set (Y ⧸ pCore 2 Y))) ∧
              ∃ a : (A ⊓ Y : Subgroup G), q ⟨a.val,a.property.2⟩ * z * (q ⟨a.val,a.property.2⟩)⁻¹ ≠ z) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hU,hLin⟩ :=
    localCartan_escape_seed_nonunitary_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hU,?_⟩
  intro p hp ho hm
  obtain ⟨he,hp5,hfour,hsl,hB,z,hz,hz2,hu,hzT,hfix,hder,hnorm,hmove⟩ := hLin p hp ho hm
  exact ⟨he,hp5,hfour,hsl,hB,z,hz,hz2,hu,hzT,hfix,hder,hnorm,
    LocalSieve.linear_ternary_right_hall_not_normalizes_sylow_four h hH hgen c hY
      (he ▸ hKL) C hC hCn (he ▸ hKC) hp ho hm z hz hz2 hu hzT
        (le_sup_left.trans hfix),hmove⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
