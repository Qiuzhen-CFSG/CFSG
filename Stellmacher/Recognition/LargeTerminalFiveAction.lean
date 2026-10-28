module

public import Stellmacher.Recognition.LargeTerminalResidual
public import Theory.GroupAction.ComplementQuotientCentralizer
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# An actual order-five subgroup fixes only the first residual center

The large terminal context supplies a subgroup of order five in the actual
mapped first residual group. It normalizes `firstResidual`, and its
centralizer inside that two-group lies in the established center. This is
the fixed subgroup for the canonical conjugation action; the actor group,
residual, and original supplied Sylow remain literal throughout.

The proved first residual image in the vertex quotient has order five.
The exact identity O₂(E)=E∩O₂(P) therefore gives index five in E, and
Schur--Zassenhaus constructs an actual complement A to O₂(E). The quotients
R/V and V/Z are abelian two-groups. The residual acts trivially on both,
while E has full commutator support: residual perfection gives [R,E]=R,
and the transported large terminal support theorem gives [V,E]=V. Thus A
has full coprime support on both quotients. Their fixed groups vanish,
which successively puts C_R(A) inside V and then Z. The exact mapped-center
identity identifies the final subgroup with the center of `firstResidual`.

Neither equality of R with the full vertex two-core nor equality of a
vertex with an ambient involution centralizer is used. The theorem supplies
the actual five-action input for the subsequent Parrott bridge. Source:
Stellmacher (10.1)(18)--(20), printed pp.64--65 of
`refs/files/stellmacher-n-group.pdf`, together with Schur--Zassenhaus and
abelian coprime-action splitting.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
open scoped IsMulCommutative
universe u

private theorem residual_complement_five
    {G : Type u} [Group G] [Finite G] (P : Subgroup G)
    (hfive : Nonempty (((twoResidualIn P).subgroupOf P).map
      (QuotientGroup.mk' (pCore 2 P)) ≃* C5)) :
    ∃ A : Subgroup G, Nat.card A = 5 ∧ A ≤ twoResidualIn P ∧
      twoResidualIn P = twoCoreIn (twoResidualIn P) ⊔ A := by
  let E := twoResidualIn P
  let R := twoCoreIn E
  have hEP : E ≤ P := twoResidualIn_le P
  obtain ⟨e⟩ := hfive
  have hquot : Nat.card ((E.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P))) = 5 :=
    (Nat.card_congr e.toEquiv).trans (by simp [C5])
  rw [← relIndex_ker, QuotientGroup.ker_mk'] at hquot
  have hmap := relIndex_map_map_of_injective (pCore 2 P) (E.subgroupOf P) P.subtype_injective
  rw [map_subgroupOf_eq_of_le hEP] at hmap
  have hindexR : R.relIndex E = 5 := by
    change (twoCoreIn (twoResidualIn P)).relIndex (twoResidualIn P) = 5
    rw [residual_core_eq_inter_core, inf_relIndex_left]
    exact hmap.trans hquot
  have hnative : R.subgroupOf E = pCore 2 E := by
    change ((pCore 2 E).map E.subtype).comap E.subtype = pCore 2 E
    exact comap_map_eq_self_of_injective E.subtype_injective _
  have hindex : (pCore 2 E).index = 5 := by
    change (R.subgroupOf E).index = 5 at hindexR
    rwa [hnative] at hindexR
  have hcop : Nat.Coprime (Nat.card (pCore 2 E)) (pCore 2 E).index := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := E)).exists_card_eq
    rw [hn, hindex]
    exact (by decide : Nat.Coprime 2 5).pow_left n
  obtain ⟨B, hB⟩ := exists_right_complement'_of_coprime hcop
  let A := B.map E.subtype
  refine ⟨A, ?_, map_subtype_le _, ?_⟩
  · exact (card_map_of_injective E.subtype_injective).trans
      (hB.symm.index_eq_card.symm.trans hindex)
  · have h := congrArg (Subgroup.map E.subtype) hB.sup_eq_top
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h.symm

/-- An actual order-five subgroup of the first residual group fixes only
the center of its two-core under conjugation. -/
public theorem LargeTerminalContext.exists_five_subgroup_fixed_center
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) :
    ∃ A : Subgroup G, Nat.card A = 5 ∧
      A ≤ (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
        (ctx.first ⊔ ctx.second).subtype ∧
      A ≤ normalizer (ctx.firstResidual : Set G) ∧
      (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤ center ctx.firstResidual := by
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let Γ := ctx.terminal.Γ
  let cp := ctx.terminal.criticalPath
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let f : K →* G := K.subtype
  have hf : Function.Injective f := K.subtype_injective
  have hlength : cp.length = 3 := ctx.length_three
  have hshort : 1 < cp.length := by omega
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset Γ cp 2 middle := ⟨⟨2, by omega⟩, rfl, rfl⟩
  let P := GAt Γ cp.firstStep
  let Q := QAt Γ cp.firstStep
  let E := EAt Γ cp.firstStep
  let R := twoCoreIn E
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  have hE : E = twoResidualIn P := Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hRE : R ≤ E := twoCoreIn_le E
  have hRQ : R ≤ Q := by
    change twoCoreIn E ≤ Γ.twoCoreAt cp.firstStep
    rw [hE, Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hER : E ≤ normalizer (R : Set K) :=
    (normal_subgroupOf_iff_le_normalizer hRE).mp (twoCoreIn_normal E)
  have hEV : E ≤ normalizer (V : Set K) := hEP.trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hEZ : E ≤ normalizer (Z : Set K) := hEP.trans (stabilizer_le_normalizer_z Γ cp.firstStep)
  have hZdata := nine_next_center_commutator_and_kernel
    tenCtx.toAmbientSectionNineContext hshort cp.firstStep ⟨1, Γ.act_one _⟩
  change Nat.card Z = 2 ∧ ⁅V, Q⁆ = Z ∧ _ at hZdata
  have hVRcomm : ⁅V, R⁆ ≤ Z := (commutator_mono le_rfl hRQ).trans hZdata.2.1.le
  obtain ⟨_, hcenter, hderived, _, _, _⟩ := ctx.first_residual_structure
  change CenterAmbient (R.map f) = Z.map f at hcenter
  change DerivedAmbient (R.map f) = V.map f at hderived
  have hRR : ⁅R, R⁆ = V := by
    apply map_injective hf
    rw [map_commutator]
    rw [show DerivedAmbient (R.map f) = ⁅R.map f, R.map f⁆ from map_subtype_commutator _] at hderived
    exact hderived
  have hVR : V ≤ R := hRR.symm.le.trans (commutator_le_self R)
  have hVnative : V.subgroupOf R = commutator R := by
    apply map_injective R.subtype_injective
    rw [map_subgroupOf_eq_of_le hVR, map_subtype_commutator, hRR]
  let _ : (V.subgroupOf R).Normal := hVnative ▸ inferInstance
  let _ : IsMulCommutative (R ⧸ V.subgroupOf R) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hVnative.ge
  let _ : IsElementaryAbelian 2 V :=
    ((lemma_seven_five tenCtx.sectionSeven Γ cp ctx.commuting).longer_case hshort).1
  let _ : (Z.subgroupOf V).Normal := inferInstance
  have hRtwo : IsPGroup 2 R := (pCore_isPGroup (p := 2) (G := E)).map E.subtype
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry tenCtx middle hpath
  have hperfect : BenderSuzuki.External.hktPResidual 2 E = ⊤ := by
    rw [hE]
    exact twoResidualAmbient_has_top_twoResidual P
  have hodd : Odd (Nat.card (E ⧸ pCore 2 E)) := by
    rw [hE]
    exact local_residual_core_quotient_odd tenCtx.sectionSeven Γ cp.firstStep middle
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hfirst)) P le_rfl
  have hRfull : ⁅R, E⁆ = R := by
    have h := congrArg (Subgroup.map E.subtype)
      (twoCore_eq_commutator_of_residual_perfect hperfect hodd)
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h.symm
  obtain ⟨mover, hmove⟩ := (lemma_seven_one tenCtx.sectionSeven Γ).local_transitivity middle
    ((mem_neighborhood_iff_adjacent Γ).mpr hfirst)
    ((mem_neighborhood_iff_adjacent Γ).mpr hterminal)
  change Γ.act (mover : K) cp.firstStep = cp.a' at hmove
  let e := MulAut.conj (mover : K)⁻¹
  have hPmap : P.map e.toMonoidHom = GAt Γ cp.a' := by
    change conjugateBy (stabilizer Γ cp.firstStep) (mover : K)⁻¹ = stabilizer Γ cp.a'
    rw [← stabilizer_act, hmove]
  have hEmap : E.map e.toMonoidHom = EAt Γ cp.a' := by
    change E.map _ = Γ.twoResidualAt cp.a'
    rw [hE, Γ.twoResidualAt_def, ← twoResidualIn_map_equiv]
    exact congrArg twoResidualIn hPmap
  have hVmap : V.map e.toMonoidHom = VAt Γ cp.a' := by
    change (v Γ cp.firstStep).map _ = v Γ cp.a'
    rw [← v_act, hmove]
  have hVfull : ⁅V, E⁆ = V := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_commutator, hVmap, hEmap]
    exact ten_one_large_terminal_residual_full tenCtx middle hpath ctx.noTransvections
  have hquotient := ten_one_large_first_residual_five tenCtx middle hpath ctx.noTransvections
  change Nonempty ((E.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)) ≃* C5) at hquotient
  rw [hE] at hquotient
  obtain ⟨A, hAcard, hAE, hgen⟩ := residual_complement_five P hquotient
  rw [← hE] at hAE hgen
  have hcopR : Nat.Coprime (Nat.card A) (Nat.card (R ⧸ V.subgroupOf R)) := by
    obtain ⟨n, hn⟩ := (hRtwo.to_quotient (V.subgroupOf R)).exists_card_eq
    rw [hAcard, hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  have hcopV : Nat.Coprime (Nat.card A) (Nat.card (V ⧸ Z.subgroupOf V)) := by
    obtain ⟨n, hn⟩ := ((IsElementaryAbelian.isPGroup 2 V).to_quotient
      (Z.subgroupOf V)).exists_card_eq
    rw [hAcard, hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  have hfixedR := centralizer_le_layer_of_coprime_generating_complement E R A R V
    hgen hER hEV hRfull hRR.le hcopR
  have hfixedV := centralizer_le_layer_of_coprime_generating_complement E R A V Z
    hgen hEV hEZ hVfull hVRcomm hcopV
  have hfixed : R ⊓ centralizer (A : Set K) ≤ Z :=
    (le_inf hfixedR inf_le_right).trans hfixedV
  refine ⟨A.map f, (card_map_of_injective hf).trans hAcard, map_mono hAE, ?_, ?_⟩
  · exact (map_mono (hAE.trans hER)).trans (le_normalizer_map f)
  · intro r hr
    change (r : G) ∈ centralizer (A.map f : Set G) at hr
    obtain ⟨s, hs, hsr⟩ := r.property
    have hscentral : s ∈ centralizer (A : Set K) := by
      rw [mem_centralizer_iff]
      intro a ha
      apply hf
      have h := mem_centralizer_iff.mp hr (f a) (mem_map_of_mem f ha)
      rw [← hsr, ← map_mul, ← map_mul] at h
      exact h
    have hrcenter : (r : G) ∈ CenterAmbient (R.map f) := by
      rw [hcenter]
      exact mem_map.mpr ⟨s, hfixed ⟨hs, hscentral⟩, hsr⟩
    obtain ⟨native, hn, hnr⟩ := hrcenter
    exact (Subtype.ext hnr : native = r) ▸ hn

end Stellmacher.Recognition
