module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.MarkedMovedSection
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Saturated
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import Theory.Mathieu.M23.Properties.MovedNormalizer
public import Theory.Mathieu.SchurMultipliers.M23TwoKernelSource

/-!
# M₂₃ exclusion on the actual moved subgroup

The original moved-normalizer bound implies that N_I([V,L]) normalizes L.
The trivial central kernel of M₂₃ transports this exact restriction to the
marked quotient. Full movement and perfectness give at least eight elements
in its elementary moved image, while the intrinsic two-core quotient retains
its factor 168. The native M₂₃ normalizer comparison then makes every opposite
moved involution centralize I, contradicting the original source bound.

This proves the comparison for all binary-three rows without irreducibility,
including fixed kernels and nonsplit extensions. Quasisimple.Source applies
it to finish the natural and dual sections. Source: Aschbacher--Smith 10.2.9,
printed pp.750--751.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c


/-- The trivial M₂₃ multiplier makes the literal quotient map injective.
Transport the normalizer restriction already proved on the original moved
subgroup; no normalizer assertion is inferred from the carrier name. -/
theorem mathieuTwentyThree_moved_normalizer [Group.IsPerfect I]
    (e : (I ⧸ center I) ≃* Sporadic.Mathieu.M23) :
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center I))
    normalizer (((⁅D.fullModule,L⁆).subgroupOf I).map q : Set Sporadic.Mathieu.M23) ≤
      normalizer ((L.subgroupOf I).map q : Set Sporadic.Mathieu.M23) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center I))
  let f : PerfectCentralCovering.Cover I Sporadic.Mathieu.M23 := {
    toMonoidHom := q
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := by
      intro x hx
      apply (QuotientGroup.eq_one_iff x).mp
      exact e.injective ((MonoidHom.mem_ker.mp hx).trans (map_one e).symm) }
  have hq : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp
    (Sporadic.Mathieu.SchurMultipliers.M23TwoKernelSource.kernel_eq_bot f)
  let a : I ≃* Sporadic.Mathieu.M23 := MulEquiv.ofBijective q ⟨hq,f.surjective⟩
  change normalizer (((⁅D.fullModule,L⁆).subgroupOf I).map a.toMonoidHom : Set Sporadic.Mathieu.M23) ≤
    normalizer ((L.subgroupOf I).map a.toMonoidHom : Set Sporadic.Mathieu.M23)
  rw [←map_equiv_normalizer_eq,←map_equiv_normalizer_eq]
  exact map_mono (moved_normalizer_le_component_normalizer D c)

theorem mathieuTwentyThree_quotient_fixer [Group.IsPerfect I]
    (h168 : 168 ∣ Nat.card (L ⧸ pCore 2 L))
    (e : (I ⧸ center I) ≃* Sporadic.Mathieu.M23) :
    let B := (L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
    ∀ a : MulAut Sporadic.Mathieu.M23, a^2=1 → (∀ x ∈ B, a x=x) → a=1 := by
  obtain ⟨S,_,_,hSB,_,_,_,hE,_,hne,hmove⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map (e.toMonoidHom.comp q)
  let E := ((⁅D.fullModule,L⁆).subgroupOf I).map (e.toMonoidHom.comp q)
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPB : (P : Subgroup Sporadic.Mathieu.M23) ≤ normalizer (B : Set Sporadic.Mathieu.M23) := by
    change ((R : Subgroup (I ⧸ center I)).map e.toMonoidHom) ≤ _
    change _ ≤ normalizer (↑((L.subgroupOf I).map (e.toMonoidHom.comp q)) : Set Sporadic.Mathieu.M23)
    rw [←Subgroup.map_map]
    exact
      (map_mono (f := e.toMonoidHom) hSB).trans (le_normalizer_map e.toMonoidHom)
  have hEp : IsElementaryAbelian 2 E := by
    let := hE
    change IsElementaryAbelian 2 (((⁅D.fullModule,L⁆).subgroupOf I).map (e.toMonoidHom.comp q))
    rw [←Subgroup.map_map]
    exact IsElementaryAbelian.map (p := 2) (A := ((⁅D.fullModule,L⁆).subgroupOf I).map q) e.toMonoidHom
  have hBE : B ≤ normalizer (E : Set Sporadic.Mathieu.M23) := by
    have hn : L.subgroupOf I ≤ normalizer ((⁅D.fullModule,L⁆).subgroupOf I : Set I) := by
      rw [←subgroupOf_normalizer_eq ((source_full_moved_le_component D).trans c.strict.le)]
      exact comap_mono (normalizer_commutator_ge_right _ _)
    exact (map_mono hn).trans (le_normalizer_map _)
  have hEB : E ≤ B := map_mono (comap_mono (source_full_moved_le_component D))
  let := Chapter1.mem_L_isPerfect D.maximal.1
  have hB : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := markedLocalHom c.strict.le e) (markedLocalHom_surjective c.strict.le e)
  let := hB
  let := hEp
  let F := E.subgroupOf B
  let : F.Normal := normal_subgroupOf_of_le_normalizer hBE
  have hmov : ⁅E,B⁆ = E := by
    simpa only [E,B,map_commutator,map_map] using congrArg (map e.toMonoidHom) hmove
  have hFmov : ⁅F,(⊤ : Subgroup B)⁆ = F := by
    apply map_injective B.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hEB,←MonoidHom.range_eq_map,
      range_subtype,hmov]
  have hFne : F ≠ ⊥ := by
    intro hf
    have heq : E = ⊥ := by
      rw [←map_subgroupOf_eq_of_le hEB]
      change F.map B.subtype = ⊥
      rw [hf,Subgroup.map_bot]
    apply hne
    apply (map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp
    simpa only [E,←map_map] using heq
  have hcard : 8 ≤ Nat.card E := by
    have hh := commutator_card_ge_eight_of_isPerfect (⊤ : Subgroup B) F
      ((IsElementaryAbelian.isPGroup 2 E).comap_of_injective B.subtype B.subtype_injective)
      (hFmov.symm ▸ hFne)
    rwa [hFmov,Nat.card_congr (subgroupOfEquivOfLe hEB).toEquiv] at hh
  have h168B : 168 ∣ Nat.card (B ⧸ pCore 2 B) := by
    have hh := Nat.card_congr (markedCoreQuotientEquiv D c.strict.le e).toEquiv
    exact hh ▸ h168
  exact Sporadic.Mathieu.M23Geometry.eq_one_of_fixes_moved_normalizer
    P B E hPB hEp hEB hBE hcard h168B
      (mathieuTwentyThree_moved_normalizer D c e)

theorem mathieuTwentyThree_common_centralizer [IsQuasisimple I]
    (h168 : 168 ∣ Nat.card (L ⧸ pCore 2 L))
    (e : (I ⧸ center I) ≃* Sporadic.Mathieu.M23) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G) := by
  let B := (L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
  have hfixer := mathieuTwentyThree_quotient_fixer D c h168 e
  let U := (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  let := source_original_full_moved_elementary D
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  intro u hu
  let a : MulAut I := I.normalizerMonoidHom ⟨u,partner_normalizes D c hu⟩
  have ha2 : a ^ 2 = 1 := by
    change (I.normalizerMonoidHom ⟨u,partner_normalizes D c hu⟩) ^ 2 = 1
    rw [←map_pow]
    have he : (⟨u,partner_normalizes D c hu⟩ : normalizer (I : Set G)) ^ 2 = 1 :=
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := U) u hu)
    rw [he,map_one]
  have hfix : ∀ x ∈ B, MulAut.centralQuotientAction e a x = x := by
    intro x hx
    obtain ⟨l,hl⟩ := markedLocalHom_surjective c.strict.le e ⟨x,hx⟩
    have hxval := congrArg Subtype.val hl
    change e (QuotientGroup.mk' (center I) (inclusion c.strict.le l)) = x at hxval
    rw [←hxval,MulAut.centralQuotientAction_apply]
    have hal : a (inclusion c.strict.le l) = inclusion c.strict.le l := by
      apply Subtype.ext
      change u*l.val*u⁻¹=l.val
      exact mul_inv_eq_iff_eq_mul.mpr (c.crossed hu l.val l.property).symm
    rw [hal]
  have hqa : MulAut.centralQuotientAction e a = 1 :=
    hfixer _
      (by rw [←map_pow,ha2,map_one]) hfix
  have ha : a = 1 := MulAut.centralQuotientAction_injective e
    (hqa.trans (map_one _).symm)
  intro i hi
  have hh := congrArg (fun b : MulAut I => (b ⟨i,hi⟩ : G)) ha
  change u*i*u⁻¹=i at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The M₂₃ carrier is impossible on every original binary-three row.
The fixed kernel, nonsplit extensions and all fixed vectors are retained. -/
theorem not_mathieuTwentyThree_of_binary_three [IsQuasisimple I]
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (e : (I ⧸ center I) ≃* Sporadic.Mathieu.M23) : False := by
  apply source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer
    I c.escapes
  apply mathieuTwentyThree_common_centralizer D c _ e
  rw [Nat.card_congr dL.toEquiv,Matrix.PSL3Two.card_SL]

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
