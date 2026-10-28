module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CoreFactors
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeSection
public import Theory.Mathieu.M24.LocalGeometry.SextetCore

/-!
# Coordinates on the original M24-code intersection

For the same selected degree-one pair, E.2.10 puts [A,B] inside the
original fixed subgroup U. The actual sextet marking therefore puts B
in the native even code space. Both have dimension ten, so this containment
is equality. The four-space marking and the ten-space marking use the
same whole-code coordinates and the same full original actor.

Source: Aschbacher--Smith E.2.10(2), H.16.1(3), and 8.2.8(4--5), printed
pp.222,402,718, refs/quasithin.pdf. The native Golay calculations are
attributed in the imported NormalizedShadowRows.CodeSection module.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.SextetLayers.CoordinateTransport
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE HermitianSource Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
  {H M I : Subgroup G} {i : I} {S : Sylow 2 I}

/-- The literal B and U have the even-space and four-space markings in
one set of code coordinates. -/
theorem selected_code_section_coordinates
    (s : Selected H T M V I 1 i S)
    (e : Additive V ≃ₗ[ZMod 2] Code) (p : Automizer V →* M24)
    (he : ∀ a v, e (automizerRepresentation V a v) = codeRepresentation (p a) (e v))
    (hAN : V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 ≤ normalizer (V : Set G))
    (hfix : V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hc : (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)).map p = SextetCore.core) :
    (∀ v : Additive V, (v.toMul : G) ∈ V ⊓ centralizer
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) ↔
      e v ∈ CodeFlags.sextetCodeSpace standardSextet) ∧
    (∀ v : Additive V, (v.toMul : G) ∈ V ⊓ I.pCoreIn 2 ↔
      e v ∈ NormalizedShadowRows.CodeSection.evenSpace standardSextet) := by
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  let B := V ⊓ I.pCoreIn 2
  let U := V ⊓ centralizer (A : Set G)
  have hmark (v : Additive V) : (v.toMul : G) ∈ U ↔
      e v ∈ CodeFlags.sextetCodeSpace standardSextet := by
    have hf := fixedSpace_map_equivariant (automizerRepresentation V) codeRepresentation p e he
      (inducedAutomizer V A)
    rw [hc] at hf
    change _ = fixedSpace codeRepresentation (CodeFlags.sextetCore standardSextet) at hf
    rw [CodeFlags.sextetCore_fixedSpace] at hf
    rw [←hf]
    constructor
    · intro hv
      exact ⟨v,(mem_fixedSpace_inducedAutomizer V A hAN v).mpr hv.2,rfl⟩
    · rintro ⟨w,hw,hwv⟩
      have hwv' := e.injective hwv
      rw [hwv'] at hw
      exact ⟨v.toMul.property,(mem_fixedSpace_inducedAutomizer V A hAN v).mp hw⟩
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hbmap : (TwoConjugate.B (V.subgroupOf I) (M.subgroupOf I)).map I.subtype = B := by
    rw [s.twoConjugate.B_eq_twoCore_inf,map_inf _ _ _ I.subtype_injective,
      map_subgroupOf_eq_of_le hVI,inf_comm]
    rfl
  have hcomm : ⁅A,B⁆ ≤ U := by
    have hh := map_mono (f := I.subtype) s.twoConjugate.commutator_A_B_le_Z
    rw [map_commutator,selected_actor_image I M V hVI S i s.twoConjugate,hbmap,
      selected_intersection_image I V hVI i,←hfix] at hh
    exact hh
  have hB (v : Additive V) (hv : (v.toMul : G) ∈ B) :
      e v ∈ NormalizedShadowRows.CodeSection.evenSpace standardSextet := by
    apply (NormalizedShadowRows.CodeSection.displacement_mem_fourSpace_iff _ _).mp
    intro t
    obtain ⟨a,ha,hat⟩ := (show (nativeTranslation standardSextet t).val ∈
      (inducedAutomizer V A).map p by
        rw [hc]
        exact CodeFlags.nativeTranslation_mem_core standardSextet t)
    obtain ⟨a,ha,rfl⟩ := ha
    have hdisp : (automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict a) v - v).toMul.val ∈ U := by
      change (a.val * (v.toMul : G) * a.val⁻¹) / (v.toMul : G) ∈ U
      simpa only [Subgroup.subtype_apply,commutatorElement_def,div_eq_mul_inv] using
        hcomm (commutator_mem_commutator ha hv)
    have hh := (hmark _).mp hdisp
    rw [map_sub,he,hat] at hh
    exact hh
  have hdim : rank V = 11 := by
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_code,Nat.log_pow Nat.one_lt_two]
  have hcor : subgroupCorank V B = 1 := by
    change subgroupCorank V (V ⊓ (pCore 2 I).map I.subtype) = 1
    rw [←quotient_rank_eq_core_corank I V hVI]
    exact s.rank_eq
  have hrB : rank B = 10 := by
    have hh := offender_corank_add (W := V) (A := B) bot_le inf_le_left
    have hh' : rank V = subgroupCorank V B + rank B := by
      simpa only [subgroupCorank,relIndex_bot_left,rank] using hh
    omega
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (show B ≤ V from inf_le_left)
  have hcard : Nat.card B = 2^10 := by
    obtain ⟨a,ha⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
    have hh : rank B = a := by rw [rank,ha,Nat.log_pow Nat.one_lt_two]
    rw [ha]
    congr 1
    omega
  let f : B → NormalizedShadowRows.CodeSection.evenSpace standardSextet :=
    fun b => ⟨e (Additive.ofMul ⟨b,b.property.1⟩),hB _ b.property⟩
  have hfi : Function.Injective f := by
    intro b d hbd
    have hh := e.injective (congrArg Subtype.val hbd)
    exact Subtype.ext (congrArg (fun v : Additive V => (v.toMul : G)) hh)
  have hfs : Function.Surjective f := (hfi.bijective_of_nat_card_le (by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      NormalizedShadowRows.CodeSection.evenSpace_finrank,hcard])).2
  refine ⟨hmark,fun v => ⟨hB v,?_⟩⟩
  intro hv
  obtain ⟨b,hb⟩ := hfs ⟨e v,hv⟩
  have hh := e.injective (congrArg Subtype.val hb)
  have hbv : (b : G) = (v.toMul : G) := congrArg (fun v : Additive V => (v.toMul : G)) hh
  exact hbv ▸ b.property

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
