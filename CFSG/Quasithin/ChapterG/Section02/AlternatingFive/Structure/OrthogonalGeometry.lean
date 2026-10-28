module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure.KernelGeometry
public import Theory.Representation.BinaryPermutation.FiveMovedHyperplanes
public import Theory.GroupTheory.InvolutionCentralizerControl
/-!
# The orthogonal intersection and conjugate hyperplanes in G.2.4

The three preceding starred conclusions identify the actual U-image with a
Sylow two-subgroup of the given A₅. Re-marking that action puts the regular
Klein four generators in this image; their fixed vectors identify the original
order-two point, and their differences identify V with the moved hyperplane.
The star kernel acts trivially, so all comparisons use the literal quotient.

The resulting [V_L,U]=V and the G.2.2 Frattini bound exclude V_L≤U. Since
|V|=8 and |V_L|=16, this proves V_L∩U=V. The normalizer of the moved hyperplane
fixes its weight-four point, so the original g gives a different hyperplane;
the two therefore span V_L. No point or hyperplane marking is an assumption.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
G.2.4, printed pp.334--335, using G.2.1--2 on printed p.332.
The source assembly owner must discharge the three starred inputs.
-/

@[expose] public section
open Subgroup BinaryPermutation
open BinaryPermutation.FiveMovedHyperplanes
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}
namespace Hypothesis
variable (d : Hypothesis D g)

private def recoordinate (a : Actor) : Hypothesis D g :=
  { d with
    model := d.model.trans (MulAut.conj a)
    coordinates := d.coordinates.trans (coordinateAut a)
    equivariant := by
      intro l v
      change coordinateAut a (d.coordinates _) = _
      rw [d.equivariant]
      exact coordinateAut_conj a (d.model (starProjection D l)) (d.coordinates v).toAdd }

private def geometryActor (hstar : D.star (D.I g) = D.star D.L) : D.I g →* Actor :=
  d.model.toMonoidHom.comp (d.IStarProjection hstar)

private def geometryImage (hstar : D.star (D.I g) = D.star D.L) (A : Subgroup G) : Subgroup Actor :=
  (A.subgroupOf (D.I g)).map (d.geometryActor hstar)

private theorem geometryImage_eq (hstar : D.star (D.I g) = D.star D.L)
    (A : Subgroup G) (hA : A ≤ D.I g) :
    d.geometryImage hstar A = ((D.star A).subgroupOf (D.star D.L)).map d.model.toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨d.IStarProjection hstar i, ⟨inclusion d.I_le_LT i, hi, rfl⟩, rfl⟩
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨i, hi, he⟩ := hq
    refine ⟨⟨i, hA hi⟩, hi, ?_⟩
    change d.model (d.IStarProjection hstar ⟨i, hA hi⟩) = d.model q
    exact congrArg d.model (Subtype.ext he)

private theorem geometryActor_equivariant (hstar : D.star (D.I g) = D.star D.L)
    (i : D.I g) (v : D.VL) :
    d.coordinates ⟨(i : G) * v * (i : G)⁻¹,
      (mem_normalizer_iff.mp (d.I_normalizes_VL i.property) v).mp v.property⟩ =
      Multiplicative.ofAdd (act (d.geometryActor hstar i) (d.coordinates v).toAdd) :=
  d.IStarProjection_equivariant hstar i v

include d in
private theorem exists_marked_geometry (hstar : D.star (D.I g) = D.star D.L)
    (hSylow : ∃ P : Sylow 2 (D.star D.L),
      (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U) :
    ∃ e : Hypothesis D g,
      CubicFixedSpace.Five.first ∈ e.geometryImage hstar D.U ∧
      CubicFixedSpace.Five.second ∈ e.geometryImage hstar D.U := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hSylow
  let P' := P.mapSurjective (f := d.model.toMonoidHom) d.model.surjective
  obtain ⟨Q, hQ⟩ := CubicFixedSpace.Five.klein_isPGroup.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq Actor P' Q
  have he : (P' : Subgroup Actor).map (MulAut.conj a).toMonoidHom = (Q : Subgroup Actor) := by
    have hh := congrArg (fun R : Sylow 2 Actor => (R : Subgroup Actor)) ha
    rwa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hh
  have hsub : (D.star D.U).subgroupOf (D.star D.L) = (P : Subgroup (D.star D.L)) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective (D.star D.L).subtype_injective _
  have hm : (d.recoordinate a).geometryImage hstar D.U = (Q : Subgroup Actor) := by
    rw [geometryImage_eq _ hstar _ le_sup_left, hsub]
    change (P : Subgroup (D.star D.L)).map
      ((MulAut.conj a).toMonoidHom.comp d.model.toMonoidHom) = _
    rw [← map_map]
    exact he
  refine ⟨d.recoordinate a, ?_, ?_⟩
  · rw [hm]; exact hQ CubicFixedSpace.Five.first_mem
  · rw [hm]; exact hQ CubicFixedSpace.Five.second_mem

-- The inverse coordinates are used in all ambient commutator calculations.
private def geometryMap : Multiplicative Space →* G := D.VL.subtype.comp d.coordinates.symm.toMonoidHom

private theorem geometryMap_injective : Function.Injective d.geometryMap :=
  Subtype.val_injective.comp d.coordinates.symm.injective

private theorem geometryMap_mem (x : Multiplicative Space) : d.geometryMap x ∈ D.VL :=
  (d.coordinates.symm x).property

private theorem geometryMap_coordinates (v : D.VL) : d.geometryMap (d.coordinates v) = v :=
  congrArg Subtype.val (d.coordinates.symm_apply_apply v)

private theorem geometry_conjugation (hstar : D.star (D.I g) = D.star D.L)
    (i : D.I g) (x : Multiplicative Space) :
    (i : G) * d.geometryMap x * (i : G)⁻¹ =
      d.geometryMap (Multiplicative.ofAdd (act (d.geometryActor hstar i) x.toAdd)) := by
  have he := d.geometryActor_equivariant hstar i (d.coordinates.symm x)
  rw [d.coordinates.apply_symm_apply] at he
  apply_fun d.coordinates.symm at he
  simpa only [MulEquiv.symm_apply_apply, geometryMap, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, subtype_apply] using congrArg Subtype.val he

private theorem geometry_commutator (hstar : D.star (D.I g) = D.star D.L)
    (i : D.I g) (x : Space) :
    ⁅(i : G), d.geometryMap (Multiplicative.ofAdd x)⁆ =
      d.geometryMap (Multiplicative.ofAdd (act (d.geometryActor hstar i) x - x)) := by
  have he := d.geometry_conjugation hstar i (Multiplicative.ofAdd x)
  simp only [toAdd_ofAdd] at he
  rw [ofAdd_sub, map_div, div_eq_mul_inv, ← he]
  rfl

private theorem geometryActor_fixes_point (hstar : D.star (D.I g) = D.star D.L)
    (i : D.I g) (hi : (i : G) ∈ centralizer (D.V₁ : Set G)) (z : D.V₁) :
    act (d.geometryActor hstar i)
      (d.coordinates ⟨z, (le_conjugateSpanBy _ _) z.property⟩).toAdd =
      (d.coordinates ⟨z, (le_conjugateSpanBy _ _) z.property⟩).toAdd := by
  have he := d.geometryActor_equivariant hstar i
    ⟨z, (le_conjugateSpanBy _ _) z.property⟩
  have hc : (i : G) * z * (i : G)⁻¹ = z := by
    rw [← hi z z.property, mul_inv_cancel_right]
  have hv : (⟨(i : G) * z * (i : G)⁻¹,
      (mem_normalizer_iff.mp (d.I_normalizes_VL i.property) z).mp ((le_conjugateSpanBy _ _) z.property)⟩ : D.VL) =
      ⟨z, (le_conjugateSpanBy _ _) z.property⟩ := Subtype.ext hc
  rw [hv] at he
  exact he.symm

variable {d}

private theorem marked_point_coordinates (hstar : D.star (D.I g) = D.star D.L)
    (ha : CubicFixedSpace.Five.first ∈ d.geometryImage hstar D.U)
    (hb : CubicFixedSpace.Five.second ∈ d.geometryImage hstar D.U)
    (z : D.V₁) (hz : z ≠ 1) :
    d.coordinates ⟨z, (le_conjugateSpanBy _ _) z.property⟩ =
      Multiplicative.ofAdd AlternatingFiveBorel.fixedVector := by
  apply fixed_generators
  · intro he
    apply hz
    have hh := d.coordinates.injective (he.trans d.coordinates.map_one.symm)
    have hval : (z : G) = 1 := congrArg (fun v : D.VL => (v : G)) hh
    exact Subtype.ext hval
  · obtain ⟨u, hu, he⟩ := ha
    rw [← he]
    exact d.geometryActor_fixes_point hstar u (d.setup.U_le_centralizer_point hu) z
  · obtain ⟨u, hu, he⟩ := hb
    rw [← he]
    exact d.geometryActor_fixes_point hstar u (d.setup.U_le_centralizer_point hu) z

variable (d)
include d

private theorem geometryImage_fixes_last (hstar : D.star (D.I g) = D.star D.L)
    (ha : CubicFixedSpace.Five.first ∈ d.geometryImage hstar D.U)
    (hb : CubicFixedSpace.Five.second ∈ d.geometryImage hstar D.U)
    (A : Subgroup G) (hA : A ≤ D.G₁) :
    ∀ a ∈ d.geometryImage hstar A, a.val 4 = 4 := by
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp d.setup.point_ne_bot
  have hc := marked_point_coordinates hstar ha hb z hz
  rintro _ ⟨i, hi, rfl⟩
  apply (fixes_point_iff _).mp
  have he := d.geometryActor_fixes_point hstar i
    (normalizer_le_centralizer_of_card_two D.V₁ d.point_card (hA hi)) z
  rw [hc] at he
  exact he

private def geometryMoved : Subgroup G := moved.map d.geometryMap

private theorem geometryMoved_le_VL : d.geometryMoved ≤ D.VL := by
  rintro _ ⟨x, _, rfl⟩
  exact d.geometryMap_mem x

private theorem card_geometryMoved : Nat.card d.geometryMoved = 8 :=
  (card_map_of_injective d.geometryMap_injective).trans card_moved

private theorem commutator_le_geometryMoved (hstar : D.star (D.I g) = D.star D.L)
    (A : Subgroup G) (hAI : A ≤ D.I g)
    (hA : ∀ a ∈ d.geometryImage hstar A, a.val 4 = 4) :
    ⁅D.VL, A⁆ ≤ d.geometryMoved := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha v hv
  have he := d.geometry_commutator hstar ⟨a, hAI ha⟩ (d.coordinates ⟨v,hv⟩).toAdd
  rw [ofAdd_toAdd, d.geometryMap_coordinates] at he
  rw [he]
  exact mem_map.mpr ⟨_, difference_mem_moved _ (hA _ (mem_map_of_mem _ ha)) _, rfl⟩

private theorem geometryMoved_le_commutator_U (hstar : D.star (D.I g) = D.star D.L)
    (ha : CubicFixedSpace.Five.first ∈ d.geometryImage hstar D.U)
    (hb : CubicFixedSpace.Five.second ∈ d.geometryImage hstar D.U) :
    d.geometryMoved ≤ ⁅D.VL, D.U⁆ := by
  apply (map_le_iff_le_comap).mpr
  apply moved_le_of_differences
  intro a ha' x
  have hmem : a ∈ d.geometryImage hstar D.U := by
    rcases ha' with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact (d.geometryImage hstar D.U).mul_mem ha hb
  obtain ⟨u, hu, he⟩ := hmem
  change d.geometryMap (Multiplicative.ofAdd (act a x - x)) ∈ ⁅D.VL, D.U⁆
  rw [← he, ← d.geometry_commutator hstar]
  rw [commutator_comm]
  exact commutator_mem_commutator hu (d.geometryMap_mem _)

include d in
/-- Equality of star images gives equality of the actual actions on V_L. -/
private theorem commutator_mono_of_star (hstar : D.star (D.I g) = D.star D.L)
    (A B : Subgroup G) (hA : A ≤ D.I g) (hB : B ≤ D.I g)
    (hAB : D.star A ≤ D.star B) : ⁅D.VL,A⁆ ≤ ⁅D.VL,B⁆ := by
  rw [commutator_comm, commutator_comm D.VL B]
  apply commutator_le.mpr
  intro a ha v hv
  have him : d.geometryActor hstar ⟨a,hA ha⟩ ∈ d.geometryImage hstar B := by
    apply (show d.geometryImage hstar A ≤ d.geometryImage hstar B from ?_)
      (mem_map_of_mem _ ha)
    rw [d.geometryImage_eq hstar A hA, d.geometryImage_eq hstar B hB]
    exact map_mono (subgroupOf_mono _ hAB)
  obtain ⟨b, hb, he⟩ := him
  have hca := d.geometry_commutator hstar ⟨a,hA ha⟩ (d.coordinates ⟨v,hv⟩).toAdd
  have hcb := d.geometry_commutator hstar b (d.coordinates ⟨v,hv⟩).toAdd
  simp only [ofAdd_toAdd, geometryMap_coordinates] at hca hcb
  rw [hca, ← he, ← hcb]
  exact commutator_mem_commutator hb hv

private theorem marked_seed_eq_moved (hstar : D.star (D.I g) = D.star D.L)
    (hBorel : D.star D.U = (D.star D.L₁).pCoreIn 2)
    (ha : CubicFixedSpace.Five.first ∈ d.geometryImage hstar D.U)
    (hb : CubicFixedSpace.Five.second ∈ d.geometryImage hstar D.U) :
    D.V = d.geometryMoved ∧ ⁅D.VL,D.U⁆ = D.V := by
  have hlocal : D.L₁ ≤ D.L := (map_subtype_le _).trans inf_le_left
  have hlocalI := hlocal.trans (d.L_le_I_of_star hstar.ge)
  have hlocalG : D.L₁ ≤ D.G₁ := (map_subtype_le _).trans inf_le_right
  have hVm : D.V ≤ d.geometryMoved := by
    rw [d.seed_eq]
    exact d.commutator_le_geometryMoved hstar D.L₁ hlocalI
      (d.geometryImage_fixes_last hstar ha hb D.L₁ hlocalG)
  have hmU := d.geometryMoved_le_commutator_U hstar ha hb
  have hUV : ⁅D.VL,D.U⁆ ≤ D.V := by
    rw [d.seed_eq]
    apply d.commutator_mono_of_star hstar D.U D.L₁ le_sup_left hlocalI
    rw [hBorel]
    exact pCoreIn_le 2 _
  exact ⟨le_antisymm hVm (hmU.trans hUV), le_antisymm hUV (hVm.trans hmU)⟩

private theorem geometry_normalizer_le_point (hstar : D.star (D.I g) = D.star D.L)
    (ha : CubicFixedSpace.Five.first ∈ d.geometryImage hstar D.U)
    (hb : CubicFixedSpace.Five.second ∈ d.geometryImage hstar D.U)
    (hV : D.V = d.geometryMoved) :
    D.L ⊓ normalizer (D.V : Set G) ≤ D.G₁ := by
  intro l hl
  let i : D.I g := ⟨l, (d.L_le_I_of_star hstar.ge) hl.1⟩
  have hfix : (d.geometryActor hstar i).val 4 = 4 := by
    apply moved_stabilizer
    intro x hx
    have hxV : d.geometryMap x ∈ D.V := hV ▸ mem_map_of_mem _ hx
    have hyV := (mem_normalizer_iff.mp hl.2 (d.geometryMap x)).mp hxV
    rw [d.geometry_conjugation hstar i, hV] at hyV
    obtain ⟨y, hy, he⟩ := hyV
    exact d.geometryMap_injective he ▸ hy
  apply centralizer_le_normalizer (D.V₁ : Set G)
  intro z hz
  by_cases hz1 : z = 1
  · simp [hz1]
  have hzc := marked_point_coordinates hstar ha hb ⟨z,hz⟩
    (fun he => hz1 (congrArg Subtype.val he))
  have he := d.geometryActor_equivariant hstar i
    ⟨z, (le_conjugateSpanBy _ _) hz⟩
  rw [hzc, toAdd_ofAdd, (fixes_point_iff _).mpr hfix] at he
  have he' := d.coordinates.injective (he.trans hzc.symm)
  have hc : l * z * l⁻¹ = z := congrArg Subtype.val he'
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

private theorem geometry_intermediate (hc : Nat.card D.V = 8)
    (K : Subgroup G) (hVK : D.V ≤ K) (hK : K ≤ D.VL) : K = D.V ∨ K = D.VL := by
  have hlo : 8 ≤ Nat.card K := hc ▸ card_le_of_le hVK
  have hd : Nat.card K ∣ 16 := d.card_VL ▸ card_dvd_of_le hK
  have hm := Nat.mem_divisors.mpr ⟨hd, (by decide : 16 ≠ 0)⟩
  rw [show Nat.divisors 16 = {1,2,4,8,16} by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have he : Nat.card K = 8 ∨ Nat.card K = 16 := by omega
  rcases he with he | he
  · exact Or.inl (eq_of_le_of_card_ge hVK (by omega)).symm
  · exact Or.inr (eq_of_le_of_card_ge hK (by rw [d.card_VL, he]))

/-- The Frattini bound excludes V_L ≤ U, so the actual intersection is V. -/
private theorem intersection_of_moved_geometry (hV : D.V ≤ D.VL) (hc : Nat.card D.V = 8)
    (hcomm : ⁅D.VL,D.U⁆ = D.V) : D.VL ⊓ D.U = D.V := by
  have hVU : D.V ≤ D.U := le_conjugateSpanBy _ _
  rcases d.geometry_intermediate hc (D.VL ⊓ D.U) (le_inf hV hVU) inf_le_left with he | he
  · exact he
  have hVU' : D.VL ≤ D.U := he.symm ▸ (show D.VL ⊓ D.U ≤ D.U from inf_le_right)
  have hsmall : D.V ≤ D.V₁ := by
    rw [← hcomm]
    exact (commutator_mono hVU' le_rfl).trans
      (derived_le_of_frattini_image_le d.setup.U_isPGroup d.setup.frattini_U_le_point)
  have hcard := card_le_of_le hsmall
  rw [hc, d.point_card] at hcard
  omega

/-- Different point stabilizers give distinct hyperplanes, for the original g. -/
private theorem conjugate_span_of_moved_geometry (hV : D.V ≤ D.VL) (hc : Nat.card D.V = 8)
    (hn : D.L ⊓ normalizer (D.V : Set G) ≤ D.G₁) :
    D.V ⊔ conjugate D.V g = D.VL := by
  have hconj : conjugate D.V g ≤ D.VL := by
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hV
    have he : D.VL.map (MulAut.conj g⁻¹).toMonoidHom = D.VL :=
      mem_normalizer_iff_map_conj_eq.mp
        ((normalizer (D.VL : Set G)).inv_mem (L_normalizes_VL D d.g_mem))
    rwa [he] at hm
  rcases d.geometry_intermediate hc (D.V ⊔ conjugate D.V g) le_sup_left
      (sup_le hV hconj) with he | he
  · have hle : conjugate D.V g ≤ D.V :=
      (show conjugate D.V g ≤ D.V ⊔ conjugate D.V g from le_sup_right).trans he.le
    have hEq : conjugate D.V g = D.V := eq_of_le_of_card_ge hle
      (card_map_of_injective (MulAut.conj g⁻¹).injective).ge
    have hgi : g⁻¹ ∈ normalizer (D.V : Set G) := mem_normalizer_iff_map_conj_eq.mpr hEq
    have hg : g ∈ normalizer (D.V : Set G) := inv_inv g ▸ (normalizer (D.V : Set G)).inv_mem hgi
    exact (d.g_not_normalizes (hn ⟨d.g_mem,hg⟩)).elim
  · exact he

include d in
/-- The orthogonal geometry used in G.2.4 counting and terminal reduction.
Only the preceding starred conclusions remain explicit. -/
theorem orthogonal_geometry_of_borel
    (hstar : D.star (D.I g) = D.star D.L)
    (hBorel : D.star D.U = (D.star D.L₁).pCoreIn 2)
    (hSylow : ∃ P : Sylow 2 (D.star D.L),
      (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U) :
    D.VL ⊓ D.U = D.V ∧ Nat.card D.V = 8 ∧
      D.V ⊔ conjugate D.V g = D.VL ∧ ⁅D.VL,D.U⁆ = D.V := by
  obtain ⟨e, ha, hb⟩ := d.exists_marked_geometry hstar hSylow
  obtain ⟨hVm, hcomm⟩ := e.marked_seed_eq_moved hstar hBorel ha hb
  have hV : D.V ≤ D.VL := hVm ▸ e.geometryMoved_le_VL
  have hc : Nat.card D.V = 8 := hVm ▸ e.card_geometryMoved
  exact ⟨e.intersection_of_moved_geometry hV hc hcomm, hc,
    e.conjugate_span_of_moved_geometry hV hc
      (e.geometry_normalizer_le_point hstar ha hb hVm), hcomm⟩

variable (hstar : D.star (D.I g) = D.star D.L)
    (hBorel : D.star D.U = (D.star D.L₁).pCoreIn 2)
    (hSylow : ∃ P : Sylow 2 (D.star D.L),
      (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U)
include hstar hBorel hSylow

/-- The source intersection used in the G.2.4 order calculation. -/
theorem VL_inf_U_of_borel : D.VL ⊓ D.U = D.V :=
  (d.orthogonal_geometry_of_borel hstar hBorel hSylow).1

/-- The seed is the eight-element orthogonal moved hyperplane. -/
theorem card_V_of_borel : Nat.card D.V = 8 :=
  (d.orthogonal_geometry_of_borel hstar hBorel hSylow).2.1

/-- The source span, with the original right conjugator retained. -/
theorem V_sup_conjugate_of_borel : D.V ⊔ conjugate D.V g = D.VL :=
  (d.orthogonal_geometry_of_borel hstar hBorel hSylow).2.2.1

/-- The actual U-action on the orthogonal module has moved subgroup V. -/
theorem commutator_VL_U_of_borel : ⁅D.VL,D.U⁆ = D.V :=
  (d.orthogonal_geometry_of_borel hstar hBorel hSylow).2.2.2

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
