module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Lines
public import Theory.SpecificGroups.Tits.ReeLocalBlockOrders
public import Theory.SpecificGroups.Tits.R1AmbientCosetCover

/-!
# Certified point coordinates in the actual binary Ree building

The checked 1755-row Parrott R₁ cover is transported through the marked
Parrott–Atlas equivalence and its embedding into the derived Ree group.
Exact endpoint images and subgroup orders prove that inverse representatives
are a bijection to the full Ree point cosets. Every signed table transition
is the actual left action of the inverse generator, with no relabeling.

Source: Parrott (1972), p.683; Aschbacher–Smith J.5.6, printed p.447.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge
open Subgroup Tits Theory.GroupTheory.CosetEnumeration
open Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
open Tits.ExceptionalParabolics
local instance pointAction : MulAction (Model 0) PointCoset :=
  @MulAction.quotient (Model 0) (Model 0) (modelGroup 0) inferInstance
    (Monoid.toMulAction _) FullRee.first (MulAction.left_quotientAction _)

def presentationMap : ParrottGroup →* Model 0 :=
  FullRee.atlasEmbedding.comp parrottFiniteImageEquiv.toMonoidHom

theorem presentationMap_injective : Function.Injective presentationMap :=
  FullRee.atlasEmbedding_injective.comp parrottFiniteImageEquiv.injective

theorem presentationMap_first :
    parrottR1Subgroup.map presentationMap = FullRee.first ⊓ commutator (Model 0) := by
  rw [presentationMap, ← map_map, ReeLocalBlockOrders.first_map, FullRee.atlas_first_map]

theorem presentationMap_range : presentationMap.range = commutator (Model 0) := by
  rw [presentationMap, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
    parrottFiniteImageEquiv.surjective, ← MonoidHom.range_eq_map, FullRee.atlasEmbedding_range]

theorem presentationMap_comap_first : FullRee.first.comap presentationMap = parrottR1Subgroup := by
  have he : (parrottR1Subgroup.map presentationMap).comap presentationMap = parrottR1Subgroup :=
    comap_map_eq_self (show presentationMap.ker ≤ parrottR1Subgroup from by
      rw [presentationMap.ker_eq_bot presentationMap_injective]; exact bot_le)
  have ht : presentationMap.range.comap presentationMap = ⊤ := by
    ext x; exact ⟨fun _ => mem_top _, fun _ => ⟨x,rfl⟩⟩
  rw [presentationMap_first, comap_inf, ← presentationMap_range, ht, inf_top_eq] at he
  exact he

def cover : ParrottR1CosetCover where
  rep i := representative parrottGenerator R1Certificate.input (R1Certificate.index i)
  initial := 0
  initial_eq := by
    change representative parrottGenerator R1Certificate.input
      (R1Certificate.index R1Certificate.initial) = 1
    simp [representative, R1Certificate.initial_index, R1Certificate.model.zero]
  step a := tablePermutation R1Certificate.table R1Certificate.inverse_table (a,true)
  transition i a := by
    simpa only [Fact.Valid, Related, eval_singleton, letterValue, ↓reduceIte,
      tablePermutation, Equiv.coe_fn_mk] using R1Certificate.edges i a

def parrottPoint (i : Fin 1755) : ParrottGroup ⧸ parrottR1Subgroup :=
  ((cover.rep i)⁻¹ : ParrottGroup)

theorem parrottPoint_surjective : Function.Surjective parrottPoint := by
  intro q
  obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨h,i,hi⟩ := cover.covers x⁻¹
  refine ⟨i, ?_⟩
  change ((cover.rep i)⁻¹ : ParrottGroup) = (x : ParrottGroup ⧸ parrottR1Subgroup)
  apply QuotientGroup.eq.mpr
  have hx : x = (cover.rep i)⁻¹ * (h : ParrottGroup)⁻¹ := by
    simpa only [inv_inv, mul_inv_rev] using congrArg Inv.inv hi
  rw [inv_inv, hx, mul_inv_cancel_left]
  exact parrottR1Subgroup.inv_mem h.property

theorem parrottPoint_card : Nat.card (ParrottGroup ⧸ parrottR1Subgroup) = 1755 := by
  have h := parrottR1Subgroup.card_mul_index
  rw [ReeLocalBlockOrders.r1_card, parrottGroup_card] at h
  change parrottR1Subgroup.index = 1755
  omega

theorem parrottPoint_bijective : Function.Bijective parrottPoint :=
  parrottPoint_surjective.bijective_of_nat_card_le
    (by rw [Nat.card_fin, parrottPoint_card])

def pointMap (i : Fin 1755) : PointCoset := ((presentationMap (cover.rep i))⁻¹ : Model 0)

theorem point_card : Nat.card PointCoset = 1755 := by
  have h := FullRee.first.card_mul_index
  rw [FullRee.first_card, FullRee.group_card] at h
  change FullRee.first.index = 1755
  omega

theorem line_card : Nat.card LineCoset = 2925 := by
  have h := FullRee.second.card_mul_index
  rw [FullRee.second_card, FullRee.group_card] at h
  change FullRee.second.index = 2925
  omega

theorem pointMap_injective : Function.Injective pointMap := by
  intro i j he
  apply parrottPoint_bijective.1
  change (((cover.rep i)⁻¹ : ParrottGroup) : ParrottGroup ⧸ parrottR1Subgroup) = _
  apply QuotientGroup.eq.mpr
  have hh := QuotientGroup.eq.mp he
  change ((presentationMap (cover.rep i))⁻¹)⁻¹ * (presentationMap (cover.rep j))⁻¹ ∈ FullRee.first at hh
  have hc : (cover.rep i) * (cover.rep j)⁻¹ ∈ FullRee.first.comap presentationMap := by
    simpa only [mem_comap, map_mul, map_inv, inv_inv] using hh
  rw [presentationMap_comap_first] at hc
  simpa only [inv_inv] using hc

def pointEquiv : Fin 1755 ≃ PointCoset := Equiv.ofBijective pointMap
  (pointMap_injective.bijective_of_nat_card_le (by rw [Nat.card_fin, point_card]))

theorem pointEquiv_step (i : Fin 1755) (a : ParrottGenerator) :
    pointEquiv (R1Certificate.table i (a,true)) =
      ((presentationMap (parrottGenerator a))⁻¹ • pointEquiv i : PointCoset) := by
  obtain ⟨h,hh,he⟩ := cover.transition i a
  change (((presentationMap (cover.rep (cover.step a i)))⁻¹ : Model 0) : PointCoset) =
    (presentationMap (parrottGenerator a))⁻¹ •
      (((presentationMap (cover.rep i))⁻¹ : Model 0) : PointCoset)
  rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  apply QuotientGroup.eq.mpr
  have ht : cover.rep (cover.step a i) * (parrottGenerator a)⁻¹ * (cover.rep i)⁻¹ = h⁻¹ := by
    calc
      _ = h⁻¹ * (cover.rep i * parrottGenerator a) * (parrottGenerator a)⁻¹ * (cover.rep i)⁻¹ := by rw [he]; group
      _ = _ := by group
  change ((presentationMap (cover.rep (cover.step a i)))⁻¹)⁻¹ *
    ((presentationMap (parrottGenerator a))⁻¹ * (presentationMap (cover.rep i))⁻¹) ∈ FullRee.first
  rw [inv_inv, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← mul_assoc, ht]
  exact (presentationMap_first ▸ mem_map_of_mem presentationMap
    (parrottR1Subgroup.inv_mem hh)).1


/-- Signed table transitions retain the inverse-representative convention. -/
theorem pointEquiv_letter (i : Fin 1755) (a : Letter ParrottGenerator) :
    pointEquiv (R1Certificate.table i a) =
      ((presentationMap (letterValue parrottGenerator a))⁻¹ • pointEquiv i : PointCoset) := by
  rcases a with ⟨a,b⟩
  cases b
  · simp only [letterValue, Bool.false_eq_true, ↓reduceIte, map_inv, inv_inv]
    have hi : R1Certificate.table (R1Certificate.table i (a,false)) (a,true) = i :=
      R1Certificate.inverse_table i (a,false)
    have he := congrArg (fun q : PointCoset => presentationMap (parrottGenerator a) • q)
      (pointEquiv_step (R1Certificate.table i (a,false)) a)
    rw [hi, smul_inv_smul] at he
    exact he.symm
  · exact pointEquiv_step i a

theorem pointEquiv_zero : pointEquiv 0 = (1 : Model 0) := by
  change (((presentationMap (cover.rep 0))⁻¹ : Model 0) : PointCoset) = _
  rw [show cover.rep 0 = 1 from cover.initial_eq, map_one, inv_one]
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge
