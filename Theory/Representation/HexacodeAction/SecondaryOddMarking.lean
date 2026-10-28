module

public import Theory.Representation.HexacodeAction.SecondaryEquality
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.ElementaryAbelian.Injective

/-!
# The even intersection of an odd secondary actor

An odd rank-three actor fixing a binary plane on the hexacode has a literal
even intersection of rank two. The plane and its cubic-scalar image are
disjoint and both are fixed by that intersection, which is consequently a
hexacode offender. Every secondary fixed-codimension bound restricts along
the same original coordinate map.

This retains the equality case in the secondary product calculation of
Aschbacher--Smith 12.7.20, printed p.846.
-/

public section
open Atlas.Codes Subgroup Representation.BinaryOffender
namespace Representation.Hexacode.SecondaryOddMarking

private theorem odd_element {A : Subgroup HexAutomorphisms}
    (ho : ¬ A ≤ hexSign.ker) : ∃ g ∈ A, hexSign g = -1 := by
  obtain ⟨g,hg,hge⟩ := Set.not_subset.mp ho
  exact ⟨g,hg,(Int.units_eq_one_or (hexSign g)).resolve_left hge⟩

private theorem even_intersection_card (A : Subgroup HexAutomorphisms)
    (hA : IsElementaryTwo A) (hr : rank A = 3) (ho : ¬ A ≤ hexSign.ker) :
    Nat.card (A ⊓ hexSign.ker : Subgroup HexAutomorphisms) = 4 := by
  obtain ⟨g,hg,hgo⟩ := odd_element ho
  have he : A.map hexSign = ⊤ := by
    apply eq_top_iff.mpr
    intro u _
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact one_mem _
    · exact ⟨g,hg,hgo⟩
  have hc := IsElementaryAbelian.card_inf_ker_mul_card_map A hexSign
  rw [he, card_top, Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int,
    hA.card_eq_two_pow_rank, hr] at hc
  omega

private theorem scalar_span_le_even_fixed (A : Subgroup HexAutomorphisms) :
    fixedSpace action A ⊔ (fixedSpace action A).map (action hexZ) ≤
      fixedSpace action (A ⊓ hexSign.ker) := by
  apply sup_le
  · exact fixedSpace_antitone action inf_le_left
  · rintro v ⟨w,hw,rfl⟩ a
    change action a.val (action hexZ w) = action hexZ w
    rw [action_commutes_scalar a.val a.property.2]
    exact congrArg (action hexZ) (hw ⟨a.val,a.property.1⟩)

private theorem fixed_scalar_disjoint (A : Subgroup HexAutomorphisms)
    (ho : ¬ A ≤ hexSign.ker) :
    Disjoint (fixedSpace action A) ((fixedSpace action A).map (action hexZ)) := by
  obtain ⟨g,hg,hgo⟩ := odd_element ho
  apply disjoint_iff.mpr
  apply bot_unique
  rintro v ⟨hv,w,hw,rfl⟩
  have hs : action g (action hexZ w) = action hexZ w := hv ⟨g,hg⟩
  rw [scalar_eq_omega_smul] at hs
  have hz := ThompsonOffenders.eq_zero_of_odd_fixes_scalar g hgo w (hw ⟨g,hg⟩) hs
  simp [hz]

/-- The actual even intersection of the odd equality actor is an equality
offender on the hexacode, retaining its full ambient subgroup. -/
theorem even_intersection_offender (A : Subgroup HexAutomorphisms)
    (hA : IsElementaryTwo A) (hr : rank A = 3) (ho : ¬ A ≤ hexSign.ker)
    (hd : fixedCodim action A = 4) :
    IsElementaryTwo (A ⊓ hexSign.ker) ∧ rank (A ⊓ hexSign.ker) = 2 ∧
      fixedCodim action (A ⊓ hexSign.ker) = 2 ∧
      IsOffender action (A ⊓ hexSign.ker) := by
  let B := A ⊓ hexSign.ker
  let : IsElementaryAbelian 2 A := hA.2
  have hc : Nat.card B = 4 := even_intersection_card A hA hr ho
  have hB : IsElementaryTwo B := by
    refine ⟨?_, IsElementaryAbelian.of_injective
      (Subgroup.inclusion (show B ≤ A from inf_le_left)) (Subgroup.inclusion_injective _)⟩
    intro hz
    rw [hz, card_bot] at hc
    omega
  have hBr : rank B = 2 := by rw [rank,hc]; decide
  have hdim : Module.finrank (ZMod 2) (fixedSpace action A) = 2 := by
    have h := fixedCodim_add_finrank action A
    rw [hexacode_finrank, hd] at h
    omega
  have hmap : Module.finrank (ZMod 2) ((fixedSpace action A).map (action hexZ)) = 2 :=
    ((hexAction hexZ).finrank_map_eq _).trans hdim
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (fixedSpace action A) ((fixedSpace action A).map (action hexZ))
  rw [(fixed_scalar_disjoint A ho).eq_bot, finrank_bot, add_zero,
    hdim,hmap] at hsup
  have hlo := Submodule.finrank_mono (scalar_span_le_even_fixed A)
  rw [hsup] at hlo
  change 2 + 2 ≤ Module.finrank (ZMod 2) (fixedSpace action B) at hlo
  have htotal := fixedCodim_add_finrank action B
  rw [hexacode_finrank] at htotal
  have hupper : fixedCodim action B ≤ 2 := by omega
  have hlow : 2 ≤ fixedCodim action B := by
    have he : B ≤ hexSign.ker := inf_le_right
    have hn : B.subgroupOf hexSign.ker ≠ ⊥ := by
      intro hz
      have hm := map_subgroupOf_eq_of_le he
      rw [hz, Subgroup.map_bot] at hm
      exact hB.1 hm.symm
    have hh := ThompsonOffenders.fixedCodim_ge_two (B.subgroupOf hexSign.ker) hn
    unfold fixedCodim at hh ⊢
    change 2 ≤ Module.finrank (ZMod 2)
      (_ ⧸ fixedSpace (action.comp hexSign.ker.subtype) (B.subgroupOf hexSign.ker)) at hh
    rwa [fixedSpace_comp_map, map_subgroupOf_eq_of_le he] at hh
  exact ⟨hB,hBr,le_antisymm hupper hlow,hB,by rw [hBr]; exact hupper⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The whole product budget always contains an actual even equality actor.
In the odd case it is precisely the original actor's even intersection. -/
theorem product_budget_even_subactor
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (hσ : Function.Injective σ) (A : Subgroup HexAutomorphisms)
    (hA : IsElementaryTwo A)
    (hb : fixedCodim (action.prod (σ.comp hexCoordinateSixHom)) A ≤ 2 * rank A) :
    ∃ B ≤ A, B ≤ hexSign.ker ∧ IsElementaryTwo B ∧ rank B = 2 ∧
      fixedCodim action B = 2 ∧ fixedCodim σ (B.map hexCoordinateSixHom) = 2 ∧
      IsOffender action B ∧ IsOffender σ (B.map hexCoordinateSixHom) := by
  rcases SecondaryEquality.product_budget_cases σ hσ A hA hb with
    ⟨he,hr,hd,hs,hoff⟩ | ⟨ho,hr,hd,hs,_⟩
  · exact ⟨A,le_rfl,he,hA,hr,hd,hs,⟨hA,by omega⟩,hoff⟩
  · let B := A ⊓ hexSign.ker
    obtain ⟨hB,hBr,hBd,hBo⟩ := even_intersection_offender A hA hr ho hd
    have hm : B.map hexCoordinateSixHom ≤ A.map hexCoordinateSixHom :=
      map_mono inf_le_left
    have hdim := Submodule.finrank_mono (fixedSpace_antitone σ hm)
    have hsumA := fixedCodim_add_finrank σ (A.map hexCoordinateSixHom)
    have hsumB := fixedCodim_add_finrank σ (B.map hexCoordinateSixHom)
    have hle : fixedCodim σ (B.map hexCoordinateSixHom) ≤ 2 := by omega
    have hcomp : fixedCodim (σ.comp hexCoordinateSixHom) B =
        fixedCodim σ (B.map hexCoordinateSixHom) := by
      unfold fixedCodim
      rw [fixedSpace_comp_map]
    have hprod : fixedCodim (action.prod (σ.comp hexCoordinateSixHom)) B ≤
        2 * rank B := by
      rw [fixedCodim_prod,hcomp,hBd,hBr]
      omega
    rcases SecondaryEquality.product_budget_cases σ hσ B hB hprod with
      ⟨he,_,_,hBs,hBsO⟩ | ⟨hne,_⟩
    · exact ⟨B,inf_le_left,he,hB,hBr,hBd,hBs,hBo,hBsO⟩
    · exact (hne inf_le_right).elim

/-- The original cubic ratio supplies an even equality actor with cubicity
retained on the whole product and the original coordinate image. -/
theorem cubic_product_even_actor
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (hσ : Function.Injective σ)
    (hb : cubicRatio (action.prod (σ.comp hexCoordinateSixHom)) ≤ 2) :
    ∃ B : Subgroup HexAutomorphisms, B ≤ hexSign.ker ∧ IsElementaryTwo B ∧
      IsCubic (action.prod (σ.comp hexCoordinateSixHom)) B ∧ rank B = 2 ∧
      fixedCodim action B = 2 ∧ fixedCodim σ (B.map hexCoordinateSixHom) = 2 ∧
      IsOffender action B ∧ IsOffender σ (B.map hexCoordinateSixHom) := by
  obtain ⟨A,hA,hc,hd⟩ := (cubicRatio_le_nat_iff _ 2).mp hb
  obtain ⟨B,hBA,he,hB,hr,hBd,hs,hBo,hso⟩ :=
    product_budget_even_subactor σ hσ A hA hd
  have hcu : IsCubic (action.prod (σ.comp hexCoordinateSixHom)) B :=
    fun a ha b hb c hc' v => hc a (hBA ha) b (hBA hb) c (hBA hc') v
  exact ⟨B,he,hB,hcu,hr,hBd,hs,hBo,hso⟩

end Representation.Hexacode.SecondaryOddMarking
