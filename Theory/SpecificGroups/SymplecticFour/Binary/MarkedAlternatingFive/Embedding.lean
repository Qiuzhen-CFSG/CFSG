module

public import Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive.PlaneFour
public import Theory.SpecificGroups.SymmetricSix.ExceptionalAlternatingFive.Natural
public import Theory.Representation.SL2FourNaturalOrbits.BorelFactors

/-!
# A natural SL₂(4) containing the specified rank-two four-group

The given four-group is retained literally. Isotropic-plane conjugacy aligns
the fixed plane of the existing natural embedding with its given plane;
uniqueness of rank-two four-groups then identifies the upper-root image.
-/

noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive
open Matrix Representation.SL2FourNatural
open Representation.SL2FourNatural.BorelFactors
local notation "Bit" => ZMod 2

private theorem upper_nonidentity_fixed (a : F) (ha : upper a ≠ 1) (v : V) :
    action (upper a) v = v ↔ v ∈ upperFixed := by
  have ha0 : a ≠ 0 := by
    intro h
    apply ha
    subst a
    apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [mem_upperFixed]
  constructor
  · intro h
    have hh := congrFun h 0
    rw [upper_action] at hh
    have hz : a * v 1 = 0 := by simpa using hh
    exact (mul_eq_zero.mp hz).resolve_left ha0
  · exact fun hv => (upper_fixed_iff v).mpr hv a

private theorem upperFixed_finrank : Module.finrank Bit upperFixed = 2 := by
  have hh := Module.natCard_eq_pow_finrank (K := Bit) (V := upperFixed)
  rw [card_upperFixed, Nat.card_eq_fintype_card, ZMod.card] at hh
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hh.symm)

/-- An actual symplectic matrix aligns two given isotropic binary planes. -/
public theorem exists_plane_conjugator (W X : Submodule Bit (Vector Bit))
    (hW : Module.finrank Bit W = 2) (hX : Module.finrank Bit X = 2)
    (hiW : ∀ x ∈ W, ∀ y ∈ W, form Bit x y = 0)
    (hiX : ∀ x ∈ X, ∀ y ∈ X, form Bit x y = 0) :
    ∃ g : Sp Bit, W.map (toLinear g).toLinearMap = X := by
  have align (Y : Submodule Bit (Vector Bit)) (hd : Module.finrank Bit Y = 2)
      (hi : ∀ x ∈ Y, ∀ y ∈ Y, form Bit x y = 0) :
      ∃ g : Sp Bit, Y.map (toLinear g).toLinearMap = plane Bit := by
    have hn : Y ≠ ⊥ := by intro h; rw [h, finrank_bot] at hd; omega
    obtain ⟨g,hg⟩ := TwoLocalCover.isotropic_subspace_conjugate_standard Y hn hi
    refine ⟨g, ?_⟩
    rcases hg with hg | hg
    · have hh := (toLinear g).finrank_map_eq Y
      rw [hg, finrank_point, hd] at hh
      omega
    · exact hg
  obtain ⟨a,ha⟩ := align W hW hiW
  obtain ⟨b,hb⟩ := align X hX hiX
  refine ⟨b⁻¹*a, ?_⟩
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    have hp : a • w ∈ X.map (toLinear b).toLinearMap := by
      rw [hb, ←ha]
      exact ⟨w,hw,rfl⟩
    obtain ⟨x,hx,hxe⟩ := hp
    change (b⁻¹*a) • w ∈ X
    change b • x = a • w at hxe
    rw [mul_smul, ←hxe, inv_smul_smul]
    exact hx
  · intro hv
    have hp : b • v ∈ W.map (toLinear a).toLinearMap := by
      rw [ha, ←hb]
      exact ⟨v,hv,rfl⟩
    obtain ⟨w,hw,hwe⟩ := hp
    refine ⟨w,hw,?_⟩
    change (b⁻¹*a) • w = v
    change a • w = b • v at hwe
    rw [mul_smul, hwe, inv_smul_smul]

/-- The original four-group is exactly the upper-root image in a faithful
field-natural SL₂(4), with its given plane and the complete action retained. -/
public theorem exists_marked_embedding
    (R : Subgroup (Sp Bit)) (W : Submodule Bit (Vector Bit))
    (hR : Nat.card R = 4) (hW : Module.finrank Bit W = 2)
    (hiW : ∀ x ∈ W, ∀ y ∈ W, form Bit x y = 0)
    (hfR : ∀ r ∈ R, r ≠ 1 → ∀ v : Vector Bit, r • v = v ↔ v ∈ W) :
    ∃ e : V ≃ₗ[Bit] Vector Bit, ∃ ι : SL →* Sp Bit,
      Function.Injective ι ∧
      (∀ g v, ι g • e v = e (action g v)) ∧
      U0.map ι = R ∧ upperFixed.map e.toLinearMap = W := by
  obtain ⟨e₀,ι₀,hι₀,he₀⟩ :=
    Theory.SpecificGroups.SymmetricSix.ExceptionalAlternatingFive.exists_marked_symplectic_embedding
  have mark (g : SL) (v : V) : ι₀ g • e₀ v = e₀ (action g v) := he₀ g v
  let W₀ : Submodule Bit (Vector Bit) := upperFixed.map e₀.toLinearMap
  have hd₀ : Module.finrank Bit W₀ = 2 :=
    (e₀.finrank_map_eq upperFixed).trans upperFixed_finrank
  have hiso₀ : ∀ x ∈ W₀, ∀ y ∈ W₀, form Bit x y = 0 := by
    rintro x ⟨u,hu,rfl⟩ y ⟨v,hv,rfl⟩
    have hu1 := (mem_upperFixed u).mp hu
    have hv1 := (mem_upperFixed v).mp hv
    let z : V := ![0,u 0]
    have hz : action (upper 1) z-z = u := by
      rw [upper_action]
      funext i
      fin_cases i <;> simp [z,hu1]
    have hvf : action (upper 1) v=v := (upper_fixed_iff v).mpr hv1 1
    have hp := preserves_form (ι₀ (upper 1)) (e₀ z) (e₀ v)
    rw [mark,mark,hvf] at hp
    rw [←hz,map_sub,map_sub,LinearMap.sub_apply]
    exact sub_eq_zero.mpr hp
  obtain ⟨g,hg⟩ := exists_plane_conjugator W₀ W hd₀ hW hiso₀ hiW
  let e' : V ≃ₗ[Bit] Vector Bit := e₀.trans (toLinear g)
  let ι' : SL →* Sp Bit := (MulAut.conj g).toMonoidHom.comp ι₀
  have hι' : Function.Injective ι' := (MulAut.conj g).injective.comp hι₀
  have hm (a : SL) (v : V) : ι' a • e' v = e' (action a v) := by
    change (g*ι₀ a*g⁻¹) • (g • e₀ v) = g • e₀ (action a v)
    simp only [mul_smul, inv_smul_smul, mark]
  have hplane : upperFixed.map e'.toLinearMap = W := by
    change upperFixed.map ((toLinear g).toLinearMap.comp e₀.toLinearMap) = W
    rw [Submodule.map_comp]
    exact hg
  refine ⟨e',ι',hι',hm,?_,hplane⟩
  apply eq_of_common_fixed_plane W hW hiW _ R ?_ hR ?_ hfR
  · rw [Subgroup.card_map_of_injective hι', Matrix.SpecialLinearGroup.card_upperUnipotent,
      Nat.card_eq_fintype_card, card_field]
  · rintro r ⟨a,ha,rfl⟩ hr v
    obtain ⟨b,rfl⟩ := (mem_U0 a).mp ha
    have hb : upper b ≠ 1 := by intro hh; simp [hh] at hr
    obtain ⟨w,rfl⟩ := e'.surjective v
    rw [hm,e'.injective.eq_iff,upper_nonidentity_fixed b hb]
    rw [←hplane]
    constructor
    · exact fun hw => ⟨w,hw,rfl⟩
    · rintro ⟨z,hz,hzw⟩
      exact e'.injective hzw ▸ hz

end Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive
