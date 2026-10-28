module

public import Theory.SpecificGroups.PSL3.SmallCompletion.ReflectionPairAlignment
public import Theory.SpecificGroups.PSL3.CartanActions.ThreeAlignment

/-!
# Marking an actual cubic-inverting parabolic pair

An actual cubic in the common Borel is conjugated to the full split torus.
Its two exterior inverters then lie in the two prescribed torus-normalizer
cosets. The simultaneous diagonal correction aligns the literal pair while
preserving both full parabolics and their common Borel.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The original two exterior cubic inverters admit a single compatible
standard marking. No order or recognition premise on their product is used. -/
theorem exists_cubic_reflection_pair_marking (hF : Nat.card F=4)
    (t r s : PSL(3,F)) (ht : t∈borel F) (ht3 : orderOf t=3)
    (hr : r∈pointParabolic F) (hs : s∈lineParabolic F)
    (hrout : r∉borel F) (hsout : s∉borel F)
    (hrt : r*t*r⁻¹=t⁻¹) (hst : s*t*s⁻¹=t⁻¹) :
    ∃ a : MulAut PSL(3,F), a r=reflection F false ∧ a s=reflection F true ∧
      (pointParabolic F).map a.toMonoidHom=pointParabolic F ∧
      (lineParabolic F).map a.toMonoidHom=lineParabolic F ∧
      (borel F).map a.toMonoidHom=borel F := by
  have hp : IsPGroup 3 (zpowers t) :=
    IsPGroup.of_card (n:=1) (by rw [Nat.card_zpowers,ht3,pow_one])
  obtain ⟨b,hb,hbt⟩ := ThreeAlignment.conjugate_borel_threeSubgroup_into_torus F
    (f:=2) (by simpa using hF) (zpowers t) hp (zpowers_le.mpr ht)
  let a₀ := MulAut.conj b
  have hbP : b∈pointParabolic F := by
    rw [pointParabolic_eq_sup]
    exact mem_sup_right hb
  have hbQ : b∈lineParabolic F := by
    rw [lineParabolic_eq_sup]
    exact mem_sup_right hb
  have hP : (pointParabolic F).map a₀.toMonoidHom=pointParabolic F :=
    mem_normalizer_iff_map_conj_eq.mp ((pointParabolic F).le_normalizer hbP)
  have hQ : (lineParabolic F).map a₀.toMonoidHom=lineParabolic F :=
    mem_normalizer_iff_map_conj_eq.mp ((lineParabolic F).le_normalizer hbQ)
  have hB : (borel F).map a₀.toMonoidHom=borel F :=
    mem_normalizer_iff_map_conj_eq.mp ((borel F).le_normalizer hb)
  have hT : (zpowers t).map a₀.toMonoidHom=torus F := by
    apply eq_of_le_of_card_ge hbt
    rw [card_map_of_injective a₀.injective,Nat.card_zpowers,ht3]
    have hc := BorelQuotient.card_torus_mul_scalar F
    rw [hF] at hc
    norm_num at hc
    omega
  have hnormal (x : PSL(3,F)) (hx : x*t*x⁻¹=t⁻¹) :
      a₀ x∈normalizer (torus F:Set PSL(3,F)) := by
    have hn : x∈normalizer (zpowers t:Set PSL(3,F)) := by
      rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
      change zpowers (x*t*x⁻¹)=zpowers t
      rw [hx,zpowers_inv]
    have hm := mem_map_of_mem a₀.toMonoidHom hn
    rwa [map_equiv_normalizer_eq,hT] at hm
  have hmem (H : Subgroup PSL(3,F)) (he : H.map a₀.toMonoidHom=H)
      (x : PSL(3,F)) : a₀ x∈H ↔ x∈H := by
    have hh : a₀ x∈H.map a₀.toMonoidHom ↔ x∈H :=
      mem_map_iff_mem (f:=a₀.toMonoidHom) a₀.injective
    rwa [he] at hh
  obtain ⟨d,hd⟩ := normalizer_eq_torus_mul_reflection F (by omega) false (a₀ r)
    ((hmem _ hP r).mpr hr) (hnormal r hrt) (fun he => hrout ((hmem _ hB r).mp he))
  obtain ⟨e,he⟩ := normalizer_eq_torus_mul_reflection F (by omega) true (a₀ s)
    ((hmem _ hQ s).mpr hs) (hnormal s hst) (fun he => hsout ((hmem _ hB s).mp he))
  obtain ⟨a₁,ha₁,ha₂,hP₁,hQ₁,hB₁⟩ := exists_diagonal_reflection_pair_alignment F hF d e
  refine ⟨a₀.trans a₁,?_,?_,?_,?_,?_⟩
  · change a₁ (a₀ r)=_
    rw [hd,ha₁]
  · change a₁ (a₀ s)=_
    rw [he,ha₂]
  · change (pointParabolic F).map (a₁.toMonoidHom.comp a₀.toMonoidHom)=_
    rw [←Subgroup.map_map,hP,hP₁]
  · change (lineParabolic F).map (a₁.toMonoidHom.comp a₀.toMonoidHom)=_
    rw [←Subgroup.map_map,hQ,hQ₁]
  · change (borel F).map (a₁.toMonoidHom.comp a₀.toMonoidHom)=_
    rw [←Subgroup.map_map,hB,hB₁]

end Matrix.PSL3.SmallCompletion
