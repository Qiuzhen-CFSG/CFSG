module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.Decomposition
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.Involution
public import Theory.AtlasPort.LinearGroups.G2.Order

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.InvolutionConjugacy.ExplicitFusion

/-!
# Conjugacy of involution lines in the actual group G₂(3)

Every elementary subgroup of order two is conjugate to the line generated
by the displayed torus involution. The actual group order and the centralizer
order give centralizer index 7371, which is odd. Sylow conjugacy therefore
carries any two-subgroup into that centralizer. `ExplicitFusion` constructs
root/Weyl octonion automorphisms conjugating all its involutions to the marked
one. Composing the two conjugators proves the line statement.

This supplies the involution-line branch of maximal-two-local coverage. It
assumes neither coverage, quasithinness, even characteristic, nor conjugacy.
Application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Main Theorem 0.1.2(4), printed pp.3–4 and 481–482. The configuration in I.4,
p.417, is a recognition hypothesis and is not used as an exhaustive list.
The actual automorphisms and order calculation use the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.TernaryLocals.CharacterGeometry.InvolutionConjugacy
open Involution
private theorem centralizer_index : (localSubgroup false).index = 7371 := by
  have h := (localSubgroup false).card_mul_index
  have hG : Nat.card (Model (ZMod 3)) = 4245696 := by
    norm_num [card_Model, Nat.card_eq_fintype_card]
  rw [Involution.card, hG] at h
  omega

private theorem conjugate_into_centralizer (E : Subgroup G) (hE : IsPGroup 2 E) :
    ∃ a : G, E.map (MulAut.conj a).toMonoidHom ≤ localSubgroup false := by
  let T : Sylow 2 P := Classical.choice inferInstance
  let R : Subgroup G := (T : Subgroup P).map (localSubgroup false).subtype
  have hR : IsPGroup 2 R := T.isPGroup'.map (localSubgroup false).subtype
  have hi : ¬ 2 ∣ R.index := by
    rw [show R.index = (T : Subgroup P).index * (localSubgroup false).index from
      Subgroup.index_map_subtype _, centralizer_index]
    exact Nat.prime_two.not_dvd_mul T.not_dvd_index (by decide)
  let S : Sylow 2 G := hR.toSylow hi
  obtain ⟨Q, hEQ⟩ := hE.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G Q S
  refine ⟨a, ?_⟩
  have hm : E.map (MulAut.conj a).toMonoidHom ≤ (S : Subgroup G) := by
    rw [← ha]
    exact Subgroup.map_mono hEQ
  exact hm.trans (Subgroup.map_subtype_le _)

/-- Every elementary involution line in the actual ternary octonion
model is a conjugate of the displayed torus involution line. -/
theorem elementary_card_two_conjugate (E : Subgroup G)
    (hEA : IsElementaryAbelian 2 E) (hE : Nat.card E = 2) :
    ∃ g : G, E = (Subgroup.zpowers involution).map (MulAut.conj g).toMonoidHom := by
  let _ := hEA
  have hc : IsCyclic E := isCyclic_of_prime_card hE
  obtain ⟨x, hx⟩ := E.isCyclic_iff_exists_zpowers_eq_top.mp hc
  have hxmem : x ∈ E := hx ▸ Subgroup.mem_zpowers x
  have hxn : x ≠ 1 := by
    intro hn
    have he : E = ⊥ := by simpa [hn] using hx.symm
    rw [he, Subgroup.card_bot] at hE
    omega
  have hxsq : x ^ 2 = 1 := by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) (⟨x,hxmem⟩ : E)
    exact congrArg Subtype.val h
  obtain ⟨a, ha⟩ := conjugate_into_centralizer E (IsElementaryAbelian.isPGroup 2 E)
  let y : P := ⟨(MulAut.conj a) x, ha (Subgroup.mem_map.mpr ⟨x,hxmem,rfl⟩)⟩
  have hysq : y^2 = 1 := by
    apply Subtype.ext
    change (MulAut.conj a) x ^ 2 = 1
    rw [← map_pow, hxsq, map_one]
  have hyn : y ≠ 1 := by
    intro hn
    apply hxn
    apply (MulAut.conj a).injective
    exact (congrArg Subtype.val hn).trans (map_one _).symm
  obtain ⟨b, hb⟩ := centralizer_involution_conjugate y hysq hyn
  refine ⟨a⁻¹*b, ?_⟩
  rw [MonoidHom.map_zpowers, ← hx]
  congr 1
  change x = (a⁻¹*b) * involution * (a⁻¹*b)⁻¹
  have he : a*x*a⁻¹ = b*involution*b⁻¹ := hb
  calc
    x = a⁻¹ * (a*x*a⁻¹) * a := by group
    _ = a⁻¹ * (b*involution*b⁻¹) * a := by rw [he]
    _ = _ := by group
end Atlas.G2.TernaryLocals.CharacterGeometry.InvolutionConjugacy
