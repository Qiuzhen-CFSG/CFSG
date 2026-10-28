module
public import Theory.SpecificGroups.SymmetricEight.CentralPair
public import Theory.Alternating.proposition_5_2_4
public import Theory.Alternating.theorem_5_2_3

/-!
# Sylow centers in the double cover of A₈

In a finite quasisimple double cover of A₈, every Sylow-central element
maps to the identity. After Sylow conjugacy, the only possible nontrivial
image is the product z of four disjoint transpositions. A suitable double
transposition b in the same Sylow subgroup has z and zb conjugate. Centrality
would force a lift of b to have square one, contrary to the Schur-cover
calculation. Thus a normal subgroup of the Sylow disjoint from the covering
kernel is trivial, by the fixed-point theorem for two-groups.

The consumer is the literal image of U in L/V in original 12.2.25,
Aschbacher--Smith, printed p.805. The cover facts used here are GLS3,
Theorem 5.2.3 and Proposition 5.2.4; the binary-tree Sylow calculation is
in SymmetricEight.CentralPair.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Theory.SpecificGroups.SymmetricEight.DoubleSylow
open CentralPair A6ShadowTwoLocals GLS3.Chapter5.SchurPresentation
open RootFourSubgroup DoubleCoverUniqueness
universe u
variable {E : Type u} [Group E] [Finite E] [IsQuasisimple E]
local instance : IsQuasisimple A8 := alternatingGroup_isQuasisimple 3

private def b : A8 := ⟨treeGenerator 4, by change Equiv.Perm.sign (treeGenerator 4) = 1; decide +kernel⟩
private theorem b_mem : b ∈ (evenTreeSylow : Subgroup A8) := by
  rw [evenTreeSylow_coe]
  exact treeGenerator_mem 4
private theorem b_sq : b.val ^ 2 = 1 := by decide +kernel
private theorem z_sq : z.val ^ 2 = 1 := by decide +kernel
private theorem zb_sq : (z*b).val ^ 2 = 1 := by decide +kernel
private theorem z_ne : z ≠ 1 := by decide +kernel
private theorem z_zb_card : z.val.support.card = (z*b).val.support.card := by decide +kernel
private theorem root_b_card : (rho1 3).support.card = b.val.support.card := by decide +kernel
private theorem root_ne : (⟨rho1 3, rho1_mem_alternating 3⟩ : A8) ≠ 1 := by decide +kernel

private theorem root_lift (f : Covering E A8) (hk : Nat.card f.toMonoidHom.ker = 2) :
    ∃ x : E, f x = (⟨rho1 3, rho1_mem_alternating 3⟩ : A8) ∧ x^2 ≠ 1 := by
  obtain ⟨e, he, _⟩ := theorem_5_2_3_a_2 3 (schurAlternatingCovering 3) f
    (natCard_ker_schurAlternatingCovering 3) hk
  refine ⟨e (u1 3), ?_, ?_⟩
  · have hh := congrArg (fun c : Covering _ _ => c (u1 3)) he
    exact hh.trans (Subtype.ext (u1_proj 3))
  · rw [← map_pow, u1_sq]
    intro hh
    exact schurAlternatingCentral_ne_one 3 (e.injective (hh.trans e.map_one.symm))

private theorem b_lift_square (f : Covering E A8) (hk : Nat.card f.toMonoidHom.ker = 2)
    (y : E) (hy : f y = b) : y^2 ≠ 1 := by
  obtain ⟨x,hx,hx2⟩ := root_lift f hk
  have hc := alternating_involution_isConj_of_card_support_eq
    (sigma := (⟨rho1 3, rho1_mem_alternating 3⟩ : A8))
    (by simpa only [pow_two] using rho1_sq 3) b_sq root_ne root_b_card
  obtain ⟨c,hc⟩ := isConj_iff.mp hc
  have he := sq_eq_sq_of_conjugate_images f hk (x := x) (y := y) (c := c)
    (by rw [hx]; apply Subtype.ext; change rho1 3 ^ 2 = 1; simpa only [pow_two] using rho1_sq 3)
    (by rw [hx,hy]; exact hc)
  exact he ▸ hx2

theorem center_image_eq_one_of_map_eq (f : Covering E A8)
    (hk : Nat.card f.toMonoidHom.ker = 2) (P : Sylow 2 E)
    (hP : (P : Subgroup E).map f.toMonoidHom = (evenTreeSylow : Subgroup A8))
    (x : E) (hx : x ∈ P) (hxc : ∀ y ∈ (P : Subgroup E), x*y=y*x) : f x = 1 := by
  have hfx : f x ∈ (evenTreeSylow : Subgroup A8) := hP ▸ mem_map_of_mem _ hx
  have hfc : ∀ t ∈ (evenTreeSylow : Subgroup A8), f x * t = t * f x := by
    intro t ht
    rw [← hP] at ht
    obtain ⟨y,hy,rfl⟩ := ht
    exact (map_mul f.toMonoidHom x y).symm.trans
      ((congrArg f (hxc y hy)).trans (map_mul f.toMonoidHom y x))
  rcases evenTree_center (f x) hfx hfc with he | he
  · exact he
  · have hb : b ∈ (P : Subgroup E).map f.toMonoidHom := hP ▸ b_mem
    obtain ⟨y,hy,hfy⟩ := hb
    change f y = b at hfy
    have hy2 := b_lift_square f hk y hfy
    obtain ⟨c,hc⟩ := isConj_iff.mp
      (alternating_involution_isConj_of_card_support_eq z_sq zb_sq z_ne z_zb_card)
    have hsq := sq_eq_sq_of_conjugate_images f hk (x := x) (y := x*y) (c := c)
      (by rw [he]; exact Subtype.ext z_sq)
      (by change c * f x * c⁻¹ = f.toMonoidHom (x*y); rw [map_mul]; change c * f x * c⁻¹ = f x * f y; rw [he,hfy]; exact hc)
    have hcomm : Commute x y := hxc y hy
    rw [hcomm.mul_pow] at hsq
    have hcan : y^2 = 1 := mul_left_cancel (hsq.symm.trans (mul_one (x^2)).symm)
    exact False.elim (hy2 hcan)

theorem center_image_eq_one (f : Covering E A8)
    (hk : Nat.card f.toMonoidHom.ker = 2) (P : Sylow 2 E)
    (x : E) (hx : x ∈ P) (hxc : ∀ y ∈ (P : Subgroup E), x*y=y*x) : f x = 1 := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A8 (P.mapSurjective f.surjective) evenTreeSylow
  let a := MulAut.conj g
  let f' : Covering E A8 :=
    { toMonoidHom := a.toMonoidHom.comp f.toMonoidHom
      surjective := a.surjective.comp f.surjective }
  have hk' : f'.toMonoidHom.ker = f.toMonoidHom.ker :=
    MonoidHom.ker_comp_of_injective _ _ a.injective
  have hP' : (P : Subgroup E).map f'.toMonoidHom = (evenTreeSylow : Subgroup A8) := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Sylow.coe_mapSurjective]
    exact (Subgroup.map_map _ _ _).symm
  have hh := center_image_eq_one_of_map_eq f' (hk' ▸ hk) P hP' x hx hxc
  exact a.injective (hh.trans a.map_one.symm)

theorem normal_subgroup_eq_bot (f : Covering E A8)
    (hk : Nat.card f.toMonoidHom.ker = 2) (P : Sylow 2 E)
    (N : Subgroup P) [N.Normal]
    (hd : Disjoint (N.map (P : Subgroup E).subtype) f.toMonoidHom.ker) : N = ⊥ := by
  by_contra hN
  let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  have hn := P.isPGroup'.to_subgroup N
  have hdN : 2 ∣ Nat.card N := by
    obtain ⟨n,hn,he⟩ := hn.nontrivial_iff_card.mp inferInstance
    rw [he]
    exact dvd_pow_self 2 (by omega)
  have hc := P.isPGroup'.of_equiv ConjAct.toConjAct
  have hfix : (1 : N) ∈ MulAction.fixedPoints (ConjAct P) N := by
    intro g
    exact smul_one g
  obtain ⟨c,hcfix,hcne⟩ := hc.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hdN hfix
  have hcc : ∀ y ∈ (P : Subgroup E), (c : E)*y=y*(c : E) := by
    intro y hy
    have hh := congrArg (fun t : N => (t : E)) (hcfix (ConjAct.toConjAct (⟨y,hy⟩ : P)))
    change y * (c : E) * y⁻¹ = (c : E) at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hck : (c : E) ∈ f.toMonoidHom.ker := center_image_eq_one f hk P c c.val.property hcc
  have he : (c : E) = 1 := disjoint_def.mp hd (mem_map_of_mem _ c.property) hck
  exact hcne (Subtype.ext (Subtype.ext he.symm))
end Theory.SpecificGroups.SymmetricEight.DoubleSylow
