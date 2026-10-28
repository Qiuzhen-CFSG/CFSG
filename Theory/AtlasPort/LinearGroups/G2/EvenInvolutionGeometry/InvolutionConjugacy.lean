module

public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.RootElements
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Core
public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts
public import Mathlib.Algebra.CharP.Reduced

/-!
# Involution conjugacy in finite even G₂

Every nonidentity involution of the actual split-octonion model is conjugate
to a nonzero A-root or C-root element. The proof works uniformly over finite
fields of characteristic two, including the full group G₂(2).

First place the involution in the six-root Sylow subgroup. For coordinates
`(a,b,c,d,e,f)`, its square gives `e*f = 0`. If `f ≠ 0`, it also gives
`c = d*f`; conjugation by E(d/f), followed by the long Weyl reflection,
makes the sixth coordinate zero. In that five-root subgroup, the square
condition is `b*e + c*d = 0`. When `e ≠ 0`, choose `z² = c/e` and conjugate
by F(z); the C and B coordinates vanish, and the short Weyl reflection gives
an A–B–C product. The cases `e = 0` reduce to the same form. A nonzero C
coordinate absorbs A and B by explicit D- and F-root conjugations; otherwise
the existing long-root-plane calculation applies.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, the G₂ element clause of 16.1.4(1), printed p.1171,
and its uses in 16.5.13–14, printed pp.1201–1203. The collection and Weyl laws
come from the ATLAS port by Gerald Höhn and the ATLAS contributors; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. The exhaustive coordinate
reduction is proved here from those laws.
-/

public section

open Atlas.G2 Atlas.G2.LieParabolicSetup
namespace Atlas.G2.EvenInvolutionGeometry
variable {F : Type*} [Field F] [CharP F 2]

private theorem square_parameters (t : Fin 6 → F) :
    unipotentProductParameters t t =
      ![t 1*t 4 + t 2*t 3 + t 2*t 4*t 5 + (t 3)^2*t 5 + t 3*t 4*(t 5)^2,
        t 2*t 5 + t 3*(t 5)^2 + t 4*(t 5)^3,
        t 4*(t 5)^2, t 4*t 5, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [unipotentProductParameters, CharTwo.sub_eq_add, CharTwo.ofNat_eq_mod]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]

private theorem conjugate_E (a b c d e f z : F) :
    MulAut.conj (rootE z) (unipotentProduct ![a,b,c,d,e,f]) =
      unipotentProduct ![a+b*z+d*f^2*z+e*f^3*z,
        b+f^3*z,c+f^2*z,d+f*z,e,f] := by
  have hi : (rootE z)⁻¹ = rootE z := by
    apply inv_eq_of_mul_eq_one_left
    rw [rootE_add, CharTwo.add_self_eq_zero, rootE_zero]
  rw [MulAut.conj_apply, hi]
  have he : rootE z = unipotentProduct ![0,0,0,0,z,0] := by simp [unipotentProduct]
  rw [he, unipotentProduct_mul, unipotentProduct_mul]
  congr 1
  funext i
  fin_cases i <;>
    simp [unipotentProductParameters, CharTwo.sub_eq_add, CharTwo.ofNat_eq_mod]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]

private theorem conjugate_F (a b c d e f z : F) :
    MulAut.conj (rootF z) (unipotentProduct ![a,b,c,d,e,f]) =
      unipotentProduct ![a+d^2*z+d*e*z^2+e^2*z^3,
        b+c*z+d*z^2+e*z^3,c+e*z^2,d+e*z,e,f] := by
  have hi : (rootF z)⁻¹ = rootF z := by
    apply inv_eq_of_mul_eq_one_left
    rw [rootF_add, CharTwo.add_self_eq_zero, rootF_zero]
  rw [MulAut.conj_apply, hi]
  have hf : rootF z = unipotentProduct ![0,0,0,0,0,z] := by simp [unipotentProduct]
  rw [hf, unipotentProduct_mul, unipotentProduct_mul]
  congr 1
  funext i
  fin_cases i <;>
    simp [unipotentProductParameters, CharTwo.sub_eq_add, CharTwo.ofNat_eq_mod]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]

private theorem conjugate_D (a b c z : F) :
    MulAut.conj (rootD z) (unipotentProduct ![a,b,c,0,0,0]) =
      unipotentProduct ![a+c*z,b,c,0,0,0] := by
  have hi : (rootD z)⁻¹ = rootD z := by
    apply inv_eq_of_mul_eq_one_left
    rw [rootD_add, CharTwo.add_self_eq_zero, rootD_zero]
  rw [MulAut.conj_apply, hi]
  have hd : rootD z = unipotentProduct ![0,0,0,z,0,0] := by simp [unipotentProduct]
  rw [hd, unipotentProduct_mul, unipotentProduct_mul]
  congr 1
  funext i
  fin_cases i <;>
    simp [unipotentProductParameters, CharTwo.sub_eq_add, CharTwo.ofNat_eq_mod]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]


omit [CharP F 2] in
private theorem square_zero (t : Fin 6 → F) (h : (unipotentProduct t)^2 = 1) :
    unipotentProductParameters t t = 0 := by
  apply unipotentProduct_injective
  rw [← unipotentProduct_mul, ← pow_two, h, unipotentProduct_zero]

private theorem five_relation (a b c d e : F)
    (h : (unipotentProduct ![a,b,c,d,e,0])^2 = 1) : b*e+c*d=0 := by
  have hh := congrFun (square_zero _ h) 0
  simpa [square_parameters] using hh

omit [CharP F 2] in
private theorem root_conj (g : Model F) {x : Model F} (h : IsRootElement x) :
    IsRootElement (MulAut.conj g x) := by
  rcases h with ⟨k,a,ha,rfl⟩ | ⟨k,a,ha,rfl⟩
  · exact Or.inl ⟨g*k,a,ha,by rw [map_mul, MulAut.mul_apply]⟩
  · exact Or.inr ⟨g*k,a,ha,by rw [map_mul, MulAut.mul_apply]⟩

omit [CharP F 2] in
private theorem root_of_conj (g : Model F) {x : Model F}
    (h : IsRootElement (MulAut.conj g x)) : IsRootElement x := by
  have hh := root_conj g⁻¹ h
  simpa [MulAut.conj_apply, mul_assoc] using hh

-- The A–B–C subgroup is the final normal form.
private theorem ABC_isRoot (a b c : F)
    (hne : unipotentProduct ![a,b,c,0,0,0] ≠ 1) :
    IsRootElement (unipotentProduct ![a,b,c,0,0,0]) := by
  by_cases hc : c = 0
  · have hm : unipotentProduct ![a,b,c,0,0,0] ∈ longRootLocal := by
      exact ⟨Multiplicative.ofAdd (a,b), by simp [longRootHom, unipotentProduct, hc]⟩
    obtain ⟨z,hz,g,hg⟩ := ShortRootProducts.longRootLocal_isLong hm hne
    exact Or.inl ⟨g,z,hz,hg⟩
  · right
    refine ⟨rootF (b/c) * rootD (a/c), c, hc, ?_⟩
    rw [map_mul, MulAut.mul_apply]
    have hC : rootC c = unipotentProduct ![0,0,c,0,0,0] := by simp [unipotentProduct]
    rw [hC, conjugate_D, conjugate_F]
    simp [mul_div_cancel₀ _ hc]

-- Finite characteristic-two fields supply the one square root used in the proof.
private theorem nonzero_E_isRoot [Finite F] (a b c d e : F) (he : e ≠ 0)
    (hsq : (unipotentProduct ![a,b,c,d,e,0])^2 = 1)
    (hne : unipotentProduct ![a,b,c,d,e,0] ≠ 1) :
    IsRootElement (unipotentProduct ![a,b,c,d,e,0]) := by
  obtain ⟨z,hz⟩ := isSquare_of_charTwo' (c/e)
  have hz' : e*z^2 = c := by
    rw [pow_two, ← hz, mul_div_cancel₀ _ he]
  let a' := a+d^2*z+d*e*z^2+e^2*z^3
  let b' := b+c*z+d*z^2+e*z^3
  let d' := d+e*z
  have hconj : MulAut.conj (rootF z) (unipotentProduct ![a,b,c,d,e,0]) =
      unipotentProduct ![a',b',0,d',e,0] := by
    rw [conjugate_F, hz', CharTwo.add_self_eq_zero]
  have hsq' : (unipotentProduct ![a',b',0,d',e,0])^2 = 1 := by
    rw [← hconj, ← map_pow, hsq, map_one]
  have hb : b'=0 := by
    have hh := five_relation a' b' 0 d' e hsq'
    simpa using (mul_eq_zero.mp (by simpa using hh : b'*e=0)).resolve_right he
  have hw : MulAut.conj weylS (unipotentProduct ![a',b',0,d',e,0]) =
      unipotentProduct ![a',e,d',0,0,0] := by
    change weylS * _ * weylS⁻¹ = _
    rw [weylS_fiveRoot_conjugate _ rfl]
    simp [hb]
  apply root_of_conj (rootF z)
  rw [hconj]
  apply root_of_conj weylS
  rw [hw]
  apply ABC_isRoot
  intro hh
  apply hne
  apply (MulAut.conj (rootF z)).injective
  apply (MulAut.conj weylS).injective
  simpa only [hconj, hw, map_one] using hh

private theorem five_isRoot [Finite F] (a b c d e : F)
    (hsq : (unipotentProduct ![a,b,c,d,e,0])^2 = 1)
    (hne : unipotentProduct ![a,b,c,d,e,0] ≠ 1) :
    IsRootElement (unipotentProduct ![a,b,c,d,e,0]) := by
  by_cases he : e = 0
  · subst e
    have hcd : c*d = 0 := by simpa using five_relation a b c d 0 hsq
    rcases mul_eq_zero.mp hcd with hc | hd
    · subst c
      have hw : MulAut.conj weylS (unipotentProduct ![a,b,0,d,0,0]) =
          unipotentProduct ![a,0,d,0,b,0] := by
        change weylS * _ * weylS⁻¹ = _
        rw [weylS_fiveRoot_conjugate _ rfl]
        simp
      have hsq' : (unipotentProduct ![a,0,d,0,b,0])^2 = 1 := by
        rw [← hw, ← map_pow, hsq, map_one]
      have hne' : unipotentProduct ![a,0,d,0,b,0] ≠ 1 := by
        rw [← hw, MulEquiv.map_ne_one_iff]
        exact hne
      apply root_of_conj weylS
      rw [hw]
      by_cases hb : b=0
      · subst b
        exact ABC_isRoot a 0 d hne'
      · exact nonzero_E_isRoot a 0 d 0 b hb hsq' hne'
    · subst d
      exact ABC_isRoot a b c hne
  · exact nonzero_E_isRoot a b c d e he hsq hne


omit [CharP F 2] in
private theorem conjugate_R_ABF (a b f : F) :
    MulAut.conj weylR (unipotentProduct ![a,b,0,0,0,f]) =
      unipotentProduct ![b,a,0,f,0,0] := by
  have hRF : MulAut.conj weylR (rootF f) = rootD f := by
    have hh : MulAut.conj weylR (MulAut.conj weylR (rootD f)) = rootD f := by
      rw [← MulAut.mul_apply, ← map_mul, ← pow_two, weylR_sq]
      simp
    rwa [show MulAut.conj weylR (rootD f) = rootF f from weylR_rootD f] at hh
  simp only [unipotentProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, rootC_zero, rootD_zero, rootE_zero,
    rootF_zero, mul_one]
  rw [map_mul, show MulAut.conj weylR (rootA a * rootB b) = rootA b * rootB a from
    weylR_conjugate_longRoot a b, hRF]

-- The sixth-coordinate case reduces to the five-root calculation.
private theorem unipotent_isRoot [Finite F] (t : Fin 6 → F)
    (hsq : (unipotentProduct t)^2 = 1) (hne : unipotentProduct t ≠ 1) :
    IsRootElement (unipotentProduct t) := by
  have ht : t = ![t 0,t 1,t 2,t 3,t 4,t 5] := by ext i; fin_cases i <;> rfl
  by_cases hf : t 5 = 0
  · rw [ht] at hsq hne ⊢
    simp only [hf] at hsq hne ⊢
    exact five_isRoot _ _ _ _ _ hsq hne
  have hs := square_zero t hsq
  have hef : t 4 * t 5 = 0 := by simpa [square_parameters] using congrFun hs 3
  have he : t 4 = 0 := (mul_eq_zero.mp hef).resolve_right hf
  have hcf : (t 2 + t 3*t 5)*t 5 = 0 := by
    have hh := congrFun hs 1
    simp only [square_parameters, Matrix.cons_val_one, Matrix.cons_val_zero,
      Pi.zero_apply, he, zero_mul, add_zero] at hh
    linear_combination hh
  have hc : t 2 = t 3*t 5 := by
    have hh := (mul_eq_zero.mp hcf).resolve_right hf
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh
  have hd : t 5 * (t 3 / t 5) = t 3 := by field_simp
  have hcc : (t 5)^2 * (t 3/t 5) = t 3*t 5 := by
    rw [pow_two, mul_assoc, hd, mul_comm]
  let a := t 0 + t 1*(t 3/t 5) + t 3*(t 5)^2*(t 3/t 5)
  let b := t 1 + (t 5)^3*(t 3/t 5)
  have hE : MulAut.conj (rootE (t 3/t 5)) (unipotentProduct t) =
      unipotentProduct ![a,b,0,0,0,t 5] := by
    rw [show unipotentProduct t = unipotentProduct ![t 0,t 1,t 2,t 3,t 4,t 5] from
      congrArg unipotentProduct ht, conjugate_E]
    simp only [he, zero_mul, add_zero, hd, hcc, hc, CharTwo.add_self_eq_zero]
    rfl
  have hR := conjugate_R_ABF a b (t 5)
  have hsq' : (unipotentProduct ![b,a,0,t 5,0,0])^2 = 1 := by
    rw [← hR, ← hE, ← map_pow, ← map_pow, hsq, map_one, map_one]
  have hne' : unipotentProduct ![b,a,0,t 5,0,0] ≠ 1 := by
    rw [← hR, ← hE, MulEquiv.map_ne_one_iff, MulEquiv.map_ne_one_iff]
    exact hne
  apply root_of_conj (rootE (t 3/t 5))
  rw [hE]
  apply root_of_conj weylR
  rw [hR]
  exact five_isRoot _ _ _ _ _ hsq' hne'

/-- Every nonidentity involution in the actual positive-root Sylow subgroup
is conjugate to an A-root or C-root element. -/
theorem unipotent_involution_isRoot [Finite F] {x : Model F} (hx : x ∈ unipotent)
    (hsq : x^2 = 1) (hne : x ≠ 1) : IsRootElement x := by
  rw [unipotent_eq_range] at hx
  obtain ⟨t,rfl⟩ := hx
  exact unipotent_isRoot t hsq hne

/-- All involutions of the full finite even G₂ model are root elements,
including those outside the derived subgroup of G₂(2). -/
theorem involution_isRoot [Finite F] {x : Model F} (hsq : x^2 = 1) (hne : x ≠ 1) :
    IsRootElement x := by
  have hp : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, orderOf_eq_prime hsq hne, pow_one])
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hx : x ∈ S := hS (Subgroup.mem_zpowers x)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model F) (sylow (F := F)) S
  have hm : unipotent.map (MulAut.conj g).toMonoidHom = (S : Subgroup (Model F)) :=
    congrArg Sylow.toSubgroup hg
  have hx' : x ∈ unipotent.map (MulAut.conj g).toMonoidHom := hm.symm ▸ hx
  obtain ⟨y,hy,rfl⟩ := hx'
  apply root_conj g
  apply unipotent_involution_isRoot hy
  · apply (MulAut.conj g).injective
    simpa only [MulEquiv.coe_toMonoidHom, map_pow, map_one] using hsq
  · intro hy1
    apply hne
    simp [hy1]

end Atlas.G2.EvenInvolutionGeometry
