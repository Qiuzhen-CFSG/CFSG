module
public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionDichotomy.FixedPlane
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Kernel
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut

/-!
# Inversion of cubic square actions by a both-outer quaternion involution

An automorphism whose cube is trivial on the central quotient preserves both
intrinsic quaternion factors: its cube is inner, while its square preserves
the factors. Each factor has a Klein-four image in the square quotient.
A both-outer involution acts nontrivially on both planes. Their automorphism
groups are the symmetric group on their three nonidentity elements, where
every involution inverts every element of order dividing three. The two
planes generate the actual central quotient, proving inversion on it.

This proves inversion of the entire elementary cubic image in the c₂ branch
without assuming that inversion as an input. Only the six-element permutation
calculation is finite; the factor embeddings and quotient maps remain literal.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 14.4.4, printed p.1007.
-/

open Subgroup
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

private theorem perm_three_inverts : ∀ a b : Equiv.Perm (Fin 3),
    a^2=1 → a≠1 → b^3=1 → a*b=b⁻¹*a := by decide +kernel

private theorem klein_inverts {E : Type*} [Group E] [IsKleinFour E]
    (a b : MulAut E) (ha : a^2=1) (hne : a≠1) (hb : b^3=1) : a*b=b⁻¹*a := by
  let e := IsKleinFour.autEquivPermThree E
  apply e.injective
  simpa only [map_mul,map_inv] using perm_three_inverts (e a) (e b)
    (by rw [← map_pow,ha,map_one])
    (fun h => hne (e.injective (h.trans e.map_one.symm)))
    (by rw [← map_pow,hb,map_one])

omit [Finite Q] in
private theorem factor_normal (B C : Subgroup Q)
    (hc : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) (hs : B ⊔ C = ⊤) : B.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hs]
  exact sup_le B.le_normalizer ((show C ≤ centralizer (B : Set Q) from
    fun c hc' b hb => hc b hb c hc').trans (centralizer_le_normalizer _))

private theorem cube_trivial_preserves (b : MulAut Q)
    (hb : (quotientAut (center Q) b)^3=1) :
    d.left.map b.toMonoidHom = d.left ∧ d.right.map b.toMonoidHom = d.right := by
  have hinner : ∃ q : Q, MulAut.conj q = b^3 := by
    apply (d.quotientAut_eq_one_iff_inner (b^3)).mp
    rwa [map_pow]
  obtain ⟨q,hq⟩ := hinner
  have hsquare := quaternion_factors_invariant_of_square d.left d.right d.left_model
    d.right_model d.intersection_card d.commute b (by rw [d.span]; exact map_top_of_surjective _ b.surjective)
  have hcube (B C : Subgroup Q) (hc : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
      (hs : B ⊔ C = ⊤) : B.map (b^3).toMonoidHom = B := by
    rw [← hq]
    let := factor_normal B C hc hs
    exact Normal.map_conj_eq B q
  have calcmap (B : Subgroup Q) (hB : (B.map b.toMonoidHom).map b.toMonoidHom = B)
      (hB3 : B.map (b^3).toMonoidHom = B) : B.map b.toMonoidHom = B := by
    have hm : (b^3).toMonoidHom = b.toMonoidHom.comp (b.toMonoidHom.comp b.toMonoidHom) := by
      ext x
      rfl
    have hc : B.map (b^3).toMonoidHom = B.map b.toMonoidHom := by
      rw [hm, ← map_map, ← map_map, hB]
    exact hc.symm.trans hB3
  constructor
  · exact calcmap d.left hsquare.1 (hcube d.left d.right d.commute d.span)
  · exact calcmap d.right hsquare.2 (hcube d.right d.left (fun c hc b hb => (d.commute b hb c hc).symm)
      (by rw [sup_comm]; exact d.span))


include d in
private theorem factor_image_card (B : Subgroup Q) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hz : center Q ≤ B) : Nat.card (B.map (QuotientGroup.mk' (center Q))) = 4 := by
  have hcB : Nat.card B = 8 := by
    rw [Nat.card_congr hB.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hiB : B.index = 4 := by
    have h := B.card_mul_index
    rw [hcB,d.card] at h
    omega
  have hi := B.index_map_eq (QuotientGroup.mk'_surjective (center Q))
    (show (QuotientGroup.mk' (center Q)).ker ≤ B by rwa [QuotientGroup.ker_mk'])
  have hh := (B.map (QuotientGroup.mk' (center Q))).card_mul_index
  rw [hi,hiB,d.quotient_card] at hh
  omega

omit [Finite Q] in
private theorem quotient_preserves (B : Subgroup Q) (a : MulAut Q)
    (ha : B.map a.toMonoidHom = B) :
    (B.map (QuotientGroup.mk' (center Q))).map (quotientAut (center Q) a).toMonoidHom =
      B.map (QuotientGroup.mk' (center Q)) := by
  rw [map_map]
  have he : (quotientAut (center Q) a).toMonoidHom.comp (QuotientGroup.mk' (center Q)) =
      (QuotientGroup.mk' (center Q)).comp a.toMonoidHom := by
    ext x
    exact quotientAut_apply_mk (center Q) a x
  rw [he, ← map_map, ha]

include d in
private theorem inverts_on_factor (B : Subgroup Q)
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hz : center Q ≤ B)
    (a b : MulAut Q) (ha : a^2=1)
    (haB : B.map a.toMonoidHom = B) (hbB : B.map b.toMonoidHom = B)
    (ho : ¬ ∃ z : B, ∀ x : B, a (x : Q) = (z : Q)*x*(z : Q)⁻¹)
    (hb : (quotientAut (center Q) b)^3=1) :
    ∀ v ∈ B.map (QuotientGroup.mk' (center Q)),
      quotientAut (center Q) a (quotientAut (center Q) b v) =
        (quotientAut (center Q) b)⁻¹ (quotientAut (center Q) a v) := by
  let π := QuotientGroup.mk' (center Q)
  let E := B.map π
  let α := quotientAut (center Q) a
  let β := quotientAut (center Q) b
  let f : MulAut E := (α.subgroupMap E).trans (MulEquiv.subgroupCongr (quotient_preserves B a haB))
  let g : MulAut E := (β.subgroupMap E).trans (MulEquiv.subgroupCongr (quotient_preserves B b hbB))
  have hf (x : E) : (f x : Q ⧸ center Q) = α x := rfl
  have hg (x : E) : (g x : Q ⧸ center Q) = β x := rfl
  have hgi (x : E) : (g⁻¹ x : Q ⧸ center Q) = β⁻¹ x := by
    apply β.injective
    rw [← hg, MulAut.apply_inv_self, MulAut.apply_inv_self]
  have hc : Nat.card E = 4 := factor_image_card d B hB hz
  let _ := d.quotient_elementary
  let _ : IsElementaryAbelian 2 E := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (Q ⧸ center Q)) x)) }
  let _ : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsKleinFour E := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
  have hf2 : f^2=1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change α (α x) = x
    have hα : α^2=1 := by dsimp [α]; rw [← map_pow,ha,map_one]
    simpa only [pow_two,MulAut.mul_apply,MulAut.one_apply] using DFunLike.congr_fun hα (x : Q ⧸ center Q)
  have hg3 : g^3=1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change β (β (β x)) = x
    simpa only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply] using DFunLike.congr_fun hb (x : Q ⧸ center Q)
  have hfn : f ≠ 1 := by
    intro he
    let aB : MulAut B := (a.subgroupMap B).trans (MulEquiv.subgroupCongr haB)
    have hdiff (x : B) : x⁻¹*aB x ∈ center B := by
      have hh := congrArg Subtype.val (DFunLike.congr_fun he
        (⟨π x,mem_map_of_mem π x.property⟩ : E))
      change α (π x) = π x at hh
      rw [quotientAut_apply_mk] at hh
      have hz' : (x : Q)⁻¹*a x ∈ center Q := QuotientGroup.eq.mp hh.symm
      exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hz' y))
    obtain ⟨z,hz'⟩ := QuaternionGroup.exists_conj_of_central_difference_of_equiv hB.some aB hdiff
    exact ho ⟨z, fun x => congrArg Subtype.val (DFunLike.congr_fun hz' x)⟩
  have hh := klein_inverts f g hf2 hfn hg3
  intro v hv
  have hv' := congrArg Subtype.val (DFunLike.congr_fun hh (⟨v,hv⟩ : E))
  simpa only [MulAut.mul_apply,hf,hg,hgi] using hv'

/-- A both-outer involution inverts every cubic element of the actual square action. -/
public theorem BothOuter.inverts_cubic {a : MulAut Q} (h : d.BothOuter a)
    (ha : a^2=1) (b : MulAut Q) (hb : (quotientAut (center Q) b)^3=1) :
    quotientAut (center Q) (a*b*a⁻¹) = (quotientAut (center Q) b)⁻¹ := by
  have hpres := cube_trivial_preserves d b hb
  have he : quotientAut (center Q) a * quotientAut (center Q) b =
      (quotientAut (center Q) b)⁻¹ * quotientAut (center Q) a := by
    let π := QuotientGroup.mk' (center Q)
    have hj : d.left.map π ⊔ d.right.map π = ⊤ := by
      rw [← map_sup,d.span,map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
    have hl := inverts_on_factor d d.left d.left_model (d.center_eq ▸ inf_le_left)
      a b ha h.left_map hpres.1 h.left_outer hb
    have hr := inverts_on_factor d d.right d.right_model (d.center_eq ▸ inf_le_right)
      a b ha h.right_map hpres.2 h.right_outer hb
    let F := (quotientAut (center Q) a * quotientAut (center Q) b).toMonoidHom.eqLocus
      ((quotientAut (center Q) b)⁻¹ * quotientAut (center Q) a).toMonoidHom
    have ht : ⊤ ≤ F := hj ▸ sup_le hl hr
    ext v
    exact ht (mem_top v)
  rw [map_mul,map_mul,map_inv,he,mul_inv_cancel_right]
end Subgroup.QuaternionCentralProductData
