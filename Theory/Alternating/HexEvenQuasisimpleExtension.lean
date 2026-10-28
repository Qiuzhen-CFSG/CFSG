module

public import Theory.Alternating.HexEvenQuasisimpleExtension.Action
public import Theory.Alternating.TripleSixActorInversion

/-!
# Hatted symmetric-six extensions of the actual HexEven group

For a normal HexEven subgroup equal to F*(G), with two-group quotient and
Sylow C₂ × D₈, the original central quotient action gives G/Z(HexEven) ≃ S₆.
Its kernel is the embedded cubic component center, and the component is
exactly G'. The chosen outer involution inverts that center; index two then
proves inversion for every element of odd sign in the literal quotient.

No ambient isomorphism or prescribed automorphism image is assumed. The
Sylow and exceptional-A₆ calculations in the descendants construct the
natural image from the actual source hypotheses.

Source: GLS3 5.2.7; Aschbacher–Smith F.6.18(8), printed p.310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Equiv Atlas.Codes
namespace Theory.HexEvenExtension
variable {G : Type*} [Group G] [Finite G]

private theorem center_map_equiv {A B : Type*} [Group A] [Group B] (j : A ≃* B) :
    (center A).map j.toMonoidHom = center B := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (centerCongr j ⟨a, ha⟩).property
  · intro hb
    exact ⟨j.symm b, (centerCongr j.symm ⟨b, hb⟩).property, j.apply_symm_apply b⟩

/-- The actual HexEven model gives the marked central quotient. -/
def centralEquiv {L : Type*} [Group L] (j : L ≃* HexEvenAutomorphisms) :
    L ⧸ center L ≃* alternatingGroup (Fin 6) :=
  (QuotientGroup.congr _ _ j (center_map_equiv j)).trans
    Representation.Hexacode.even_quotient_center_equiv

/-- Center inversion transports along an actual HexEven marking. -/
lemma center_inverted_of_hex_model
    {L : Type*} [Group L] (j : L ≃* HexEvenAutomorphisms) (x : MulAut L)
    (hx : x ^ 2 = 1) (hout : ∀ k : L, x ≠ MulAut.conj k) :
    ∀ z : L, z ∈ center L → x z = z⁻¹ := by
  let y : MulAut HexEvenAutomorphisms := MulAut.congr j x
  have hy2 : y ^ 2 = 1 := by
    change (MulAut.congr j) x ^ 2 = 1
    rw [← map_pow, hx, map_one]
  have hy : ∀ k : HexEvenAutomorphisms, y ≠ MulAut.conj k := by
    intro k hk
    apply hout (j.symm k)
    apply (MulAut.congr j).injective
    rw [MulAut.congr_conj, j.apply_symm_apply]
    exact hk
  intro z hz
  apply j.injective
  simpa only [y, MulAut.congr_apply, MulEquiv.trans_apply, j.symm_apply_apply, map_inv] using
    GLS3.Chapter5.TripleSixActorInversion.hexEven_center_inverted y hy2 hy (j z)
      ((centerCongr j ⟨z, hz⟩).property)

private theorem outside_not_inner (K : Subgroup G) [K.Normal]
    (hF : generalizedFitting G = K) (t : G) (ht : t ∉ K) :
    ∀ k : K, (MulAut.conjNormal t : MulAut K) ≠ MulAut.conj k := by
  intro k hk
  have hm : t ∈ (MulAut.innerSubgroup K).comap MulAut.conjNormal := ⟨k, hk.symm⟩
  rw [MulAut.conjNormal_comap_innerSubgroup] at hm
  have hC : centralizer (K : Set G) ≤ K := hF ▸ centralizer_generalizedFitting_le G
  exact ht ((sup_le le_rfl hC) hm)

/-- The literal hatted symmetric-six extension, including its actual sign action. -/
structure TripleSymmetricExtension (D : Type*) [Group D] where
  kernel : Subgroup D
  [normal : kernel.Normal]
  kernelEquiv : kernel ≃* Multiplicative (ZMod 3)
  quotientEquiv : (D ⧸ kernel) ≃* Perm (Fin 6)
  kernel_le : kernel ≤ commutator D
  derived_perfect : Group.IsPerfect (commutator D)
  derived_center : Nonempty (center (commutator D) ≃* Multiplicative (ZMod 3))
  derived_quotient : Nonempty ((commutator D) ⧸ center (commutator D) ≃*
    alternatingGroup (Fin 6))
  center_eq : (center (commutator D)).map (commutator D).subtype = kernel
  inverse_action : ∀ g : D,
    Perm.sign (quotientEquiv (QuotientGroup.mk' kernel g)) = -1 →
      ∀ z : kernel, g * (z : D) * g⁻¹ = (z : D)⁻¹

attribute [instance] TripleSymmetricExtension.normal

/-- Construct the full hatted symmetric-six data from the original normal component. -/
def tripleExtension
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) [K.Normal] (hquot : IsPGroup 2 (G ⧸ K))
    (hF : generalizedFitting G = K) (j : K ≃* HexEvenAutomorphisms) :
    TripleSymmetricExtension G := by
  let : Group.IsPerfect HexEvenAutomorphisms := Representation.Hexacode.even_isPerfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := j.symm.toMonoidHom) j.symm.surjective
  let e := centralEquiv j
  have hc : Nat.card (center K) = 3 :=
    (Nat.card_congr (centerCongr j).toEquiv).trans Representation.Hexacode.even_center_card
  have ho : Odd (Nat.card (center K)) := hc ▸ (by decide : Odd 3)
  have hsplit := central_involution T eT K hquot e ho
  have hindex := hsplit.1
  let t : G := hsplit.2.choose
  have ht2 : orderOf t = 2 := hsplit.2.choose_spec.2.1
  have htout : t ∉ K := hsplit.2.choose_spec.2.2.1
  have hn := quotientAction_natural T eT K hquot e ho
  have hne : K ≠ ⊤ := by intro h; exact htout (h ▸ mem_top t)
  let f := action K e hn
  have hf := action_surjective K hF hne e hn
  have hk := action_ker K hF e hn
  have hd := derived_eq K hF e hn
  let q : (G ⧸ f.ker) ≃* Perm (Fin 6) := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hkerCard : Nat.card f.ker = 3 := by
    rw [hk, card_map_of_injective K.subtype_injective, hc]
  have hderivedCard : Nat.card (center (commutator G)) = 3 := by rwa [hd]
  refine {
    kernel := f.ker
    kernelEquiv := mulEquivOfPrimeCardEq hkerCard (by simp)
    quotientEquiv := q
    kernel_le := by rw [hd, hk]; exact map_subtype_le _
    derived_perfect := hd ▸ inferInstance
    derived_center := ⟨mulEquivOfPrimeCardEq hderivedCard (by simp)⟩
    derived_quotient := by cases hd; exact ⟨e⟩
    center_eq := by rw [hd, hk]
    inverse_action := ?_ }
  intro g hg z
  have hgout : g ∉ K := by
    intro hgK
    have heven : Perm.sign (f g) = 1 := by
      change f g ∈ alternatingGroup (Fin 6)
      rw [← action_preimage K hF e hn] at hgK
      exact hgK
    change Perm.sign (f g) = -1 at hg
    exact (by decide : (1 : ℤˣ) ≠ -1) (heven.symm.trans hg)
  have hut : g * t⁻¹ ∈ K := by
    rw [K.mul_mem_iff_of_index_two hindex, K.inv_mem_iff]
    exact iff_of_false hgout htout
  let u : K := ⟨g * t⁻¹, hut⟩
  have hz : (z : G) ∈ (center K).map K.subtype := hk ▸ z.property
  obtain ⟨k, hkc, hkz⟩ := hz
  have hta : (MulAut.conjNormal t : MulAut K) ^ 2 = 1 := by
    rw [← map_pow, ← ht2, pow_orderOf_eq_one, map_one]
  have hi := center_inverted_of_hex_model j (MulAut.conjNormal t) hta
    (outside_not_inner K hF t htout) k hkc
  have hiv := congrArg Subtype.val hi
  change t * (k : G) * t⁻¹ = (k : G)⁻¹ at hiv
  have huc : (u : G) * (k : G)⁻¹ * (u : G)⁻¹ = (k : G)⁻¹ := by
    have hu := congrArg Subtype.val (mem_center_iff.mp ((center K).inv_mem hkc) u)
    change (u : G) * (k : G)⁻¹ = (k : G)⁻¹ * (u : G) at hu
    rw [hu, mul_inv_cancel_right]
  have hgi : g * (k : G) * g⁻¹ = (k : G)⁻¹ := by
    calc
      g * (k : G) * g⁻¹ = (u : G) * (t * (k : G) * t⁻¹) * (u : G)⁻¹ := by
        dsimp [u]
        group
      _ = (k : G)⁻¹ := by rw [hiv, huc]
  change (k : G) = (z : G) at hkz
  rwa [hkz] at hgi

end Theory.HexEvenExtension
