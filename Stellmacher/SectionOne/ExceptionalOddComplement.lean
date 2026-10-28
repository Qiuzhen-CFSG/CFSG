module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.LocalFixedIndex
public import Theory.Representation.FourNineInversion
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.Transfer

/-!
# The exceptional odd core is a full Sylow complement

Under the Section 1 hypotheses, suppose the elementary Sylow two-subgroup
has order four and the odd core has order nine. Then the odd core is
elementary abelian of exponent three and is complementary to the Sylow
subgroup in the whole ambient group.

The proved trivial Sylow centralizer of the odd core makes conjugation
faithful. Since Aut(C9) has order six, the odd core cannot be cyclic.
The faithful elementary four-on-nine action therefore contains inversion.
Its preimage in the Sylow subgroup is fixed by the entire Sylow normalizer,
because inversion commutes with every automorphism of the odd core.

Consequently the normalizer's automorphism image on the Sylow subgroup has
order at most two. Its order is also odd: the abelian Sylow subgroup lies
in the action kernel, so the image order divides its odd index in the
normalizer. Thus the Sylow normalizer centralizes the Sylow subgroup.
Burnside transfer supplies an odd normal complement. It lies in the odd
core by definition, and the complementary decomposition and coprime
intersection show that it equals the whole odd core.

This proves, rather than assumes, the full-group equality needed before
the final product identification in Stellmacher (1.6), journal p.18;
see `refs/latex/stellmacher-n-group.tex`.
-/

open scoped IsMulCommutative

namespace Stellmacher.SectionOne

universe u

/-- In the order-nine exceptional case, the odd core is elementary abelian
and is a normal complement to the elementary Sylow subgroup of order four. -/
public theorem oddCore_isComplement_sylow_of_card_nine
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS : IsElementaryAbelian 2 (S : Subgroup G))
    (hScard : Nat.card (S : Subgroup G) = 4)
    (hWcard : Nat.card (oddCore G) = 9) :
    IsElementaryAbelian 3 (oddCore G) ∧ (oddCore G).IsComplement' (S : Subgroup G) := by
  classical
  let W := oddCore G
  let SG : Subgroup G := S
  let _ : W.Normal := pPrimeCore_normal
  let _ : IsElementaryAbelian 2 SG := hS
  have hWp : IsPGroup 3 W := IsPGroup.of_card (p := 3) (n := 2) hWcard
  have hcent : SG ⊓ Subgroup.centralizer (W : Set G) = ⊥ :=
    RankOneThreeGroupAssembly.sylow_inf_centralizer_oddCore_eq_bot h SG hS hWp
  let φ : SG →* MulAut W := MulAut.conjNormal.comp SG.subtype
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro s hs
    have hscent : (s : G) ∈ Subgroup.centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have heq := congrArg (fun f : MulAut W => (f ⟨w, hw⟩ : G))
        (MonoidHom.mem_ker.mp hs)
      change (s : G) * w * (s : G)⁻¹ = w at heq
      have heq' := congrArg (fun x : G => x * (s : G)) heq
      simpa [mul_assoc] using heq'.symm
    exact Subtype.ext (hcent.le ⟨s.property, hscent⟩)
  have hnotcyclic : ¬ IsCyclic W := by
    intro hcyclic
    let _ : IsCyclic W := hcyclic
    have hAut : Nat.card (MulAut W) = 6 := by
      rw [IsCyclic.card_mulAut, hWcard]
      decide
    have hbad := Subgroup.card_dvd_of_injective φ hφinj
    rw [hScard, hAut] at hbad
    norm_num at hbad
  have hWcomm : IsMulCommutative W :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hWcard
  have hWexp : Monoid.exponent W = 3 :=
    (not_isCyclic_iff_exponent_eq_prime Nat.prime_three hWcard).mp hnotcyclic
  let hWelem : IsElementaryAbelian 3 W :=
    { toIsMulCommutative := hWcomm
      exponent_dvd_p := by rw [hWexp] }
  let _ : IsElementaryAbelian 3 W := hWelem
  have hfaith : fixingSubgroup SG (Set.univ : Set W) = ⊥ := by
    apply le_antisymm _ bot_le
    intro s hs
    apply hφinj
    rw [map_one]
    apply MulEquiv.ext
    intro w
    change s • w = w
    exact (mem_fixingSubgroup_iff (M := SG) (s := (Set.univ : Set W))).mp hs
      w (Set.mem_univ w)
  obtain ⟨z, hz, hinv⟩ := Representation.exists_inversion_of_elementary_card_four_card_nine
    hScard hWcard hfaith
  let N : Subgroup G := Subgroup.normalizer (SG : Set G)
  let f : N →* MulAut SG := SG.normalizerMonoidHom
  have hfconj (n : N) : φ (f n z) =
      MulAut.conjNormal (n : G) * φ z * (MulAut.conjNormal (n : G))⁻¹ := by
    have hval : (f n z : G) = (n : G) * (z : G) * (n : G)⁻¹ := rfl
    change MulAut.conjNormal (f n z : G) = _
    rw [hval, map_mul, map_mul, map_inv]
    rfl
  have hfix (n : N) : f n z = z := by
    apply hφinj
    rw [hfconj]
    apply MulEquiv.ext
    intro w
    have hzφ (w : W) : φ z w = w⁻¹ := hinv w
    change MulAut.conjNormal (n : G) (φ z ((MulAut.conjNormal (n : G))⁻¹ w)) = φ z w
    rw [hzφ, hzφ, map_inv]
    simp
  have hsmall : Nat.card f.range ≤ 2 :=
    card_mulAut_subgroup_le_two_of_fixed_point hScard z hz f.range
      (by rintro a ⟨n, rfl⟩; exact hfix n)
  have hSNker : SG.subgroupOf N ≤ f.ker := by
    intro s hs
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    change (s : G) * (a : G) * (s : G)⁻¹ = a
    have hcomm : (s : G) * (a : G) = (a : G) * (s : G) :=
      congrArg Subtype.val (mul_comm (⟨s, hs⟩ : SG) a)
    rw [hcomm, mul_inv_cancel_right]
  have hdiv : Nat.card f.range ∣ (SG.subgroupOf N).index := by
    rw [← Subgroup.index_ker]
    exact Subgroup.index_dvd_of_le hSNker
  have hodd : ¬ 2 ∣ Nat.card f.range := by
    intro hdvd
    exact (S.subtype (show SG ≤ N from Subgroup.le_normalizer)).not_dvd_index
      (hdvd.trans hdiv)
  have hone : Nat.card f.range = 1 := by omega
  have hrange : f.range = ⊥ := Subgroup.card_eq_one.mp hone
  have hNcent : N ≤ Subgroup.centralizer (SG : Set G) := by
    intro n hn
    have hf : f ⟨n, hn⟩ = 1 := hrange.le ⟨⟨n, hn⟩, rfl⟩
    have hk : (⟨n, hn⟩ : N) ∈ f.ker := MonoidHom.mem_ker.mpr hf
    change (⟨n, hn⟩ : N) ∈ SG.normalizerMonoidHom.ker at hk
    rw [Subgroup.normalizerMonoidHom_ker] at hk
    exact hk
  let K : Subgroup G := (MonoidHom.transferSylow S hNcent).ker
  have hKcomp : K.IsComplement' SG := MonoidHom.ker_transferSylow_isComplement' S hNcent
  have hKodd : Nat.Coprime 2 (Nat.card K) :=
    Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mpr
      (MonoidHom.not_dvd_card_ker_transferSylow S hNcent)
  have hKW : K ≤ W := le_sSup ⟨inferInstance, hKodd⟩
  have hWSdisj : Disjoint W SG :=
    IsPGroup.disjoint_of_ne 3 2 (by decide) W SG hWp (hS.isPGroup 2 SG)
  have hWK : W ≤ K := by
    intro w hw
    obtain ⟨⟨k, s⟩, hks⟩ := hKcomp.2 w
    change (k : G) * (s : G) = w at hks
    have hsW : (s : G) ∈ W := by
      have heq : (s : G) = (k : G)⁻¹ * w := by rw [← hks]; simp
      rw [heq]
      exact W.mul_mem (W.inv_mem (hKW k.property)) hw
    have hs1 : (s : G) = 1 := hWSdisj.le_bot ⟨hsW, s.property⟩
    rw [hs1, mul_one] at hks
    exact hks ▸ k.property
  have hKeq : K = W := le_antisymm hKW hWK
  refine ⟨hWelem, ?_⟩
  change W.IsComplement' SG
  rw [← hKeq]
  exact hKcomp

end Stellmacher.SectionOne

