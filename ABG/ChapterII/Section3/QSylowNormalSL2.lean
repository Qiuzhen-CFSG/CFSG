module
public import ABG.ChapterII.Section3.QProjectiveLinearComplement
public import Theory.GroupTheory.SylowNoIndexTwoComparison
public import Theory.SpecificGroups.SL2.NoIndexTwo

/-!
# The actual normal SL2 Sylow layer in an enlarged Q-group

For a finite enlarged Q-group with trivial odd core and a supplied normal
SL2 subgroup over an odd finite field, the original Definition 3 overgroup
witness can be chosen so that its designated largest quaternion subgroup
is exactly the image of the Sylow intersection with that SL2 subgroup.
The Sylow subgroup itself need not be full semidihedral or wreathed;
proper quaternion overgroups and fields of orders three and nine remain.

Retain the actual normal subgroup K and linked quaternion subgroup Y from
the Q definition. The prescribed projective decomposition puts the ambient
derived subgroup inside Z(R)L0, with Z(R) central. Since SL2 has no normal
subgroup of index two, the generic normal-layer comparison gives
R∩K=R∩L0. Applying the original injective overgroup map then identifies Y
with the actual SL2 intersection, without introducing a new quaternion model.

This is the Sylow-layer identification in Alperin--Brauer--Gorenstein
II.3 Proposition 3, article pp25–26. It supplies the exact quaternion input
for matching central-product radii with the concrete matrix Sylow models.
-/

namespace ABG
open GorensteinWalter
universe u

public theorem qGroup_exists_sylow_embedding_normal_sl2
    {H : Type u} [Group H] [Finite H] (hH : IsQGroup H)
    (hcore : pPrimeCore 2 H = ⊥) (L0 : Subgroup H) [L0.Normal]
    (F : Type u) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (eL0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ (S : Type u) (iS : Group S), letI := iS;
      (Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S) ∧
        ∃ (R : Sylow 2 H) (f : R →* S) (Y : Subgroup S),
          Function.Injective f ∧ IsLargestQuaternionSubgroup Y ∧
            (L0.comap (R : Subgroup H).subtype).map f = Y := by
  obtain ⟨S, iS, hS, R, f, Y, K, hf, hY, hKN, ⟨m, hKm⟩, hKno, _hw, hlink⟩ :=
    isQGroup_iff_quaternionOvergroup.mp hH
  let : Group S := iS
  let : K.Normal := hKN
  let Z := subgroupCenter (R : Subgroup H)
  have hZ : Z ≤ Subgroup.center H := by
    have h := qGroup_eq_oddCore_mul_sylowCenterCentralizer hH R
    rw [hcore, bot_sup_eq] at h
    exact Subgroup.centralizer_eq_top_iff_subset.mp h
  let : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZ hz) g, mul_inv_cancel_right]
    exact hz⟩
  obtain ⟨_hZc, _hZcyc, _hZne, _hZtwo, φ, L, E, _hφ, _hLN, _hL0,
      _hc, _hEcyc, _hEodd, _hLmap, _hL0map, _hEmap, _hidx, hcomm⟩ :=
    qGroup_projective_linear_complement hH hcore R Z rfl L0 F hF eL0
  have hodd : Odd (Nat.card F) := by
    obtain ⟨p, n, _hp, hpodd, _hn, he⟩ := hF
    rw [he]
    exact hpodd.pow
  have hno : ∀ M : Subgroup L0, M.Normal → M.index ≠ 2 := by
    intro M _hMN
    have h := Matrix.SpecialLinearGroup.index_ne_two
      (GorensteinWalter.two_ne_zero_of_odd_card F hodd) (M.map eL0.toMonoidHom)
    exact fun hm => h ((M.index_map_equiv eL0).trans hm)
  have heq := Subgroup.sylow_intersections_eq_of_central_abelian_quotient
    K L0 Z m hKm hKno hno hZ hcomm R
  have heq' : K.comap (R : Subgroup H).subtype = L0.comap (R : Subgroup H).subtype := by
    ext r
    constructor
    · intro hr
      have hx : (r : H) ∈ (R : Subgroup H) ⊓ K := ⟨r.property, hr⟩
      rw [heq] at hx
      exact hx.2
    · intro hr
      have hx : (r : H) ∈ (R : Subgroup H) ⊓ L0 := ⟨r.property, hr⟩
      rw [← heq] at hx
      exact hx.2
  refine ⟨S, iS, hS, R, f, Y, hf, hY, ?_⟩
  rw [← heq']
  exact hlink

end ABG

