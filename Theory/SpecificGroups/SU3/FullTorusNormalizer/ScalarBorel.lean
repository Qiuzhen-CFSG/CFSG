module

public import Theory.SpecificGroups.SU3.FullTorusNormalizer.ScalarCover
public import Theory.GroupTheory.CyclicHallNormalizerEscape

/-!
# Odd normalizer escape in scalar unitary covers

The full torus has two-power index in the projective Borel. This relative
index is unchanged under preimage by a surjection. A scalar cover makes
the full preimage torus cyclic and supplies its escaping Weyl normalizer.
Sylow conjugacy consequently gives escape for every odd-primary subgroup
of the preimage Borel, including at the scalar prime three.

Source: Aschbacher–Smith 4.4.13(1), pp.623–624.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Theory.SpecificGroups.UnitaryBorel
variable {E : Type*} [Field E] [Finite E] [CharP E 2]
  (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

theorem fullTorus_relativeIndex_twoPower :
    ∃ n : ℕ, (hermitianTorusPSU J hJ).range.relIndex
      (BenderBorel.unitaryBorel J hJ) = 2^n := by
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let B := BenderBorel.unitaryBorel J hJ
  let U := (hermitianUnipotentPSU J hJ).range
  let T := (hermitianTorusPSU J hJ).range
  let UB := U.subgroupOf B
  let TB := T.subgroupOf B
  let : UB.Normal := BenderBorel.hermitian_root_normal J hJ
  have hU : IsPGroup 2 UB :=
    ((BenderBorel.hermitian_root_isPGroup J).of_surjective
      (hermitianUnipotentPSU J hJ).rangeRestrict
      (hermitianUnipotentPSU J hJ).rangeRestrict_surjective).comap_subtype
  have hgen : UB ⊔ TB = ⊤ := by
    rw [← subgroupOf_sup (show U ≤ B from le_sup_left) (show T ≤ B from le_sup_right)]
    exact subgroupOf_self B
  have hd := Theory.GroupTheory.index_dvd_of_normal_supplement UB TB hgen
  obtain ⟨n,hn⟩ := hU.exists_card_eq
  rw [hn] at hd
  obtain ⟨m,_,hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact ⟨m,hm⟩

theorem fullTorus_preimage_relativeIndex_twoPower {L : Type*} [Group L]
    (r : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hr : Function.Surjective r) :
    ∃ n : ℕ, ((hermitianTorusPSU J hJ).range.comap r).relIndex
      ((BenderBorel.unitaryBorel J hJ).comap r) = 2^n := by
  rw [relIndex_comap,map_comap_eq_self_of_surjective hr]
  exact fullTorus_relativeIndex_twoPower J hJ

/-- Every odd-primary subgroup in the full Borel preimage of a scalar SU₃
cover has a normalizer outside that preimage. -/
theorem odd_normalizer_not_le_borel_preimage_of_scalar_lift
    {L : Type*} [Group L] [Finite L]
    (r : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hr : Function.Surjective r)
    (k : J.specialSubgroup →* L) (hk : Function.Surjective k)
    (hfac : r.comp k = J.specialToProjective)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (A : Subgroup L) (hA : IsPGroup p A)
    (hAB : A ≤ (BenderBorel.unitaryBorel J hJ).comap r) :
    ¬ normalizer (A : Set L) ≤ (BenderBorel.unitaryBorel J hJ).comap r := by
  let C := (hermitianTorusPSU J hJ).range.comap r
  let B := (BenderBorel.unitaryBorel J hJ).comap r
  let : IsCyclic C := fullTorus_preimage_isCyclic_of_scalar_lift J hJ r k hk hfac
  have hCB : C ≤ B := comap_mono (show (hermitianTorusPSU J hJ).range ≤
    BenderBorel.unitaryBorel J hJ from le_sup_right)
  obtain ⟨n,hn⟩ := fullTorus_preimage_relativeIndex_twoPower J hJ r hr
  have hindex : ¬ p ∣ (C.subgroupOf B).index := by
    change ¬ p ∣ C.relIndex B
    rw [hn]
    exact fun hd => (Fact.out : p.Prime).ne_one
      (Nat.eq_one_of_dvd_coprimes (hp.coprime_two_right.pow_right n) (dvd_refl p) hd)
  obtain ⟨hw,hout⟩ := scalar_weyl_escape J hJ r k hk hfac
  exact Theory.GroupTheory.normalizer_not_le_of_cyclic_torus B C A hCB hindex
    hA hAB (k (hermitianWeylSU J hJ)) hw hout

end Theory.SpecificGroups.UnitaryBorel
