module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryExclusion.ModelCore.Coordinates
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel.Projective

/-!
# The order-five action on a PSU₃(4) Sylow subgroup

An element of order five in the Sylow normalizer acts nontrivially by
conjugation. In the actual projective unitary model, the root group acts
regularly on the complement of infinity in the 65 isotropic points, and
its normalizer fixes infinity. The cyclic five-group has a second fixed
point by orbit counting. If its generator centralizes the root group,
transitivity propagates that fixed point to the entire complement;
faithfulness then forces the generator to be the identity.

The marked Sylow coordinates transport centralization to this matrix root.
The actual normalizer conjugation homomorphism has order-five image, since
its image is nonidentity and its order divides five.

Source: Huppert II.10.12 for the action and root coordinates;
Aschbacher--Smith, proof of 15.3.40, printed p.1138, for the unitary
exclusion that consumes this intrinsic action calculation.
-/

open Subgroup

private theorem five_centralizer_obstruction
    {G Ω : Type*} [Group G] [Finite Ω]
    (ρ : G →* Equiv.Perm Ω) (hρ : Function.Injective ρ)
    (R : Subgroup G) (pinf : Ω) (hcard : Nat.card Ω = 65)
    (htrans : ∀ x y : Ω, x ≠ pinf → y ≠ pinf → ∃ r : R, ρ r x = y)
    (a : G) (ha : orderOf a = 5) (hfix : ρ a pinf = pinf)
    (hcentral : a ∈ centralizer (R : Set G)) : False := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : MulAction G Ω := MulAction.compHom Ω ρ
  have hC : IsPGroup 5 (zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ha, pow_one])
  have hinf : pinf ∈ MulAction.fixedPoints (zpowers a) Ω := by
    intro c
    exact smul_eq_self_of_mem_zpowers c.property hfix
  obtain ⟨b, hb, hbinf⟩ := hC.exists_fixed_point_of_prime_dvd_card_of_fixed_point Ω
    (by rw [hcard]; decide) hinf
  have hab : ρ a b = b := hb ⟨a, mem_zpowers a⟩
  have he : ρ a = 1 := by
    ext x
    change ρ a x = x
    by_cases hx : x = pinf
    · simpa [hx] using hfix
    obtain ⟨r, hr⟩ := htrans b x hbinf.symm hx
    rw [← hr]
    calc
      ρ a (ρ r b) = ρ (a * r) b := by rw [map_mul]; rfl
      _ = ρ ((r : G) * a) b := by rw [hcentral r r.property]
      _ = ρ r (ρ a b) := by rw [map_mul]; rfl
      _ = ρ r b := by rw [hab]
  have haone : a = 1 := hρ (he.trans ρ.map_one.symm)
  simp [haone] at ha

open BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.External
open CFSG.Quasithin.ChapterF.Source.Unitary
open scoped Matrix

private theorem root_centralizer_has_no_five
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (a : ProjectiveSpecialUnitaryMatrixGroup J) (ha : orderOf a = 5) :
    a ∉ centralizer ((hermitianUnipotentPSU J hJ).range : Set _) := by
  intro hcentral
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let Ω := unitaryIsotropicPoints J
  obtain ⟨hΩ, ρ, pinf, hρ, _hnatural, _hUcard,
    ⟨R, D, hRU, _hDU, hUN, _hdisj, _hsup, _hcyc, hRcard,
      _hcomm, _hcommcard, _hDcard, hregular,
      ⟨coord, hcoord⟩, _hDcoord, _hDsurj⟩,
    _htwo, _hGcard, _hthree⟩ :=
      huppert_II_10_12 J 4 hcard
        (fixed_card J 2 (by decide) hcard hconj) hJ
  have hroot (z : hermitianUnipotentCoord J) :
      (coord z : G) = hermitianUnipotentPSU J hJ z := by
    obtain ⟨M, hM, hproj⟩ := hcoord z
    apply Subtype.ext
    rw [hproj, hermitianUnipotentPSU_val]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun (congrFun hM i) j
  have hR : R = (hermitianUnipotentPSU J hJ).range := by
    ext g
    constructor
    · intro hg
      obtain ⟨z, hz⟩ := coord.surjective ⟨g, hg⟩
      refine ⟨z, ?_⟩
      rw [← hroot, hz]
    · rintro ⟨z, rfl⟩
      rw [← hroot]
      exact (coord z).property
  rw [← hR] at hcentral
  let : Finite Ω := Nat.finite_of_card_ne_zero (by rw [hΩ]; decide)
  let : MulAction G Ω := MulAction.compHom Ω ρ
  have hRne : R ≠ ⊥ := by
    intro h
    have hc : Nat.card R = 1 := by rw [h]; simp
    norm_num [hc] at hRcard
  have hnormalizer : normalizer (R : Set G) = MulAction.stabilizer G pinf :=
    normalizer_eq_stabilizer_of_regular_compl R pinf hRU hRne hregular hUN
  have hafix : ρ a pinf = pinf := by
    have hn : a ∈ normalizer (R : Set G) := Subgroup.centralizer_le_normalizer _ hcentral
    rw [hnormalizer] at hn
    exact hn
  exact five_centralizer_obstruction ρ hρ R pinf hΩ
    (fun x y hx hy => (hregular x y hx hy).exists) a ha hafix hcentral

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryExclusion

/-- Every five-element of the marked PSU₃(4) Sylow normalizer induces an
order-five automorphism through the actual conjugation homomorphism. -/
public theorem unitary_four_normalizer_five_action
    {H : Type*} [Group H] [Finite H] (hm : ClassicalGroup.IsPSU H 3 4)
    (P : Sylow 2 H) (a : Subgroup.normalizer (P : Set H))
    (ha : orderOf a = 5) :
    orderOf ((P : Subgroup H).normalizerMonoidHom a) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime
  · rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  · intro heq
    have hc : (a : H) ∈ centralizer ((P : Subgroup H) : Set H) := by
      have hk : a ∈ (P : Subgroup H).normalizerMonoidHom.ker := heq
      rw [normalizerMonoidHom_ker] at hk
      exact hk
    obtain ⟨F, _, _, J, hJ, hcard, hconj, e, hP⟩ :=
      unitary_four_sylow_coordinates hm P
    apply root_centralizer_has_no_five J hJ hcard hconj (e a)
      (by rw [e.orderOf_eq, Subgroup.orderOf_coe, ha])
    rw [← hP]
    rintro x ⟨y, hy, rfl⟩
    change e y * e (a : H) = e (a : H) * e y
    simpa only [map_mul] using congrArg e (hc y hy)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryExclusion
