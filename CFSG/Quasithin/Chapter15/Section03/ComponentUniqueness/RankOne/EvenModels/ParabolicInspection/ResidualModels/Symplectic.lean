module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.ResidualModels.Data
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.ResidualTransport
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.CubicSubgroup
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.QuasithinBasic

/-!
# Excluding larger-field symplectic parabolics by their three-residuals

The original normal four-group lies in the component. Its normalizer in
Sp₄ therefore lies in a conjugate full point or plane parabolic, placing
the actual local intersection there. The determinant-one Levi projection
onto SL₂ shows that solvability of O^{3′} forces this intersection to
normalize its Sylow two-subgroup. The supplied parabolic contains that
normalizer, so the intersection is exactly the Borel.

The cubic two-core index forces three to divide the Borel order, excluding
odd field degree. In even degree the two independent split-torus coordinates
supply an elementary abelian subgroup of order nine, contradicting the
three-rank bound from the same residual index. All transports use the
actual component-to-matrix equivalence. No solvability assertion for the
whole parabolic is inferred from solvability of its residual, and the
O² calculations for the Borel are not substituted for O^{3′}.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
15.3.43, printed p.1140; the incoming symplectic family is supplied by
1.1.5(3)(a), pp.501–502, and A.2.3–4, p.33.
-/

public section

open Subgroup
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)

private noncomputable def localEquiv :
    M.subgroupOf L ≃* (M ⊓ L : Subgroup G) :=
  (MulEquiv.subgroupCongr (inf_subgroupOf_right M L).symm).trans
    (subgroupOfEquivOfLe inf_le_right)

include c in
private theorem local_residual_solvable :
    Group.IsSolvable (primeToResidual 3 (M.subgroupOf L)) := by
  have hr := residual_on_component c
  rw [threeResidualIn_eq_primeToResidual] at hr
  let e := (primeToResidualEquiv 3 (localEquiv (M := M) (L := L))).trans
    (((primeToResidual 3 (M ⊓ L : Subgroup G)).equivMapOfInjective
      (M ⊓ L).subtype (M ⊓ L).subtype_injective).trans
        (MulEquiv.subgroupCongr hr.symm))
  let := actor_solvable c
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

omit [Finite G] in
private theorem componentSylow_eq (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = S ⊓ L) : S.subgroupOf L = P := by
  apply Subgroup.map_injective L.subtype_injective
  rw [subgroupOf_map_subtype, hP]

omit [Finite G] in
private theorem borel_subgroupOf_sylow (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = S ⊓ L) :
    (ChapterF.Source.borel L S).subgroupOf L = normalizer (P : Set L) := by
  rw [ChapterF.Source.borel, inf_subgroupOf_left,
    subgroupOf_normalizer_eq inf_le_right, inf_subgroupOf_right, componentSylow_eq P hP]
  rfl

include c in
private theorem symplectic_normalizes {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) (e : L ≃* Sp F) (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = S ⊓ L) :
    M.subgroupOf L ≤ normalizer (P : Set L) := by
  let H := (M.subgroupOf L).map e.toMonoidHom
  let W := (V₂.subgroupOf L).map e.toMonoidHom
  let T := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hVW : V₂ ≃* W := (subgroupOfEquivOfLe (plane_le_component c)).symm.trans
    (e.subgroupMap (V₂.subgroupOf L))
  have hWne : W ≠ ⊥ := by
    intro hw
    have hc := (Nat.card_congr hVW.toEquiv).symm.trans c.plane_two_card
    rw [hw, Subgroup.card_bot] at hc
    norm_num at hc
  have hWp : IsPGroup 2 W := by
    let := c.plane_two_elementary
    exact (IsElementaryAbelian.isPGroup 2 V₂).of_equiv hVW
  have hnorm : M.subgroupOf L ≤ normalizer (V₂.subgroupOf L : Set L) := by
    rw [← subgroupOf_normalizer_eq (plane_le_component c)]
    exact fun x hx => c.plane_two_normalized ⟨hx, c.component_le x.property⟩
  have hHW : H ≤ normalizer (W : Set (Sp F)) := by
    exact (map_mono hnorm).trans ((V₂.subgroupOf L).le_normalizer_map e.toMonoidHom)
  obtain ⟨g, hg⟩ := twoLocal_parabolic_cover_of_charTwo
    (normalizer (W : Set (Sp F))) ⟨W, hWne, hWp, rfl⟩
  have hpar : ∃ g : Sp F, H.map (MulAut.conj g).toMonoidHom ≤ pointParabolic ∨
      H.map (MulAut.conj g).toMonoidHom ≤ planeParabolic := by
    exact ⟨g, hg.imp ((map_mono hHW).trans) ((map_mono hHW).trans)⟩
  have hsol : Group.IsSolvable (primeToResidual 3 H) := by
    let := local_residual_solvable c
    let f := primeToResidualEquiv 3 (e.subgroupMap (M.subgroupOf L))
    exact Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective
  have hTH : (T : Subgroup (Sp F)) ≤ H := by
    apply map_mono
    rw [← componentSylow_eq P hP]
    exact fun _ hx => c.sylow_le_M hx
  have hn := ThreeResidualPlacement.conjugate_parabolic_le_normalizer hF T H hsol hTH hpar
  change (M.subgroupOf L).map e.toMonoidHom ≤
    normalizer ((P : Subgroup L).map e.toMonoidHom : Set (Sp F)) at hn
  rw [← map_equiv_normalizer_eq] at hn
  exact (map_le_map_iff_of_injective e.injective).mp hn

private theorem symplectic_intersection {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSp L 2 (2 ^ n)) (hp : QuotientParabolic c) :
    M ⊓ L = ChapterF.Source.borel L S := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hcard
  let f : L ≃* Sp F := e.trans EvenProjective.equiv.symm
  have hlarge : 2 < Nat.card F := by
    rw [hcard]
    exact (show (2 : ℕ) ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
  obtain ⟨P, hP⟩ := component_sylow c
  have hle := symplectic_normalizes c hlarge f P hP
  rw [← borel_subgroupOf_sylow P hP] at hle
  have hm := map_mono (f := L.subtype) hle
  rw [subgroupOf_map_subtype, map_subgroupOf_eq_of_le
    (show ChapterF.Source.borel L S ≤ L from inf_le_left)] at hm
  exact le_antisymm hm (borel_le_intersection c hp)

/-- The larger-field symplectic family is incompatible with the actual
prime-to-three residual and the normal four-group in the reduced configuration. -/
theorem symplectic_residual_exclusion {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSp L 2 (2 ^ n)) (hp : QuotientParabolic c) : False := by
  have hB := symplectic_intersection c hn hm hp
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hcard
  let f : L ≃* Sp F := e.trans EvenProjective.equiv.symm
  obtain ⟨P, hP⟩ := component_sylow c
  let T := P.mapSurjective (f := f.toMonoidHom) f.surjective
  have hlocal : M.subgroupOf L = normalizer (P : Set L) := by
    rw [← inf_subgroupOf_right M L, hB, borel_subgroupOf_sylow P hP]
  have hnmap : (normalizer (P : Set L)).map f.toMonoidHom =
      normalizer (T : Set (Sp F)) := map_equiv_normalizer_eq (P : Subgroup L) f
  let j : (M ⊓ L : Subgroup G) ≃* normalizer (T : Set (Sp F)) :=
    (localEquiv (M := M) (L := L)).symm.trans
      ((MulEquiv.subgroupCongr hlocal).trans
        ((f.subgroupMap (normalizer (P : Set L))).trans
          (MulEquiv.subgroupCongr hnmap)))
  have h3Y : 3 ∣ Nat.card Yplus := c.index ▸ (pCore 2 Yplus).index_dvd_card
  have hYM : Yplus ≤ M ⊓ L :=
    le_inf ((actor_le_local c).trans inf_le_left) c.y_le_component
  have h3B : 3 ∣ Nat.card (normalizer (T : Set (Sp F))) := by
    rw [← Nat.card_congr j.toEquiv]
    exact h3Y.trans (Subgroup.card_dvd_of_le hYM)
  have heven : Even n := by
    by_contra he
    exact EvenBorelTorus.three_not_dvd_card_normalizer hcard hn.le
      (Nat.not_even_iff_odd.mp he) T h3B
  let k := j.trans (EvenBorelTorus.sylowNormalizerEquiv hcard hn.le T)
  have hr := threeRank_le_one_of_residual_index (residual_on_component c) c.index
  rw [Theory.GroupTheory.primeRank_equiv 3 k] at hr
  obtain ⟨E, hE, hEc⟩ := EvenBorelTorus.exists_cubic_borel_subgroup hcard heven
  have hc := (primeRank_le_iff_elementary_card_le _).mp hr E hE
  rw [hEc] at hc
  norm_num at hc

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
