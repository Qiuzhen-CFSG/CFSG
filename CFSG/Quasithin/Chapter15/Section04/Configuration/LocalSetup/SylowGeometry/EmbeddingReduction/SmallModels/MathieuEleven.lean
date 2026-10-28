module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.SmallModels.Reduction
public import Theory.Mathieu.M11.Properties.Sylow3
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.SharpSetStabilizer

/-!
# The induced Sylow-complement automizer in M₁₁

For a Sylow two-subgroup S and an odd complement R with RS = SR, the
order-27 alternative is excluded by |M₁₁| = 7920. Thus R is elementary
abelian of order nine. Its natural degree-eleven action has a nine-point
orbit: otherwise a nonidentity point stabilizer fixes a three-point orbit
and the at least two common fixed points, contrary to sharp four-transitivity.

The product RS has order 144. Orbit divisibility forces it to preserve this
nine-point orbit. The same argument applies to N(R), whose order is 144 by
Sylow conjugacy and the checked explicit normalizer. The stabilizer of the
nine-point set also has order 144, so it equals N(R), proving that S normalizes
R for every permutable pair. Finally C_S(R), a two-group acting on nine points,
has a fixed point. Centralization of the transitive R-action makes it fix the
whole orbit, and sharp four-transitivity makes it trivial. The actual induced
automizer therefore has order |S| = 16.

This proves the fixed-carrier restriction; quotient transport and the final
source exclusion remain with the parent. No extendible pair-automizer order
is substituted for the induced conjugation image.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Proposition 1.3.4, printed pp.509–511, and the second paragraph of
15.4.20, printed p.1164. The concrete M₁₁ model and its checked natural action
are from `Theory.Mathieu.M11.Properties`.
-/

open Subgroup MulAction
open scoped Pointwise IsMulCommutative
open Sporadic.Mathieu

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.SmallModels

open Chapter1 Chapter1.XiEmbedding

private theorem fixed_set_card_lt {g : M11} (hg : g ≠ 1) :
    Set.ncard {x : Fin 11 | g • x = x} < 4 := by
  classical
  simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred] using
    m11_isSharplyFourPretransitive.card_fixedPoints_lt hg

private theorem fixes_large_set {g : M11} {A : Set (Fin 11)}
    (hc : 4 ≤ A.ncard) (hfix : ∀ x ∈ A, g • x = x) : g = 1 := by
  by_contra hg
  have hh := fixed_set_card_lt hg
  have hle := Set.ncard_mono (show A ⊆ {x | g • x = x} from hfix)
  omega

private theorem orbit_eq_orbit_of_le {R H : Subgroup M11} (hle : R ≤ H)
    {x : Fin 11} (hR : (orbit R x).ncard = 9) (hH : Nat.card H = 144) :
    orbit R x = orbit H x := by
  have hsub : orbit R x ⊆ orbit H x := by
    rintro y ⟨r, rfl⟩
    exact ⟨inclusion hle r, rfl⟩
  have hmin : 9 ≤ (orbit H x).ncard := by
    rw [← hR]
    exact Set.ncard_mono hsub
  have hmax : (orbit H x).ncard ≤ 11 := by
    simpa using Set.ncard_le_card (orbit H x)
  have hd : (orbit H x).ncard ∣ 144 := by
    rw [← index_stabilizer, ← hH]
    exact (stabilizer H x).index_dvd_card
  have hc : (orbit H x).ncard = 9 := by
    interval_cases hn : (orbit H x).ncard <;> omega
  exact Set.eq_of_subset_of_ncard_le hsub (by omega)

private theorem exists_nine_orbit (R : Subgroup M11) [IsMulCommutative R]
    (hR : IsPGroup 3 R) (hc : Nat.card R = 9) :
    ∃ x : Fin 11, (orbit R x).ncard = 9 := by
  classical
  have hfp : 2 ≤ (fixedPoints R (Fin 11)).ncard := by
    have hh := hR.card_modEq_card_fixedPoints (Fin 11)
    rw [Nat.card_fin, Nat.card_coe_set_eq] at hh
    change 11 % 3 = (fixedPoints R (Fin 11)).ncard % 3 at hh
    omega
  let : Nontrivial R := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨r, hr⟩ := exists_ne (1 : R)
  have hr' : (r : M11) ≠ 1 := fun hh => hr (Subtype.ext hh)
  obtain ⟨x, hx⟩ : ∃ x : Fin 11, (r : M11) • x ≠ x := by
    by_contra! hh
    exact hr' (Subtype.ext (Equiv.ext hh))
  have hxn : x ∉ fixedPoints R (Fin 11) := fun hh => hx (hh r)
  have hdisj : Disjoint (orbit R x) (fixedPoints R (Fin 11)) := by
    rw [Set.disjoint_left]
    intro y hy hyf
    have hxy : x = y := mem_fixedPoints'.mp hyf x ((mem_orbit_symm).mp hy)
    subst y
    exact hxn hyf
  have hpos : 0 < (orbit R x).ncard := (Set.ncard_pos).mpr ⟨x, mem_orbit_self x⟩
  have hd : (orbit R x).ncard ∣ 9 := by
    rw [← index_stabilizer, ← hc]
    exact (stabilizer R x).index_dvd_card
  have hne : (orbit R x).ncard ≠ 1 := by
    intro hh
    apply hxn
    rw [mem_fixedPoints_iff_card_orbit_eq_one, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
    exact hh
  have hcases : (orbit R x).ncard = 3 ∨ (orbit R x).ncard = 9 := by
    have hle := Nat.le_of_dvd (by omega : 0 < 9) hd
    interval_cases hn : (orbit R x).ncard <;> omega
  rcases hcases with hthree | hnine
  · have hs : Nat.card (stabilizer R x) = 3 := by
      have hh := (stabilizer R x).card_mul_index
      rw [index_stabilizer, hc, hthree] at hh
      omega
    let : Nontrivial (stabilizer R x) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨a, ha⟩ := exists_ne (1 : stabilizer R x)
    have ha' : ((a : R) : M11) ≠ 1 := by
      intro hh
      exact ha (Subtype.ext (Subtype.ext hh))
    apply False.elim
    apply ha'
    apply fixes_large_set (A := orbit R x ∪ fixedPoints R (Fin 11))
    · rw [Set.ncard_union_eq hdisj, hthree]
      omega
    · intro y hy
      rcases hy with hy | hy
      · obtain ⟨b, rfl⟩ := hy
        change (a : R) • (b • x) = b • x
        rw [← mul_smul, mul_comm, mul_smul, mem_stabilizer_iff.mp a.property]
      · exact hy a
  · exact ⟨x, hnine⟩

private theorem pair_stabilizer_card (t : Set.powersetCard (Fin 11) 2) :
    Nat.card (stabilizer M11 t) = 144 := by
  let : IsMultiplyPretransitive M11 (Fin 11) 4 := m11_isFourPretransitive
  let : IsMultiplyPretransitive M11 (Fin 11) 2 :=
    isMultiplyPretransitive_of_le (m := 2) (n := 4) (by norm_num) (by norm_num)
  let : IsPretransitive M11 (Set.powersetCard (Fin 11) 2) :=
    Set.powersetCard.isPretransitive_of_isMultiplyPretransitive
      (G := M11) (α := Fin 11) (n := 2) inferInstance
  have hh := (stabilizer M11 t).card_mul_index
  rw [index_stabilizer_of_transitive, Set.powersetCard.card, Nat.card_fin, m11_order] at hh
  norm_num [Nat.choose] at hh ⊢
  omega

private theorem nine_stabilizer_card (A : Set (Fin 11)) (hc : A.ncard = 9) :
    Nat.card (stabilizer M11 A) = 144 := by
  classical
  have hcomp : Aᶜ.ncard = 2 := by
    rw [Set.ncard_compl, hc]
    norm_num
  let t : Set.powersetCard (Fin 11) 2 := ⟨Aᶜ.toFinset, by
    change Aᶜ.toFinset.card = 2
    rwa [← Set.ncard_eq_toFinset_card']⟩
  have ht : (t : Set (Fin 11)) = Aᶜ := by
    change (Aᶜ.toFinset : Set (Fin 11)) = Aᶜ
    exact Set.coe_toFinset _
  have hst : stabilizer M11 A = stabilizer M11 t := by
    calc
      stabilizer M11 A = stabilizer M11 Aᶜ := (stabilizer_compl (G := M11) (s := A)).symm
      _ = stabilizer M11 (t : Set (Fin 11)) := by rw [ht]
      _ = stabilizer M11 t := (Set.powersetCard.stabilizer_coe (G := M11) t).symm
  rw [hst, pair_stabilizer_card]

private theorem le_nine_stabilizer {R H : Subgroup M11} (hle : R ≤ H)
    {x : Fin 11} (hR : (orbit R x).ncard = 9) (hH : Nat.card H = 144) :
    H ≤ stabilizer M11 (orbit R x) := by
  rw [orbit_eq_orbit_of_le hle hR hH]
  intro g hg
  exact smul_orbit (⟨g, hg⟩ : H) x

private theorem two_centralizer_eq_bot (S R : Subgroup M11)
    (hS : IsPGroup 2 S) {x : Fin 11} (hR : (orbit R x).ncard = 9)
    (hstab : S ≤ stabilizer M11 (orbit R x)) :
    S ⊓ centralizer (R : Set M11) = ⊥ := by
  let A := orbit R x
  let K := S ⊓ centralizer (R : Set M11)
  let f : K →* stabilizer M11 A := inclusion (inf_le_left.trans hstab)
  let : MulAction K A := MulAction.compHom A f
  have hK : IsPGroup 2 K := hS.of_injective (inclusion inf_le_left) (inclusion_injective _)
  obtain ⟨y, hy⟩ := hK.nonempty_fixed_point_of_prime_not_dvd_card A (by
    rw [Nat.card_coe_set_eq]
    change ¬ 2 ∣ (orbit R x).ncard
    rw [hR]
    norm_num)
  apply eq_bot_iff.mpr
  intro g hg
  have hgy : g • (y : Fin 11) = y := by
    exact congrArg Subtype.val (hy (⟨g, hg⟩ : K))
  apply fixes_large_set (A := orbit R y)
  · have he : orbit R (y : Fin 11) = orbit R x := orbit_eq_iff.mpr y.property
    rw [he, hR]
    omega
  · rintro z ⟨r, rfl⟩
    have hcomm : g * (r : M11) = (r : M11) * g :=
      (mem_centralizer_iff.mp hg.2 r r.property).symm
    change g • ((r : M11) • (y : Fin 11)) = (r : M11) • (y : Fin 11)
    rw [← mul_smul, hcomm, mul_smul, hgy]

private theorem sylow_two_card (S : Sylow 2 M11) : Nat.card S = 16 := by
  rw [S.card_eq_multiplicity, m11_order]
  have hzero : padicValNat 2 495 = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
  rw [Nat.factorization_def 7920 Nat.prime_two,
    show (7920 : Nat) = 2 ^ 4 * 495 by norm_num,
    padicValNat_base_pow_mul (by norm_num) (by norm_num) 4, hzero]
  norm_num

private theorem normalizer_nine_card (R : Subgroup M11) (hc : Nat.card R = 9) :
    Nat.card (normalizer (R : Set M11)) = 144 := by
  have hchosen : Nat.card m11Sylow3 = 9 := by
    change Nat.card m11Sylow3Subgroup = 9
    exact m11Sylow3Subgroup_card
  let P : Sylow 3 M11 := Sylow.ofCard R (by
    rw [hc, ← m11Sylow3.card_eq_multiplicity, hchosen])
  have hi : (normalizer (R : Set M11)).index =
      (normalizer (m11Sylow3Subgroup : Set M11)).index := by
    change (normalizer (P : Set M11)).index = (normalizer (m11Sylow3 : Set M11)).index
    rw [← P.card_eq_index_normalizer, ← m11Sylow3.card_eq_index_normalizer]
  have hh := (normalizer (m11Sylow3Subgroup : Set M11)).card_mul_index
  rw [m11Sylow3_normalizer_card, m11_order] at hh
  have hh' := (normalizer (R : Set M11)).card_mul_index
  rw [hi, m11_order] at hh'
  have hin : (normalizer (m11Sylow3Subgroup : Set M11)).index = 55 := by omega
  rw [hin] at hh'
  omega

private theorem automizer_card_of_normalizes (S : Sylow 2 M11) (R : Subgroup M11)
    (hN : (S : Subgroup M11) ≤ normalizer (R : Set M11))
    (hC : (S : Subgroup M11) ⊓ centralizer (R : Set M11) = ⊥) :
    Nat.card (automizer (S : Subgroup M11) R) = 16 := by
  let f := R.normalizerMonoidHom.comp (inclusion
    (show (S : Subgroup M11) ⊓ normalizer R ≤ normalizer R from inf_le_right))
  have hinj : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro g hg
    have hker : inclusion inf_le_right g ∈ R.normalizerMonoidHom.ker := hg
    rw [normalizerMonoidHom_ker] at hker
    have he : (g : M11) ∈ (S : Subgroup M11) ⊓ centralizer (R : Set M11) :=
      ⟨g.property.1, hker⟩
    rw [hC] at he
    exact Subtype.ext he
  change Nat.card f.range = 16
  calc
    Nat.card f.range = Nat.card ((S : Subgroup M11) ⊓ normalizer R : Subgroup M11) :=
      (Nat.card_congr (Equiv.ofBijective f.rangeRestrict
        ⟨(MonoidHom.rangeRestrict_injective_iff).mpr hinj,
          MonoidHom.rangeRestrict_surjective _⟩)).symm
    _ = 16 := by rw [inf_eq_left.mpr hN]; exact sylow_two_card S

private theorem sylow_normalizes_nine (S : Sylow 2 M11) (R : Subgroup M11)
    [IsMulCommutative R] (hR : IsPGroup 3 R) (hc : Nat.card R = 9)
    (hperm : (R : Set M11) * (S : Set M11) = (S : Set M11) * (R : Set M11)) :
    (S : Subgroup M11) ≤ normalizer R ∧
      (S : Subgroup M11) ⊓ centralizer (R : Set M11) = ⊥ := by
  have hd : Disjoint R (S : Subgroup M11) :=
    hR.disjoint_of_coprime S.isPGroup' (by decide)
  have hprod := card_set_mul_mul_card_inf R (S : Subgroup M11)
  rw [hd.eq_bot, card_bot, mul_one,
    ← coe_sup_of_set_mul_comm R (S : Subgroup M11) hperm, sylow_two_card S,
    hc] at hprod
  have hprod' : Nat.card (R ⊔ (S : Subgroup M11) : Subgroup M11) = 144 := hprod
  obtain ⟨x, hx⟩ := exists_nine_orbit R hR hc
  have hstab : (S : Subgroup M11) ≤ stabilizer M11 (orbit R x) :=
    le_sup_right.trans (le_nine_stabilizer le_sup_left hx hprod')
  have hN := normalizer_nine_card R hc
  have hNeq : normalizer (R : Set M11) = stabilizer M11 (orbit R x) :=
    eq_of_le_of_card_ge (le_nine_stabilizer R.le_normalizer hx hN)
      (by rw [hN, nine_stabilizer_card _ hx])
  exact ⟨hNeq ▸ hstab, two_centralizer_eq_bot _ R S.isPGroup' hx hstab⟩

/-- Every permutable Sylow-two/odd-complement pair in M₁₁ has an induced
conjugation automizer of order sixteen. -/
public theorem mathieuEleven_automizer_card (S : Sylow 2 M11) (R : Subgroup M11)
    (hR : XiOddQuotient 3 R)
    (hperm : (R : Set M11) * (S : Set M11) = (S : Set M11) * (R : Set M11)) :
    Nat.card (automizer (S : Subgroup M11) R) = 16 := by
  rcases hR with ⟨he, hc⟩ | ⟨_, hc, _⟩
  · let _ := he
    have hRp : IsPGroup 3 R := IsPGroup.of_card hc
    have hnine : Nat.card R = 9 := hc
    obtain ⟨hN, hC⟩ := sylow_normalizes_nine S R hRp hnine hperm
    exact automizer_card_of_normalizes S R hN hC
  · have hd := R.card_subgroup_dvd_card
    rw [hc, m11_order] at hd
    norm_num at hd

/-- The concrete M₁₁ restriction used to exclude its actual D₈ complement
 action in the contrary Sylow configuration. -/
public theorem mathieuEleven_restriction : Restriction M11 := by
  intro S R hR hperm
  exact Or.inr (by
    simpa only [mathieuEleven_automizer_card S R hR hperm] using (dvd_refl 16))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.SmallModels
