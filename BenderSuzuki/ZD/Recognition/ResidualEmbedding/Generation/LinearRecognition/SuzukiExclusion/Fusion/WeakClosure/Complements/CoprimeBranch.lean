module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Interfaces
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Bounds
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Cardinality
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ElementaryBranch
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Complements.Coordinates
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity.OddNormalizer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowObstruction
public import Theory.GroupTheory.NormalizedSupCard
public import FeitThompson.GroupAction.NoncyclicAbelianPGroup


/-!
# Coprime centralizers and the Suzuki invariant complement

Choose a common prime divisor of the orders of the cyclic groups K and Y.
Their commuting prime-order subgroups give an elementary abelian actor of
order p² on S. Coprime fixed-point generation supplies a centralizer outside
T. The pure K and Y centralizers lie in T by Sylow maximality, so the actor
is mixed. The direct product T = PU and the two fixed-point-free actions
then give C_T(xy) = 1.

The actual centralizer A = C_S(xy) is normalized by K and Y. Transitivity
of K on the nonidentity cosets of T gives the literal carrier product
S = TA. The quotient map embeds A into S/T, identified with M° through
the commutator coordinates, proving that A is elementary abelian.

This proves the conditional complement branch of GLS4, Chapter 2,
Lemma 14.7(a), `refs/KGroup/GLS4/Chapter2.tex`, lines 2571–2585. The
independently produced torus action and the permitted cyclicity, order
and fixed-point restrictions on Y remain explicit. Their discharge belongs
to the enclosing source assembly.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

omit [Finite G] in
private theorem sylow_intersection_le {H S R : Subgroup G}
    (hS : IsPGroup 2 S) (hRS : R ≤ S)
    (hR : ∃ V : Sylow 2 H, (V : Subgroup H).map H.subtype = R) :
    S ⊓ H ≤ R := by
  obtain ⟨V, hV⟩ := hR
  have hVS : (V : Subgroup H) ≤ S.subgroupOf H := by
    intro x hx
    exact hRS (hV ▸ mem_map_of_mem H.subtype hx)
  have he := V.is_maximal' (hS.comap_subtype (K := H)) hVS
  intro x hx
  have hm : (⟨x, hx.2⟩ : H) ∈ (V : Subgroup H) := he ▸ hx.1
  exact hV ▸ mem_map_of_mem H.subtype hm

private theorem S_two (g : LocalGeometry Z M z t m) (s : SylowGeometry g) :
    IsPGroup 2 g.S := by
  obtain ⟨V, hV⟩ := s.S_sylow
  exact hV ▸ V.isPGroup'

private theorem torus_fixed_mem_U (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) (hsemi : TorusSemiregular M t)
    {x a : G} (hx : x ∈ residualCommutator M t) (hx1 : x ≠ 1)
    (ha : a ∈ g.S) (hac : Commute a x) : a ∈ g.U := by
  apply sylow_intersection_le (S_two g s) g.U_le_S g.U_sylow_pair
  exact ⟨ha, d.torus_centralizer_le_pair hsemi hx hx1
    ⟨g.S_le_M ha, mem_centralizer_singleton_iff.mpr hac.eq⟩⟩

private theorem centralizer_fixed_mem_T (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) {y a : G}
    (hy : y ∈ centralizer (residualGenerated M z t : Set G)) (hy1 : y ≠ 1)
    (ha : a ∈ g.S) (hac : Commute a y) : a ∈ g.T := by
  apply sylow_intersection_le (S_two g s) g.T_lt_S.le g.T_sylow
  refine ⟨ha, g.normalizer_control (zpowers y) (zpowers_le.mpr hy) ?_ ?_⟩
  · intro he
    exact hy1 (mem_bot.mp (he ▸ mem_zpowers y))
  · apply Subgroup.centralizer_le_normalizer
    rw [zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr hac.eq

omit [Finite G] in
private theorem torus_commute_centralizer {x y : G}
    (hx : x ∈ residualCommutator M t)
    (hy : y ∈ centralizer (residualGenerated M z t : Set G)) : Commute x y :=
  mem_centralizer_iff.mp hy x ((show residualCommutator M t ≤
    residualGenerated M z t from le_sup_right) hx)

private theorem torus_disjoint_centralizer (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) (hsemi : TorusSemiregular M t) :
    Disjoint (residualCommutator M t) (centralizer (residualGenerated M z t : Set G)) := by
  apply disjoint_def.mpr
  intro x hxK hxJ
  by_contra hx1
  have hA : closure (Z ∩ (M : Set G)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    apply mem_bot.mpr
    apply disjoint_def.mp g.closure_disjoint_U ha
    exact torus_fixed_mem_U d g s hsemi hxK hx1 (g.closure_le_S ha)
      (mem_centralizer_iff.mp hxJ a ((show closure (Z ∩ (M : Set G)) ≤
        residualGenerated M z t from g.closure_le_P.trans (by rw [g.P_eq]; exact inf_le_right)) ha))
  have hc := (d.closure_elementary_card g).2
  rw [hA, card_bot] at hc
  have : 1 < 2 ^ (2 * m + 1) := one_lt_pow₀ (by omega) (by omega)
  omega

private theorem Y_normalizes (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (Y : Subgroup G) (hY : Y ≤ centralizer (residualGenerated M z t : Set G))
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal) :
    Y ≤ normalizer (g.T : Set G) ∧ Y ≤ normalizer (g.S : Set G) := by
  have hYP : Y ≤ normalizer (borelTwoCore M z t : Set G) :=
    (hY.trans (centralizer_le (by rw [g.P_eq]; exact inf_le_right))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hYU : Y ≤ normalizer (g.U : Set G) :=
    hY.trans ((normal_subgroupOf_iff_le_normalizer g.U_le_centralizer).mp hU)
  have hTeq : g.T = borelTwoCore M z t ⊔ g.U := by
    apply le_antisymm
    · intro a ha
      obtain ⟨p, hp, u, hu, rfl⟩ := (Set.ext_iff.mp g.T_product a).mp ha
      exact mul_mem_sup hp hu
    · exact sup_le (by rw [g.P_eq]; exact inf_le_left) g.U_le_T
  have hYT : Y ≤ normalizer (g.T : Set G) := by
    rw [hTeq]
    exact (le_inf hYP hYU).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  refine ⟨hYT, hYT.trans ?_⟩
  have hSN : g.S ≤ normalizer (g.T : Set G) := by
    obtain ⟨V, hV⟩ := g.S_sylow
    rw [← hV]
    exact map_subtype_le _
  exact (normal_subgroupOf_iff_le_normalizer hSN).mp s.S_normal

private theorem mixed_fixed_trivial (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) (hsemi : TorusSemiregular M t)
    (hK : TorusQuotientAction g) (Y : Subgroup G)
    (hY : Y ≤ centralizer (residualGenerated M z t : Set G))
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal)
    (hfree : ∀ y ∈ Y, y ≠ 1 → ∀ u ∈ g.U, Commute u y → u = 1)
    {x y a : G} (hx : x ∈ residualCommutator M t) (hx1 : x ≠ 1)
    (hy : y ∈ Y) (hy1 : y ≠ 1) (ha : a ∈ g.T) (hac : Commute a (x * y)) : a = 1 := by
  obtain ⟨p, hp, u, hu, rfl⟩ := (Set.ext_iff.mp g.T_product a).mp ha
  have hxL : x ∈ residualGenerated M z t :=
    (show residualCommutator M t ≤ residualGenerated M z t from le_sup_right) hx
  have hpL : p ∈ residualGenerated M z t := (g.P_eq ▸ hp).2
  have hxp : MulAut.conj x p ∈ borelTwoCore M z t := by
    rw [g.P_eq]
    exact ⟨(mem_normalizer_iff.mp (hK.normalizes_T hx) p).mp ((g.P_eq ▸ hp).1),
      (residualGenerated M z t).mul_mem
        ((residualGenerated M z t).mul_mem hxL hpL)
        ((residualGenerated M z t).inv_mem hxL)⟩
  have hyu : MulAut.conj y u ∈ g.U :=
    (mem_normalizer_iff.mp (((normal_subgroupOf_iff_le_normalizer
      g.U_le_centralizer).mp hU) (hY hy)) u).mp hu
  have hyp : Commute y p := (mem_centralizer_iff.mp (hY hy) p hpL).symm
  have hypfix : MulAut.conj y p = p := by
    simp only [MulAut.conj_apply, hyp.eq, mul_inv_cancel_right]
  have hxyu := torus_commute_centralizer hx (g.U_le_centralizer hyu)
  have hxyufix : MulAut.conj x (MulAut.conj y u) = MulAut.conj y u := by
    exact mul_inv_eq_iff_eq_mul.mpr hxyu.eq
  have he : MulAut.conj x p * MulAut.conj y u = p * u := by
    calc
      _ = MulAut.conj x (MulAut.conj y (p * u)) := by
        rw [map_mul, hypfix, map_mul, hxyufix]
      _ = MulAut.conj (x * y) (p * u) := by
        simp only [MulAut.conj_apply]; group
      _ = p * u := by simp only [MulAut.conj_apply, hac.symm.eq, mul_inv_cancel_right]
  have hcoord : (⟨MulAut.conj x p, hxp⟩, ⟨MulAut.conj y u, hyu⟩) =
      ((⟨p, hp⟩, ⟨u, hu⟩) : borelTwoCore M z t × g.U) :=
    mul_injective_of_disjoint g.P_disjoint_U he
  have hpfix : MulAut.conj x p = p := congrArg (fun v => (v.1 : G)) hcoord
  have hufix : MulAut.conj y u = u := congrArg (fun v => (v.2 : G)) hcoord
  have hp1 : p = 1 := disjoint_def.mp g.P_disjoint_U hp
    (torus_fixed_mem_U d g s hsemi hx hx1 (g.T_lt_S.le ((g.P_eq ▸ hp).1))
      (mul_inv_eq_iff_eq_mul.mp hpfix).symm)
  have hu1 := hfree y hy hy1 u hu (mul_inv_eq_iff_eq_mul.mp hufix).symm
  simp only [hp1, hu1, one_mul]

private theorem exists_fixed_outside {p : ℕ} [Fact p.Prime]
    (S T B : Subgroup G) [IsElementaryAbelian p B]
    (hBT : Nat.card B = p ^ 2) (hcop : Nat.Coprime p (Nat.card S))
    (hn : B ≤ normalizer (S : Set G)) (hlt : T < S) :
    ∃ w ∈ B, w ≠ 1 ∧ ∃ a ∈ S, a ∉ T ∧ Commute a w := by
  classical
  let : Fact (IsPGroup p B) := ⟨IsElementaryAbelian.isPGroup p B⟩
  let : MulDistribMulAction B S := conjMulDistribMulActionOfLeNormalizer B S hn
  have hgen := iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := S) (A := B) p hcop (IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hBT)
  by_contra! hnone
  have hle : (⊤ : Subgroup S) ≤ T.subgroupOf S := by
    rw [← hgen]
    refine iSup₂_le fun w hw => ?_
    intro a ha
    have hf := congrArg Subtype.val (ha (⟨w, mem_zpowers w⟩ : zpowers w))
    change (w : G) * (a : G) * (w : G)⁻¹ = a at hf
    by_contra haT
    exact hnone w w.property (fun he => hw (Subtype.ext he)) a a.property haT
      (mul_inv_eq_iff_eq_mul.mp hf).symm
  exact hlt.not_ge (fun a ha => hle (mem_top (⟨a, ha⟩ : S)))

private theorem exists_mixed_fixed_outside (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) (hsemi : TorusSemiregular M t)
    (hK : TorusQuotientAction g) (Y : Subgroup G)
    (hY : Y ≤ centralizer (residualGenerated M z t : Set G)) (hYne : Y ≠ ⊥)
    (hYodd : Odd (Nat.card Y)) (hYdvd : Nat.card Y ∣ 2 ^ (2 * m + 1) - 1)
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal) :
    ∃ x ∈ residualCommutator M t, x ≠ 1 ∧ ∃ y ∈ Y, y ≠ 1 ∧
      ∃ a ∈ g.S, a ∉ g.T ∧ Commute a (x * y) := by
  obtain ⟨p, hp, hpY⟩ := Nat.exists_prime_and_dvd
    (ne_of_gt ((one_lt_card_iff_ne_bot Y).mpr hYne))
  let : Fact p.Prime := ⟨hp⟩
  have hpK : p ∣ Nat.card (residualCommutator M t) := by
    rw [d.torus_structure.2.2.1]
    exact dvd_trans hpY hYdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := residualCommutator M t) p hpK
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Y) p hpY
  let X := zpowers (x : G)
  let V := zpowers (y : G)
  have hXK : X ≤ residualCommutator M t := zpowers_le.mpr x.property
  have hVY : V ≤ Y := zpowers_le.mpr y.property
  have hc : V ≤ centralizer (X : Set G) := by
    intro b hb a ha
    exact torus_commute_centralizer (hXK ha) (hY (hVY hb))
  have hnorm : V ≤ normalizer (X : Set G) := hc.trans (Subgroup.centralizer_le_normalizer _)
  have hd : Disjoint X V := (torus_disjoint_centralizer d g s hsemi).mono hXK (hVY.trans hY)
  have hxc : Nat.card X = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hyc : Nat.card V = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy]
  let : IsElementaryAbelian p X := IsElementaryAbelian.zpowers_of_pow_eq_one (by
    have he : orderOf (x : G) = p := by rwa [Subgroup.orderOf_coe]
    rw [← he]; exact pow_orderOf_eq_one _)
  let : IsElementaryAbelian p V := IsElementaryAbelian.zpowers_of_pow_eq_one (by
    have he : orderOf (y : G) = p := by rwa [Subgroup.orderOf_coe]
    rw [← he]; exact pow_orderOf_eq_one _)
  let : IsElementaryAbelian p (X ⊔ V : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hc
  have hcard : Nat.card (X ⊔ V : Subgroup G) = p ^ 2 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint X V hnorm hd, hxc, hyc, pow_two]
  have hcop : Nat.Coprime p (Nat.card g.S) := by
    obtain ⟨n, hn⟩ := (S_two g s).exists_card_eq
    rw [hn]
    exact (hYodd.of_dvd_nat hpY).coprime_two_right.pow_right n
  have hn : X ⊔ V ≤ normalizer (g.S : Set G) :=
    sup_le (hXK.trans hK.normalizes_S) (hVY.trans (Y_normalizes g s Y hY hU).2)
  obtain ⟨w, hw, hw1, a, ha, haT, hac⟩ := exists_fixed_outside g.S g.T (X ⊔ V)
    hcard hcop hn g.T_lt_S
  have hprod : w ∈ (X : Set G) * (V : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left X V hnorm]
    exact hw
  obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := hprod
  have hx₁ne : x₁ ≠ 1 := by
    intro he
    have hy₁ne : y₁ ≠ 1 := by simpa only [he, one_mul] using hw1
    exact haT (centralizer_fixed_mem_T g s (hY (hVY hy₁)) hy₁ne ha
      (by simpa only [he, one_mul] using hac))
  have hy₁ne : y₁ ≠ 1 := by
    intro he
    exact haT (g.U_le_T (torus_fixed_mem_U d g s hsemi (hXK hx₁) hx₁ne ha
      (by simpa only [he, mul_one] using hac)))
  exact ⟨x₁, hXK hx₁, hx₁ne, y₁, hVY hy₁, hy₁ne, a, ha, haT, hac⟩

private theorem elementary_of_disjoint_T (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (A : Subgroup G) (hAS : A ≤ g.S) (hd : Disjoint g.T A) :
    IsElementaryAbelian 2 A := by
  have hUne : g.U ≠ ⊥ := (one_lt_card_iff_ne_bot _).mp (by
    have := d.two_le_U_card g; omega)
  obtain ⟨u, hu, hu1⟩ := g.U.bot_or_exists_ne_one.resolve_left hUne
  let := s.T_normal
  let e := s.commutatorQuotientEquiv g u hu hu1
  let q := (QuotientGroup.mk' (g.T.subgroupOf g.S)).comp (inclusion hAS)
  have hqi : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    have haT : (a : G) ∈ g.T := (QuotientGroup.eq_one_iff (N := g.T.subgroupOf g.S) (inclusion hAS a)).mp ha
    exact disjoint_def.mp hd haT a.property
  let φ := e.toMonoidHom.comp q
  have hi : Function.Injective φ := e.injective.comp hqi
  let := (d.closure_elementary_card g).1
  refine {
    toIsMulCommutative := ⟨⟨fun a b => hi (by simp only [map_mul]; exact mul_comm _ _)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
  }
  intro a
  apply hi
  rw [map_pow, map_one]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (closure (Z ∩ (M : Set G)))) (φ a)

private theorem mixed_centralizer_normalizes (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) (hK : TorusQuotientAction g)
    (Y : Subgroup G) (hY : Y ≤ centralizer (residualGenerated M z t : Set G))
    (hYcyc : IsCyclic Y)
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal)
    {x y : G} (hx : x ∈ residualCommutator M t) (hy : y ∈ Y) :
    residualCommutator M t ⊔ Y ≤
      normalizer ((g.S ⊓ centralizer ({x * y} : Set G) : Subgroup G) : Set G) := by
  let := d.torus_structure.2.1
  let := hYcyc
  have hnS : residualCommutator M t ⊔ Y ≤ normalizer (g.S : Set G) :=
    sup_le hK.normalizes_S (Y_normalizes g s Y hY hU).2
  have hc : residualCommutator M t ⊔ Y ≤ centralizer ({x * y} : Set G) := by
    apply sup_le
    · intro k hk
      have hkk : Commute k x := congrArg Subtype.val
        (mul_comm (⟨k, hk⟩ : residualCommutator M t) ⟨x, hx⟩)
      exact mem_centralizer_singleton_iff.mpr
        (hkk.mul_right (torus_commute_centralizer hk (hY hy))).eq
    · intro v hv
      have hvy : Commute v y := congrArg Subtype.val (mul_comm (⟨v, hv⟩ : Y) ⟨y, hy⟩)
      exact mem_centralizer_singleton_iff.mpr
        ((torus_commute_centralizer hx (hY hv)).symm.mul_right hvy).eq
  exact (le_inf hnS (hc.trans (centralizer ({x * y} : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

private theorem product_of_torus_transitive (g : LocalGeometry Z M z t m)
    (hK : TorusQuotientAction g) (A : Subgroup G) (hAS : A ≤ g.S)
    (hn : residualCommutator M t ≤ normalizer (A : Set G))
    {a : G} (ha : a ∈ A) (haT : a ∉ g.T) :
    (g.S : Set G) = (g.T : Set G) * (A : Set G) := by
  ext b
  constructor
  · intro hb
    by_cases hbT : b ∈ g.T
    · exact ⟨b, hbT, 1, A.one_mem, mul_one _⟩
    obtain ⟨k, hk, he⟩ := hK.transitive a (hAS ha) haT b hb hbT
    refine ⟨b * (MulAut.conj k a)⁻¹, he, MulAut.conj k a,
      (mem_normalizer_iff.mp (hn hk) a).mp ha, ?_⟩
    exact inv_mul_cancel_right _ _
  · rintro ⟨v, hv, c, hc, rfl⟩
    exact g.S.mul_mem (g.T_lt_S.le hv) (hAS hc)

/-- GLS4, Chapter 2, Lemma 14.7(a), with the independently produced torus
quotient action and the permitted Suzuki model restrictions explicit.
The complement is the actual centralizer in S of a mixed prime-order actor. -/
public theorem invariantElementaryComplement_of_torusQuotientAction
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hsemi : TorusSemiregular M t)
    (_f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (_hf : Function.Injective _f) (s : SylowGeometry g)
    (Y : Subgroup G) (hY : Y ≤ centralizer (residualGenerated M z t : Set G))
    (hYne : Y ≠ ⊥) (hYodd : Odd (Nat.card Y))
    (_hproduct : (centralizer (residualGenerated M z t : Set G) : Set G) =
      (g.U : Set G) * (Y : Set G))
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal)
    (hYcyc : IsCyclic Y) (hYdvd : Nat.card Y ∣ 2 ^ (2 * m + 1) - 1)
    (hfree : ∀ y ∈ Y, y ≠ 1 → ∀ u ∈ g.U, Commute u y → u = 1)
    (hK : TorusQuotientAction g) : InvariantElementaryComplement g Y := by
  obtain ⟨x, hx, hx1, y, hy, hy1, a, ha, haT, hac⟩ :=
    exists_mixed_fixed_outside d g s hsemi hK Y hY hYne hYodd hYdvd hU
  let A := g.S ⊓ centralizer ({x * y} : Set G)
  have hAS : A ≤ g.S := inf_le_left
  have hAn : residualCommutator M t ⊔ Y ≤ normalizer (A : Set G) :=
    mixed_centralizer_normalizes d g s hK Y hY hYcyc hU hx hy
  have hd : Disjoint g.T A := by
    apply disjoint_def.mpr
    intro b hb hbA
    exact mixed_fixed_trivial d g s hsemi hK Y hY hU hfree hx hx1 hy hy1 hb
      (mem_centralizer_singleton_iff.mp hbA.2)
  refine ⟨A, hAS, elementary_of_disjoint_T d g s A hAS hd, hd, ?_, hAn⟩
  exact product_of_torus_transitive g hK A hAS (le_sup_left.trans hAn)
    ⟨ha, mem_centralizer_singleton_iff.mpr hac.eq⟩ haT

end BenderSuzuki.ZD.SuzukiExclusion
