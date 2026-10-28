module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.Basic
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The actual component projection in the L₃(2) branch

For K in the genuine Y_z family, the T_v-invariance conclusion of 13.6.14
makes K+ normal in the entire plus actor. Conjugation by the two-perfect
L_v therefore gives an action on K+. Its outer action is trivial because
Out(L₃(2)) has order two. Centerlessness then constructs the component
projection, with an explicit conjugation identity on the literal plus map.

The projection is equivariant for T_v and has nontrivial range whenever
[K+,L_v+] is nonzero. Its kernel is computed as the inverse image of the
centralizer of K+. The earlier cubic core quotient proves that the kernel
of every nontrivial image of L_v is a two-group, and that its image still
has cubic quotient by its two-core.

These are constructions inside the noncentral branch, not a proof of
13.6.20. The central doubled-natural configuration and the lift from the
projection back to L_v ≤ K remain necessary source arguments. In
particular the kernel of the entire plus action is not declared to be a
two-group, and equality of quotient images is not used as a containment lift.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Lemma 13.6.20,
printed p.931; the earlier residual calculation on p.926 and 13.6.14, p.929.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree
open ComponentSelection
variable {G : Type*} [Group G]

/-- Under the actual invariance conclusion of 13.6.14, K+ is normal in
its full plus actor, including L_v+ and T_v+. -/
theorem plus_component_normal (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G)) :
    (plusImage K L T z v hL hz K).Normal := by
  have hs := starImage_Kminus_normal_in_actor K L T z v hK
  rw [Kminus_eq_of_invariant K T v hn] at hs
  have hm := hs.map (starToPlus K L T z v hK.1.1 hL hz)
    (starToPlus_surjective K L T z v hK.1.1 hL hz)
  rwa [starToPlus_image K L T z v hK.1.1 hL hz K (K_le_plusActor K L T v)] at hm

/-- The restriction of the literal plus quotient to L_v. -/
def residualPlusMap (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    Lv L v →* Gplus K L T z v hL hz :=
  (plusMk K L T z v hL hz).comp (inclusion (le_sup_right.trans le_sup_left))

theorem residualPlusMap_range (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    (residualPlusMap K L T z v hL hz).range =
      plusImage K L T z v hL hz (Lv L v) := by
  ext x
  constructor
  · rintro ⟨l, rfl⟩
    exact mem_map.mpr ⟨inclusion (le_sup_right.trans le_sup_left) l, l.property, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩

/-- The kernel on L_v is the actual relative centralizer of W_K. -/
theorem residualPlusMap_ker (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    (residualPlusMap K L T z v hL hz).ker =
      (centralizer (WK K L T z v : Set G)).subgroupOf (Lv L v) := by
  rw [residualPlusMap, ← MonoidHom.comap_ker, plusMk_ker]
  rfl

private theorem exists_inner_lift {D C : Type*} [Group D] [Group C]
    (hD : IsPPerfect 2 D) (a : D →* MulAut C)
    (e : C ≃* Matrix.PSL3Two.SL) :
    ∃ f : D →* C, (MulAut.conj : C →* MulAut C).comp f = a := by
  let b := (MulAut.congr e).toMonoidHom.comp a
  let q := QuotientGroup.mk' (MulAut.innerSubgroup Matrix.PSL3Two.SL)
  have ht : q.comp b = 1 := hD.hom_eq_one_of_isPGroup
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup (q.comp b)
  have hi : ∀ d, b d ∈ MulAut.innerSubgroup Matrix.PSL3Two.SL := by
    intro d
    exact (QuotientGroup.eq_one_iff _).mp
      (congrArg (fun f : D →* MulAut.Outer Matrix.PSL3Two.SL => f d) ht)
  let j : Matrix.PSL3Two.SL ≃* MulAut.innerSubgroup Matrix.PSL3Two.SL :=
    MonoidHom.ofInjective
      (MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot)
  let f := e.symm.toMonoidHom.comp (j.symm.toMonoidHom.comp (b.codRestrict _ hi))
  refine ⟨f, ?_⟩
  apply MonoidHom.ext
  intro d
  apply (MulAut.congr e).injective
  change MulAut.congr e (MulAut.conj (f d)) = b d
  rw [MulAut.congr_conj]
  have he : e (f d) = j.symm ⟨b d, hi d⟩ := e.apply_symm_apply _
  rw [he]
  exact congrArg Subtype.val (j.apply_symm_apply ⟨b d, hi d⟩)

private theorem component_conj_injective {C : Type*} [Group C]
    (e : C ≃* Matrix.PSL3Two.PSL) : Function.Injective (MulAut.conj : C →* MulAut C) := by
  let es := e.trans Matrix.PSL3Two.equiv.symm
  intro x y h
  apply es.injective
  apply MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
  rw [← MulAut.congr_conj es x, ← MulAut.congr_conj es y, h]

/-- Construct the actual projection of L_v onto K+ from its conjugation
action. Two-perfectness kills the outer action of order two. The displayed
identity determines the projection; no projection or containment is an input. -/
theorem exists_component_projection [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* Matrix.PSL3Two.PSL) :
    ∃ f : Lv L v →* plusImage K L T z v hL hz K,
      ∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
        (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
          residualPlusMap K L T z v hL hz l * k *
            (residualPlusMap K L T z v hL hz l)⁻¹ := by
  let N := plusImage K L T z v hL hz K
  let : N.Normal := plus_component_normal K L T z v hL hz hK hn
  let a : Lv L v →* MulAut N :=
    (MulAut.conjNormal : Gplus K L T z v hL hz →* MulAut N).comp
      (residualPlusMap K L T z v hL hz)
  obtain ⟨f, hf⟩ := exists_inner_lift
    (isPPerfect_embedded_pResidual 2 (L ⊓ Gv v)) a (e.trans Matrix.PSL3Two.equiv.symm)
  refine ⟨f, fun l k => ?_⟩
  exact congrArg (fun b : Lv L v →* MulAut N => ((b l k : N) : Gplus K L T z v hL hz)) hf

/-- The source projection is nontrivial as soon as the plus commutator is
nonzero. This uses its action identity, not an assumed image equality. -/
theorem projection_range_ne_bot (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (f : Lv L v →* plusImage K L T z v hL hz K)
    (hf : ∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
      (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
        residualPlusMap K L T z v hL hz l * k *
          (residualPlusMap K L T z v hL hz l)⁻¹)
    (hc : ⁅plusImage K L T z v hL hz K,
      plusImage K L T z v hL hz (Lv L v)⁆ ≠ ⊥) : f.range ≠ ⊥ := by
  intro hb
  apply hc
  rw [commutator_eq_bot_iff_le_centralizer, le_centralizer_iff,
    ← residualPlusMap_range K L T z v hL hz]
  rintro _ ⟨l, rfl⟩
  rw [mem_centralizer_iff]
  intro k hk
  have hfl : f l = 1 := mem_bot.mp (hb ▸ (show f l ∈ f.range from ⟨l, rfl⟩))
  have h := hf l ⟨k, hk⟩
  rw [hfl] at h
  simp only [coe_one, one_mul, inv_one, mul_one] at h
  exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm

/-- The projection preserves two-perfectness. This is needed when
recognizing its image as the residual of a parabolic. -/
theorem projection_range_twoPerfect [Finite G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (f : Lv L v →* plusImage K L T z v hL hz K) : IsPPerfect 2 f.range :=
  (isPPerfect_embedded_pResidual 2 (L ⊓ Gv v)).of_surjective
    f.rangeRestrict f.rangeRestrict_surjective

/-- The kernel of the component projection is exactly the inverse image
of the centralizer of K+ under the literal residual plus map. -/
theorem projection_ker (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* Matrix.PSL3Two.PSL)
    (f : Lv L v →* plusImage K L T z v hL hz K)
    (hf : ∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
      (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
        residualPlusMap K L T z v hL hz l * k *
          (residualPlusMap K L T z v hL hz l)⁻¹) :
    f.ker = (centralizer (plusImage K L T z v hL hz K : Set _)).comap
      (residualPlusMap K L T z v hL hz) := by
  ext l
  change f l = 1 ↔ residualPlusMap K L T z v hL hz l ∈ centralizer _
  rw [mem_centralizer_iff]
  constructor
  · intro hfl k hk
    have h := hf l ⟨k, hk⟩
    rw [hfl] at h
    simp only [coe_one, one_mul, inv_one, mul_one] at h
    exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm
  · intro hc
    apply component_conj_injective e
    rw [map_one]
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    change (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ = k
    rw [hf, ← hc k k.property, mul_inv_cancel_right]

/-- The constructed projection respects conjugation by the original T_v.
In particular its range is an invariant subgroup of K+; no diagonal or
parabolic image is assumed. -/
theorem projection_equivariant (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* Matrix.PSL3Two.PSL)
    (f : Lv L v →* plusImage K L T z v hL hz K)
    (hf : ∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
      (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
        residualPlusMap K L T z v hL hz l * k *
          (residualPlusMap K L T z v hL hz l)⁻¹)
    (t : Tv T v) (l : Lv L v) :
    (f (conjugationAction (Lv L v) (Tv T v) hL t l) : Gplus K L T z v hL hz) =
      plusMk K L T z v hL hz (inclusion le_sup_right t) * f l *
        (plusMk K L T z v hL hz (inclusion le_sup_right t))⁻¹ := by
  let N := plusImage K L T z v hL hz K
  let q := residualPlusMap K L T z v hL hz
  let a := plusMk K L T z v hL hz (inclusion le_sup_right t)
  have hN := plus_component_normal K L T z v hL hz hK hn
  let b : N := ⟨a * f l * a⁻¹, hN.conj_mem (f l) (f l).property a⟩
  have hq : q (conjugationAction (Lv L v) (Tv T v) hL t l) = a * q l * a⁻¹ := by
    let ta : plusActor K L T v := ⟨t, (show Tv T v ≤ plusActor K L T v from le_sup_right) t.property⟩
    let la : plusActor K L T v := ⟨l,
      (show Lv L v ≤ plusActor K L T v from le_sup_right.trans le_sup_left) l.property⟩
    calc
      _ = plusMk K L T z v hL hz (ta * la * ta⁻¹) := rfl
      _ = _ := by rw [map_mul, map_mul, map_inv]; rfl
  have he : f (conjugationAction (Lv L v) (Tv T v) hL t l) = b := by
    apply component_conj_injective e
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    have hk : a⁻¹ * k * a ∈ N := by
      simpa only [inv_inv] using hN.conj_mem k k.property a⁻¹
    have hh := hf l ⟨a⁻¹ * k * a, hk⟩
    change (f l : Gplus K L T z v hL hz) * (a⁻¹ * k * a) * (f l : Gplus K L T z v hL hz)⁻¹ =
      q l * (a⁻¹ * k * a) * (q l)⁻¹ at hh
    change (f (conjugationAction (Lv L v) (Tv T v) hL t l) : Gplus K L T z v hL hz) * k *
      (f (conjugationAction (Lv L v) (Tv T v) hL t l) : Gplus K L T z v hL hz)⁻¹ =
      (a * f l * a⁻¹) * k * (a * f l * a⁻¹)⁻¹
    rw [hf]
    change q (conjugationAction (Lv L v) (Tv T v) hL t l) * k *
      (q (conjugationAction (Lv L v) (Tv T v) hL t l))⁻¹ = _
    rw [hq]
    calc
      _ = a * (q l * (a⁻¹ * k * a) * (q l)⁻¹) * a⁻¹ := by group
      _ = a * ((f l : Gplus K L T z v hL hz) * (a⁻¹ * k * a) *
          (f l : Gplus K L T z v hL hz)⁻¹) * a⁻¹ := by rw [hh]
      _ = _ := by group
  exact congrArg Subtype.val he

/-- The ambient range of the projection is normalized by the literal T_v+
image. This is the invariance needed for the parabolic recognition. -/
theorem projection_range_normalized (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* Matrix.PSL3Two.PSL)
    (f : Lv L v →* plusImage K L T z v hL hz K)
    (hf : ∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
      (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
        residualPlusMap K L T z v hL hz l * k *
          (residualPlusMap K L T z v hL hz l)⁻¹) :
    plusImage K L T z v hL hz (Tv T v) ≤
      normalizer (f.range.map (plusImage K L T z v hL hz K).subtype : Set _) := by
  apply le_normalizer_iff.mpr
  rintro _ ⟨t, ht, rfl⟩ _ ⟨k, ⟨l, rfl⟩, rfl⟩
  have h := projection_equivariant K L T z v hL hz hK hn e f hf ⟨t, ht⟩ l
  change plusMk K L T z v hL hz t * f l * (plusMk K L T z v hL hz t)⁻¹ ∈ _
  change (f (conjugationAction (Lv L v) (Tv T v) hL ⟨t, ht⟩ l) :
    Gplus K L T z v hL hz) = plusMk K L T z v hL hz t * f l *
      (plusMk K L T z v hL hz t)⁻¹ at h
  rw [← h]
  exact mem_map.mpr ⟨_, ⟨_, rfl⟩, rfl⟩

private theorem kernel_le_twoCore {D C : Type*} [Group D] [Group C] [Finite D]
    (hp : IsPPerfect 2 D) (hc : Nat.card (D ⧸ pCore 2 D) = 3)
    (f : D →* C) (hf : f.range ≠ ⊥) : f.ker ≤ pCore 2 D := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsSimpleGroup (D ⧸ pCore 2 D) := isSimpleGroup_of_prime_card hc
  let q := QuotientGroup.mk' (pCore 2 D)
  have hn := (inferInstance : f.ker.Normal).map q (QuotientGroup.mk'_surjective _)
  rcases hn.eq_bot_or_eq_top with h | h
  · have hh := (map_eq_bot_iff f.ker).mp h
    simpa only [q, QuotientGroup.ker_mk'] using hh
  · have hs : f.ker ⊔ pCore 2 D = ⊤ := by
      have hh := congrArg (comap q) h
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
    have hk := hp f.ker inferInstance
      (isPGroup_quotient_of_sup_eq_top f.ker (pCore 2 D) pCore_isPGroup hs)
    apply (hf _).elim
    apply le_bot_iff.mp
    rintro _ ⟨d, rfl⟩
    exact MonoidHom.mem_ker.mp (hk.symm ▸ mem_top d)

/-- Every nontrivial image of the actual L_v has a two-group kernel,
using its earlier cubic core quotient and its intrinsic two-perfectness.
This does not assert that the plus quotient's entire kernel is a two-group. -/
theorem residual_image_kernel_le_twoCore [Finite G]
    {D : Type*} [Group D] (L : Subgroup G) (v : G)
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (f : Lv L v →* D) (hf : f.range ≠ ⊥) : f.ker ≤ pCore 2 (Lv L v) :=
  kernel_le_twoCore (isPPerfect_embedded_pResidual 2 (L ⊓ Gv v)) hc f hf

/-- The nontrivial projection retains the cubic quotient by its actual
two-core. The quotient isomorphism uses its proved two-group kernel. -/
theorem residual_image_core_quotient_card [Finite G]
    {D : Type*} [Group D] (L : Subgroup G) (v : G)
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (f : Lv L v →* D) (hf : f.range ≠ ⊥) :
    Nat.card (f.range ⧸ pCore 2 f.range) = 3 := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hk : IsPGroup 2 f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact pCore_isPGroup.to_le (residual_image_kernel_le_twoCore L v hc f hf)
  let e := f.rangeRestrict.pCoreQuotientEquiv f.rangeRestrict_surjective hk
  exact (Nat.card_congr e.toEquiv).symm.trans hc

/-- Construct the noncentral source projection, its invariant nontrivial
two-perfect image, its literal kernel bound, and its cubic core quotient.
The nonzero plus commutator is the branch premise. This theorem does not
lift containment to the original ambient group. -/
theorem exists_noncentral_projection [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* Matrix.PSL3Two.PSL)
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hcomm : ⁅plusImage K L T z v hL hz K,
      plusImage K L T z v hL hz (Lv L v)⁆ ≠ ⊥) :
    ∃ f : Lv L v →* plusImage K L T z v hL hz K,
      (∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
        (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
          residualPlusMap K L T z v hL hz l * k *
            (residualPlusMap K L T z v hL hz l)⁻¹) ∧
      f.range ≠ ⊥ ∧ IsPPerfect 2 f.range ∧ f.ker ≤ pCore 2 (Lv L v) ∧
      Nat.card (f.range ⧸ pCore 2 f.range) = 3 ∧
      plusImage K L T z v hL hz (Tv T v) ≤
        normalizer (f.range.map (plusImage K L T z v hL hz K).subtype : Set _) := by
  obtain ⟨f, hf⟩ := exists_component_projection K L T z v hL hz hK hn e
  have hne := projection_range_ne_bot K L T z v hL hz f hf hcomm
  exact ⟨f, hf, hne, projection_range_twoPerfect K L T z v hL hz f,
    residual_image_kernel_le_twoCore L v hc f hne,
    residual_image_core_quotient_card L v hc f hne,
    projection_range_normalized K L T z v hL hz hK hn e f hf⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree
