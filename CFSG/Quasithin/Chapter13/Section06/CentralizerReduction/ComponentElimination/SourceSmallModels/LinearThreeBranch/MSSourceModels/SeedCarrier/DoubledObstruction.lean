module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.SeedCarrier
public import Theory.Representation.PSL3Two.NaturalSylowFixed
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# The doubled-natural obstruction to the uniform seed equality

A Sylow subgroup of SL₃(2) fixes exactly one nonzero natural vector. Thus a
Sylow-fixed vector in W⊕W has its coordinates zero or equal. One of the two
projections or their difference is a nonzero equivariant map killing that
vector. Its kernel is a proper invariant subgroup.

In the actual marked A₅ setup, z belongs to ⟨v⟩[V,L_v], and K centralizes v.
The preceding seed-carrier module puts [V,L_v] inside sourceU. Factor z as a
power of v times u in sourceU. The actual Sylow in K fixes u; hence the
proper kernel above contains u and all its K-conjugates. It follows that
U_K=[W_K,K] is strictly smaller than sourceU in the doubled MS alternative.

This is a conditional obstruction to the uniform equality requested in the
source-realization interface. It does not assert that the doubled alternative
occurs under all standing hypotheses of 13.6.22. An equality proof must exclude
that alternative using stronger ambient facts. The downstream parabolic
argument only requires the proved marked-line containment, which remains valid.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.6.22,
printed p.932, and C.1.34(2), printed p.136; the marked seed splitting is on
printed p.926. The obstruction preserves both literal subgroup carriers.
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.SeedCarrier.DoubledObstruction
open BinaryLinearThree

-- A Sylow has at most one nonzero fixed natural vector. Thus the two
-- coordinates of a fixed vector in W ⊕ W are zero or equal.
private theorem fixed_pair_cases (S : Sylow 2 Group) (w : Vector × Vector)
    (hw : w ∈ fixedSpace (W.prod W) (S : Subgroup Group)) :
    w.1 = 0 ∨ w.2 = 0 ∨ w.1 = w.2 := by
  classical
  by_cases hx : w.1 = 0
  · exact Or.inl hx
  have hxS : w.1 ∈ fixedSpace W (S : Subgroup Group) :=
    fun s => congrArg Prod.fst (hw s)
  have hyS : w.2 ∈ fixedSpace W (S : Subgroup Group) :=
    fun s => congrArg Prod.snd (hw s)
  let f : Bool → fixedSpace W (S : Subgroup Group) :=
    fun b => if b then ⟨w.1, hxS⟩ else 0
  have hi : Function.Injective f := by
    intro a b he
    cases a <;> cases b <;> first | rfl | (exfalso; apply hx; simpa [f] using congrArg Subtype.val he) | (exfalso; apply hx; simpa [f] using (congrArg Subtype.val he).symm)
  have hs := (hi.bijective_of_nat_card_le
    (by simpa using card_sylow_natural_fixed_le_two S)).2
  obtain ⟨b, hb⟩ := hs ⟨w.2, hyS⟩
  cases b
  · exact Or.inr (Or.inl (by simpa [f] using (congrArg Subtype.val hb).symm))
  · exact Or.inr (Or.inr (by simpa [f] using congrArg Subtype.val hb))

private theorem fixed_annihilator (S : Sylow 2 Group) (w : Vector × Vector)
    (hw : w ∈ fixedSpace (W.prod W) (S : Subgroup Group)) :
    ∃ f : (Vector × Vector) →ₗ[ZMod 2] Vector, f ≠ 0 ∧ f w = 0 ∧
      ∀ g x, f ((W.prod W) g x) = W g (f x) := by
  let f₁ : (Vector × Vector) →ₗ[ZMod 2] Vector := LinearMap.fst _ _ _
  let f₂ : (Vector × Vector) →ₗ[ZMod 2] Vector := LinearMap.snd _ _ _
  rcases fixed_pair_cases S w hw with h | h | h
  · refine ⟨f₁, ?_, h, fun _ _ => rfl⟩
    intro he
    have hh := congrArg (fun f => f ((fun _ => 1), (0 : Vector))) he
    have := congrFun hh 0
    norm_num [f₁] at this
  · refine ⟨f₂, ?_, h, fun _ _ => rfl⟩
    intro he
    have hh := congrArg (fun f => f ((0 : Vector), (fun _ => 1))) he
    have := congrFun hh 0
    norm_num [f₂] at this
  · refine ⟨f₁ - f₂, ?_, ?_, ?_⟩
    · intro he
      have hh := congrArg (fun f => f ((fun _ => 1), (0 : Vector))) he
      have := congrFun hh 0
      norm_num [f₁, f₂] at this
    · change w.1 - w.2 = 0
      rw [h, sub_self]
    · intro g x
      exact (map_sub (W g) x.1 x.2).symm

open Subgroup Stellmacher
open scoped Pointwise
open ComponentSelection SourceContainment
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [_root_.Group G] [Finite G] {K L T U : Subgroup G} {z v : G}

omit [Finite G] in
private theorem kernel_obstruction
    (m : ConjugationQuotientModel K U (W.prod W))
    (hUK : U ≤ K) (hK : K ≤ Gv v)
    (a : G) (ha : a ∈ zpowers v) (u : U) (hz : z = a * (u : G))
    (S : Sylow 2 BinaryLinearThree.Group)
    (hu : Multiplicative.toAdd (m.quotient u) ∈ fixedSpace (W.prod W) (S : Subgroup BinaryLinearThree.Group)) :
    ⁅conjugateSpanBy (zpowers z) K, K⁆ ≠ U := by
  obtain ⟨f, hf, hfu, hfe⟩ := fixed_annihilator S _ hu
  let q : U →* Multiplicative Vector := f.toAddMonoidHom.toMultiplicative.comp m.quotient
  let D : Subgroup G := q.ker.map U.subtype
  have hDU : D ≤ U := map_subtype_le _
  have hstable (k : K) (x : U) (hx : x ∈ q.ker) :
      U.normalizerMonoidHom ⟨k, m.normalizes k.property⟩ x ∈ q.ker := by
    change f (Multiplicative.toAdd (m.quotient _)) = 0
    rw [m.equivariant]
    change f ((W.prod W) (m.actor k) (Multiplicative.toAdd (m.quotient x))) = 0
    rw [hfe]
    change f (Multiplicative.toAdd (m.quotient x)) = 0 at hx
    rw [hx, map_zero]
  have hconj (k : K) (x : G) (hx : x ∈ D) : (k : G) * x * (k : G)⁻¹ ∈ D := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨_, hstable k y hy, rfl⟩
  have hKD : K ≤ normalizer (D : Set G) := by
    intro k hk
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · exact hconj ⟨k, hk⟩ x
    · intro hx
      have hh := hconj (⟨k, hk⟩ : K)⁻¹ (k * x * k⁻¹) hx
      simpa only [Subgroup.coe_inv, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
  have hZ : zpowers v ≤ centralizer (K : Set G) := by
    apply le_centralizer_iff.mpr
    rw [zpowers_eq_closure, centralizer_closure]
    exact hK
  have hud : (u : G) ∈ D := ⟨u, hfu, rfl⟩
  have hseed : z ∈ zpowers v ⊔ D := by
    rw [hz]
    exact mul_mem ((show zpowers v ≤ zpowers v ⊔ D from le_sup_left) ha)
      ((show D ≤ zpowers v ⊔ D from le_sup_right) hud)
  have hle : ⁅conjugateSpanBy (zpowers z) K, K⁆ ≤ D :=
    commutator_seedSpan_le _ _ hZ
      ((hZ.trans (centralizer_le (hDU.trans hUK))).trans (Subgroup.centralizer_le_normalizer _))
      hKD hseed
  intro he
  have hall : ∀ x : U, q x = 1 := by
    intro x
    rw [he] at hle
    obtain ⟨y, hy, heq⟩ := hle x.property
    have hxy : y = x := Subtype.ext heq
    change q y = 1 at hy
    exact hxy ▸ hy
  apply hf
  apply LinearMap.ext
  intro w
  obtain ⟨x, hx⟩ := m.surjective (Multiplicative.ofAdd w)
  have hh := hall x
  change f (Multiplicative.toAdd (m.quotient x)) = 0 at hh
  change f w = 0
  rw [hx] at hh
  exact hh

/-- The source seed cannot fill two isomorphic natural summands. This uses
its actual marked factorization z∈⟨v⟩[V,L_v] and an actual Sylow in K. It is
an obstruction to the requested carrier equality in the doubled case,
not a counterexample to the full ambient 13.6.22 theorem. -/
theorem UK_ne_sourceU_of_doubled_model {V : Subgroup G}
    (s : A5Module.Marking L V)
    (d : EarlierData K L T (A5Module.markedZ s) (A5Module.markedV s))
    (hp : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (m : ConjugationQuotientModel K (sourceU K) (W.prod W))
    (hm : m.actor = linearThreeActor e) :
    UK K L T (A5Module.markedZ s) (A5Module.markedV s) ≠ sourceU K := by
  let v := A5Module.markedV s
  let z := A5Module.markedZ s
  have hUK : sourceU K ≤ K := (Subgroup.commutator_le_sup _ _).trans
    (sup_le (map_subtype_le _) le_rfl)
  have hZ : zpowers v ≤ centralizer (K : Set G) := by
    apply le_centralizer_iff.mpr
    rw [zpowers_eq_closure, centralizer_closure]
    exact d.component.1.1
  have hz : z ∈ zpowers v ⊔ sourceU K := by
    apply (sup_le_sup_left (marked_line_le_sourceU s d hp) (zpowers v))
    rw [← A5Module.Vv_eq_line_sup_commutator s]
    exact z_mem_Vv L z v
  have hprod : z ∈ (zpowers v : Set G) * (sourceU K : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _
      ((hZ.trans (centralizer_le hUK)).trans (Subgroup.centralizer_le_normalizer _))]
    exact hz
  obtain ⟨a, ha, u, hu, hzu⟩ := hprod
  obtain ⟨P, hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    d.component.1.2.2.1 (show K ≤ K ⊔ Tv T v from le_sup_left) d.component.1.2.1.subnormal
  have hsurj : Function.Surjective m.actor := hm ▸ linearThreeActor_surjective e
  let S : Sylow 2 BinaryLinearThree.Group := P.mapSurjective hsurj
  have hfixed : Multiplicative.toAdd (m.quotient ⟨u, hu⟩) ∈
      fixedSpace (W.prod W) (S : Subgroup BinaryLinearThree.Group) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk, rfl⟩ := hg
    have hkT : (k : G) ∈ Tv T v := (hP ▸ mem_map_of_mem K.subtype hk).1
    have hkz : (k : G) * z = z * (k : G) :=
      ((mem_omegaOneCenterAmbient_iff _ _).mp d.seedOmega).2.2 k hkT
    have hka : (k : G) * a = a * (k : G) :=
      mem_centralizer_iff.mp (hZ ha) k k.property
    have hku : (k : G) * u = u * (k : G) := by
      rw [← hzu, ← mul_assoc, hka, mul_assoc, mul_assoc] at hkz
      exact mul_left_cancel hkz
    have heq : (sourceU K).normalizerMonoidHom ⟨k, m.normalizes k.property⟩ ⟨u, hu⟩ =
        ⟨u, hu⟩ := by
      apply Subtype.ext
      change (k : G) * u * (k : G)⁻¹ = u
      rw [hku, mul_inv_cancel_right]
    have he := m.equivariant k ⟨u, hu⟩
    rw [heq] at he
    exact (congrArg Multiplicative.toAdd he).symm
  rw [UK, WK_eq_seedSpan d.normalizeK d.lv_le]
  exact kernel_obstruction m hUK d.component.1.1 a ha ⟨u, hu⟩ hzu.symm S hfixed

/-- In the actual whole-module alternative C.1.34(2), the seed carrier is
strictly smaller than the source center commutator. An assembly asserting
equality must first exclude this alternative; the downstream marking can
instead use the already proved containment of the source line in sourceU. -/
theorem UK_lt_sourceU_of_doubled_ms_section {V : Subgroup G}
    (s : A5Module.Marking L V)
    (d : EarlierData K L T (A5Module.markedZ s) (A5Module.markedV s))
    (hp : IsPPerfect 2 K) (hv : A5Module.markedV s ^ 2 = 1)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : HasSectionModel K (msQ K (Tv T (A5Module.markedV s))) ⊥
      (linearThreeActor e) (W.prod W)) :
    UK K L T (A5Module.markedZ s) (A5Module.markedV s) < sourceU K := by
  obtain ⟨_, ⟨m, hm⟩, _⟩ := doubled_ms_section_realization (A5Module.markedV s)
    d.component.1.1 hv d.component.1.2.1.subnormal hp e h
  exact lt_iff_le_and_ne.mpr
    ⟨d.UK_le_sourceU hp, UK_ne_sourceU_of_doubled_model s d hp e m hm⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.SeedCarrier.DoubledObstruction
