module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.OrdinaryCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.EvenModels
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.SourceAction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms
public import Theory.GroupTheory.AutomorphismTowerSimple
/-!
# Scalar Sylow actions exclude the remaining triality and Ree rows

Solvable Sylow control places the actual odd complement in the normalizer
of the component Sylow. Triality's simultaneous Cartan coordinates and
inner–coefficient decomposition make each normalizing Sylow actor a uniform
power map. For Ree, a two-power automorphism is inner; its representative
lies in the specified Sylow and centralizes the odd complement.

Frattini factorization transports these power maps through the actual
complement quotient and X/O₂,Φ(X). A power map commutes with every
automorphism. Thus a Sylow subgroup of the literal C_L(u) action would be
central, contradicting its surjection onto S₃. This closes both remaining
ordinary rows and combines with the characteristic-two exclusion. K,
K/O₂(K) and central quotients retain their original meanings; the ordinary
catalogue supplies simplicity of the whole component where it is used.

The centralizer and TI applications discharge the irreducible branch.
SieveActions is the earlier source input owned by qt-d-1317-module-orbits;
its discharge remains with this task's final assembly. The separate
reducible branch and Control are assembled by qt-d-1317-centralizer-sieve.
No remaining model, parabolic-marking or exclusion callback is assumed
by the irreducible contradiction.

Source: Aschbacher–Smith, 13.1.12(3), printed pp.874–875, using the actual
Cartan actions from A.3.15(5) and the argument of 1.3.4 on pp.510–511.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter1.XiEmbedding.InvariantLarge

private theorem no_symmetric_three_of_sylow_powers
    {A V : Type*} [Group A] [Finite A] [Group V]
    (ρ : A →* MulAut V) (S : Sylow 2 A)
    (hp : ∀ s : S, ∃ n : ℕ, ∀ v : V, ρ s v = v^n)
    (f : ρ.range →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f) : False := by
  let π := f.comp ρ.rangeRestrict
  have hπ : Function.Surjective π := hf.comp ρ.rangeRestrict_surjective
  let U := S.mapSurjective hπ
  have hU : (U : Subgroup (Equiv.Perm (Fin 3))) = ⊥ := by
    apply bot_unique
    rintro _ ⟨s,hs,rfl⟩
    have hc : π s ∈ center (Equiv.Perm (Fin 3)) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨a,rfl⟩ := hπ y
      have hcomm : ρ a * ρ s = ρ s * ρ a := by
        obtain ⟨n,hn⟩ := hp ⟨s,hs⟩
        ext v
        change ρ a (ρ s v) = ρ s (ρ a v)
        rw [hn,hn,map_pow]
      have he : ρ.rangeRestrict a * ρ.rangeRestrict s =
          ρ.rangeRestrict s * ρ.rangeRestrict a := Subtype.ext hcomm
      exact (map_mul f _ _).symm.trans ((congrArg f he).trans (map_mul f _ _))
    have hz : ∀ x : Equiv.Perm (Fin 3), (∀ y, y*x=x*y) → x=1 := by decide +kernel
    exact mem_bot.mpr (hz _ (mem_center_iff.mp hc))
  have hh := U.not_dvd_index
  rw [hU,index_bot] at hh
  exact hh (by norm_num [Nat.card_eq_fintype_card,Fintype.card_perm])

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- Scalar action by the actual selected Sylow is incompatible with the literal S₃ section. -/
theorem Context.not_symmetric_three_of_sylow_powers (h : Context T L p)
    {u : G} (s : Selected T L u)
    (hp : ∀ t : ((T : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G),
      ∃ n : ℕ, ∀ v, xiFrattiniAction _ (XiP p L)
        (XiP_invariant p (inf_le_left.trans h.sylow_normalizes)) t v = v^n)
    (hs : SymmetricThreeStabilizerQuotient L p u) : False := by
  let C := centralizer ({u} : Set G)
  let M := normalizer (L : Set G) ⊓ C
  let A := L ⊓ C
  have hAM : A ≤ M := inf_le_inf_right C L.le_normalizer
  let : (A.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer
    ((inf_le_inf_left (normalizer (L : Set G)) C.le_normalizer).trans
      inf_normalizer_le_normalizer_inf)
  have hS := IndexTwo.isSylowIn_inf_of_subnormal s.local_sylow hAM
    (inferInstance : (A.subgroupOf M).Normal).isSubnormal
  obtain ⟨R,hR⟩ := hS
  obtain ⟨f,hf⟩ := hs
  apply no_symmetric_three_of_sylow_powers (componentStabilizerFrattiniAction L p u) R _ f hf
  intro t
  have ht : (t.val : G) ∈ (T : Subgroup G) ⊓ C :=
    (hR ▸ mem_map_of_mem A.subtype t.property).1
  obtain ⟨n,hn⟩ := hp ⟨t.val,ht⟩
  refine ⟨n,?_⟩
  intro v
  exact hn v


/-- Two-power automorphisms preserving a specified Sylow and odd complement
act by uniform powers on that complement. Both remaining models prove this below. -/
@[expose] def ModelSylowPowers (p : ℕ) (D : Type*) [Group D] : Prop :=
  ∀ (S : Sylow 2 D) (B : Subgroup D), IsPGroup p B →
    B ≤ normalizer (S : Set D) → ∀ α : MulAut D,
    (∃ r : ℕ, α^(2^r)=1) → B.map α.toMonoidHom = B →
    (S : Subgroup D).map α.toMonoidHom = S →
    ∃ n : ℕ, ∀ b : B, α b = (b : D)^n

omit [Fact p.Prime] in
private theorem modelSylowPowers_of_equiv {D E : Type*} [Group D] [Group E] [Finite D]
    (j : D ≃* E) (hp : ModelSylowPowers p E) : ModelSylowPowers p D := by
  intro S B hB hBN α hα hαB hαS
  let U := S.mapSurjective (f := j.toMonoidHom) j.surjective
  let C := B.map j.toMonoidHom
  let β := MulAut.congr j α
  have hCN : C ≤ normalizer (U : Set E) := by
    change B.map j.toMonoidHom ≤ normalizer ((S : Subgroup D).map j.toMonoidHom : Set E)
    rw [←map_equiv_normalizer_eq]
    exact map_mono hBN
  have hm (X : Subgroup D) :
      (X.map j.toMonoidHom).map β.toMonoidHom = (X.map α.toMonoidHom).map j.toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    ext x
    simp [β]
  obtain ⟨n,hn⟩ := hp U C (hB.map _) hCN β
    (by obtain ⟨r,hr⟩ := hα; exact ⟨r,by rw [←map_pow,hr,map_one]⟩)
    (by rw [hm,hαB]) (by change ((S : Subgroup D).map j.toMonoidHom).map _ = _; rw [hm,hαS]; rfl)
  refine ⟨n,fun b => j.injective ?_⟩
  have he := hn ⟨j b,mem_map_of_mem j.toMonoidHom b.property⟩
  simpa [β,MulAut.congr] using he

private theorem triality_sylow_powers (P : Triality.Standard.Parameters)
    {n : ℕ} (hn : 0 < n) (hq : P.q=2^n) (hp : p ≠ 2) :
    ModelSylowPowers p (Triality.Standard.Carrier P) := by
  have heP := P.eq_binaryParameters_of_q_eq n hn hq
  subst P
  let P := Triality.Standard.binaryParameters n hn
  intro S B hB hBN α _ hαB hαS
  obtain ⟨j,hBT,hSU⟩ := EvenActions.Triality.SourceAlignment.simultaneous_sylow_torus_conjugacy
    P (Triality.Standard.CartanAction.borelGeometry P rfl)
    (Triality.Standard.Parabolics.unipotentSylow P rfl)
    (Triality.Standard.Parabolics.coe_unipotentSylow P rfl)
    (MulEquiv.refl _) S hp B hB hBN
  let β := MulAut.congr j α
  have hm (X : Subgroup (Triality.Standard.Carrier P)) :
      (X.map j.toMonoidHom).map β.toMonoidHom = (X.map α.toMonoidHom).map j.toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    ext x
    simp [β]
  obtain ⟨k,hk⟩ := Triality.Standard.CartanAction.normalizer_power_of_coverage P rfl
    (Triality.Standard.CartanAction.borelGeometry P rfl)
    (Triality.Standard.OuterOdd.Coverage.binary_inner_coefficient n hn)
    (B.map j.toMonoidHom) hBT β (by rw [hm,hαB]) (by rw [←hSU,hm,hαS])
  refine ⟨2^k,fun b => j.injective ?_⟩
  have he := hk (j b) (mem_map_of_mem j.toMonoidHom b.property)
  simpa [β,MulAut.congr] using he

private theorem inner_sylow_powers {D : Type*} [Group D] [Finite D]
    (hz : center D = ⊥) (hp : p ≠ 2)
    (hinner : ∀ (α : MulAut D) (r : ℕ), α^(2^r)=1 → ∃d, MulAut.conj d=α) :
    ModelSylowPowers p D := by
  intro S B hB hBN α hα hαB hαS
  obtain ⟨r,hr⟩ := hα
  obtain ⟨d,hd⟩ := hinner α r hr
  have hdN : d ∈ normalizer (S : Set D) := mem_normalizer_iff_map_conj_eq.mpr (hd ▸ hαS)
  have hdpow : d^(2^r)=1 := by
    apply MulAut.conj_injective_of_center_eq_bot hz
    rw [map_pow,hd,hr,map_one]
  have hdP : IsPGroup 2 (zpowers d) := IsPGroup.of_card_dvd_pow (n:=r)
    (by simpa [Nat.card_zpowers] using orderOf_dvd_of_pow_eq_one hdpow)
  have hdS : d ∈ S := by
    have hh := S.is_maximal' (hdP.to_sup_of_normal_right' S.isPGroup' (zpowers_le.mpr hdN)) le_sup_right
    exact hh.le (mem_sup_left (mem_zpowers d))
  have hdB : d ∈ normalizer (B : Set D) := mem_normalizer_iff_map_conj_eq.mpr (hd ▸ hαB)
  have hc := EvenActions.unipotent_centralizes (S : Subgroup D) B
    (IsPGroup.disjoint_of_ne 2 p hp.symm S B S.isPGroup' hB) hBN hdS hdB
  refine ⟨1,fun b => ?_⟩
  rw [←hd]
  change d*(b:D)*d⁻¹=(b:D)^1
  rw [←mem_centralizer_iff.mp hc b b.property,mul_inv_cancel_right,pow_one]

/-- A scalar Sylow action in the whole component descends through the actual
odd complement and both radical quotients. -/
theorem Context.sylow_powers_of_model (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hc : SolvableSylowControl 2 K) (hm : ModelSylowPowers p K) :
    ∀ t : ((T : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G),
      ∃ n : ℕ, ∀ v, xiFrattiniAction _ (XiP p L)
        (XiP_invariant p (inf_le_left.trans h.sylow_normalizes)) t v = v^n := by
  let X := XiP p L
  let S := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  have hXK : X ≤ K := h.radical_le_component s e hi
  have hSX : S ≤ normalizer (X : Set G) := XiP_invariant p (inf_le_left.trans h.sylow_normalizes)
  have hSK : S ≤ normalizer (K : Set G) :=
    (inf_le_inf_right _ h.sylow_normalizes).trans (h.local_normalizes_component s e hi)
  have hshape := (RadicalConjugateRigidity.maximal_radical_structure
    h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides).1
  let P : Sylow p X := default
  let B := (P : Subgroup X).map X.subtype
  have hBX : B ≤ X := map_subtype_le _
  have hBK := hBX.trans hXK
  let N := S ⊓ normalizer (B : Set G)
  have hXS : IsSylowIn 2 S (X ⊔ S) := e.full_sylow.restrict le_sup_right
    (sup_le ((h.radical_le_local s).trans inf_le_right) inf_le_right)
  have hQS : X.pCoreIn 2 ≤ S := by
    obtain ⟨R,hR⟩ := hXS
    exact (pCoreIn_mono_of_normalizes le_sup_left (sup_le X.le_normalizer hSX)).trans
      ((pCoreIn_le_sylow (X ⊔ S) R).trans_eq hR)
  obtain ⟨U,hU,hUX⟩ := h.component_sylow e
  let Y := X.subgroupOf K
  let C := B.subgroupOf K
  let : Group.IsSolvable X := by
    let : Group.IsNilpotent (XiQuotient X) := hshape.isPGroup.isNilpotent
    let : Group.IsNilpotent (pCore 2 X) := pCore_isPGroup.isNilpotent
    exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 X)).mpr ⟨inferInstance,inferInstance⟩
  let : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hXK).toMonoidHom) (subgroupOfEquivOfLe hXK).injective
  have hUY : (U : Subgroup K) ≤ normalizer (Y : Set K) := fun a ha =>
    X.le_normalizer_comap K.subtype (hUX (mem_map_of_mem K.subtype ha))
  let : Group.IsNilpotent U := U.isPGroup'.isNilpotent
  let : Group.IsSolvable (Y ⊔ (U : Subgroup K) : Subgroup K) :=
    Group.isSolvable_sup_of_normalizes Y U hUY
  have hCN : C ≤ normalizer (U : Set K) :=
    (subgroupOf_mono K hBX).trans (le_sup_left.trans (hc U (Y ⊔ U) inferInstance le_sup_right))
  let τ : S →* MulAut K := K.normalizerMonoidHom.comp (inclusion hSK)
  have hmap (D : Subgroup K) (t : S) :
      (D.map (τ t).toMonoidHom).map K.subtype =
        (D.map K.subtype).map (MulAut.conj (t : G)).toMonoidHom := by
    rw [map_map,map_map]
    rfl
  have hpowers (t : N) : ∃ n : ℕ, ∀ b : B, (t : G)*(b : G)*(t : G)⁻¹ = (b : G)^n := by
    let tS : S := ⟨t,t.property.1⟩
    have hαC : C.map (τ tS).toMonoidHom = C := by
      apply map_injective K.subtype_injective
      rw [hmap,map_subgroupOf_eq_of_le hBK]
      exact mem_normalizer_iff_map_conj_eq.mp t.property.2
    have hαU : (U : Subgroup K).map (τ tS).toMonoidHom = U := by
      apply map_injective K.subtype_injective
      rw [hmap,hU]
      apply mem_normalizer_iff_map_conj_eq.mp
      exact inf_normalizer_le_normalizer_inf ⟨S.le_normalizer t.property.1,hSK t.property.1⟩
    obtain ⟨r,hr⟩ := (T.isPGroup'.to_le (show S ≤ T from inf_le_left)) tS
    have hα : (τ tS)^(2^r)=1 := by rw [←map_pow,hr,map_one]
    obtain ⟨n,hn⟩ := hm U C (P.isPGroup'.map X.subtype).comap_subtype hCN
      (τ tS) ⟨r,hα⟩ hαC hαU
    exact ⟨n,fun b => congrArg Subtype.val (hn ⟨⟨b,hBK b.property⟩,b.property⟩)⟩
  let j := RadicalActions.sylowFrattiniEquiv h.odd hshape.isPGroup P
  let ρ := frattiniConjugationAction N B inf_le_right
  have hρ (t : N) : ∃ n : ℕ, ∀ a : B ⧸ frattini B, ρ t a = a^n := by
    let _ := conjMulDistribMulActionOfLeNormalizer N B (show N ≤ normalizer B from inf_le_right)
    obtain ⟨n,hn⟩ := hpowers t
    refine ⟨n,?_⟩
    intro a
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (frattini B) a
    have he : MulDistribMulAction.toMulAut N B t b = b^n := Subtype.ext (hn b)
    change quotientAut (frattini B) (MulDistribMulAction.toMulAut N B t)
      (QuotientGroup.mk' (frattini B) b) = _
    rw [quotientAut_apply_mk,he,map_pow]
  intro t
  have hN : N ≤ normalizer (X.pCoreIn 2 : Set G) := inf_le_left.trans
    (hSX.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  have ht : (t : G) ∈ X.pCoreIn 2 ⊔ N :=
    RadicalActions.normalizer_factor hSX hQS hshape.isPGroup P ▸ t.property
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hN] at ht
  obtain ⟨c,hc,a,ha,hca⟩ := ht
  obtain ⟨n,hn⟩ := hρ ⟨a,ha⟩
  refine ⟨n,?_⟩
  intro v
  obtain ⟨w,rfl⟩ := j.surjective v
  have he : t = (⟨c,hQS hc⟩ : S) * ⟨a,ha.1⟩ := Subtype.ext hca.symm
  rw [he,map_mul]
  change xiFrattiniAction S X hSX ⟨c,hQS hc⟩
    (xiFrattiniAction S X hSX ⟨a,ha.1⟩ (j w)) = (j w)^n
  rw [RadicalActions.core_fixes_frattini hSX _ hc,
    ←RadicalActions.sylowFrattiniEquiv_equivariant hSX h.odd hshape.isPGroup P ⟨a,ha⟩ w,
    hn,map_pow]


/-- Triality is excluded by the actual scalar Sylow action and S₃ section. -/
theorem Context.not_ordinary_triality (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hs : SymmetricThreeStabilizerQuotient L p u)
    {n : ℕ} (hn : 2 ≤ n) (he : Triality.Standard.IsTrialityGroupAt (2^n) K) : False := by
  obtain ⟨P,hP,⟨j⟩⟩ := he
  have hchar : P.prime=2 := by rw [P.eq_binaryParameters_of_q_eq n (by omega) hP]; rfl
  have hlarge : 2 < P.q := by rw [hP]; exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) (by omega))
  apply h.not_symmetric_three_of_sylow_powers s _ hs
  exact h.sylow_powers_of_model s e hi
    (SolvableSylowControl.of_equiv j (A315Source.triality_control P hchar hlarge))
    (modelSylowPowers_of_equiv j (triality_sylow_powers P (by omega) hP (by have := h.prime_gt_three; omega)))

/-- Ree is excluded using its odd outer group, preserving the whole ordinary component. -/
theorem Context.not_ordinary_ree (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) (hq : IsQuasisimple K) [IsSimpleGroup K]
    (hs : SymmetricThreeStabilizerQuotient L p u)
    {m : ℕ} (hm : 1 ≤ m) (he : Chapter1.Section02.LocalModels.IsReeF4At K m) : False := by
  obtain ⟨d,⟨j₀⟩⟩ := he
  let j := j₀.trans d.modelEquiv
  let := hq
  let : IsSimpleGroup (ReeF4.Model m) := j.symm.isSimpleGroup
  let : Group.IsPerfect (ReeF4.Model m) := Group.IsPerfect.ofSurjective (f := j.toMonoidHom) j.surjective
  have hz : center (ReeF4.Model m)=⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center _) inferInstance).resolve_right
      (fun hc => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hc))
  apply h.not_symmetric_three_of_sylow_powers s _ hs
  exact h.sylow_powers_of_model s e hi
    (SolvableSylowControl.of_equiv j (A315Source.ree_control m hm))
    (modelSylowPowers_of_equiv j (inner_sylow_powers hz (by have := h.prime_gt_three; omega)
      (ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.inner_of_twoPower hm)))

/-- Every ordinary irreducible escape is excluded; its complete marked catalogue
and both remaining actions are constructed from the original source inputs. -/
theorem Context.not_ordinary_of_source_actions (h : Context T L p)
    (a : SieveActions h) (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) (hq : IsQuasisimple K) : False := by
  obtain ⟨hK,hm⟩ := h.ordinary_remaining_simple_models a c s hnt e hi hq
  let := hK
  have hs := (h.sylow_reducible_and_symmetric_three a c s hnt e hi).2
  rcases hm with ⟨n,hn,hm⟩ | ⟨m,hm,he⟩
  · exact h.not_ordinary_triality s e hi hs hn hm
  · exact h.not_ordinary_ree s e hi hq hs hm he

/-- The irreducible branch of original 13.1.12(3), conditional only on its
separately owned earlier source actions and control. -/
theorem Context.not_escape_of_irreducible_source_actions (h : Context T L p)
    (a : SieveActions h) (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) : False := by
  rcases e.ordinary_or_characteristic_two with hq | hf
  · exact h.not_ordinary_of_source_actions a c s hnt e hi hq
  · exact h.not_characteristic_two_of_source_actions a c s hnt e hi hf

/-- The literal containment consumer now requires only the separate reducible
component branch, besides earlier orbit, action and control facts. -/
theorem Context.centralizer_le_of_reducible_exclusion (h : Context T L p)
    (o : OrbitFacts T L p) (a : SieveActions h) (c : Control T L p)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) :=
  h.centralizer_le_of_component_exclusions o c
    (fun _ s hnt _ e hi => h.not_escape_of_irreducible_source_actions a c s hnt e hi) hred hu hne

/-- The literal TI consumer with the complete irreducible source branch discharged. -/
theorem Context.ti_of_reducible_exclusion (h : Context T L p)
    (o : OrbitFacts T L p) (a : SieveActions h) (c : Control T L p)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) :=
  h.ti_of_component_exclusions o c
    (fun _ s hnt _ e hi => h.not_escape_of_irreducible_source_actions a c s hnt e hi) hred


end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
