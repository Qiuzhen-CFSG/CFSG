module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.FullSemisimple
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Product
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Suzuki.ExchangedActor

/-!
# The faithful product action on the original nonseparated seed

The original central Hall seed is irreducible for L₀ and is killed by O₂(L₀).
 The prescribed quotient marking of L and its chosen Sylow conjugate therefore
 descends this action to the simple square, on the unchanged seed. Failure of
 separation makes both factors nontrivial. Simplicity makes their restrictions
 faithful, and the centerless product argument proves faithfulness of the whole
 square. Consequently the original seed kernel is exactly O₂(L₀).

For a Suzuki quotient this gives the original seed degree bound. If an actual
 Sylow exchanger preserves that seed and its induced operator squares to one,
 the literal quotient formulas identify its action as interchange of the factors.
 The unconditional Schur-field exchange estimate then proves a displacement
 lower bound, excluding the source small-exchanger budget on this same seed.
 No involution lift to the ambient group is assumed. For an elementary
 actor containing the exchange, the rank bound and involution condition
 are derived, excluding action ratio at most two on the original seed.

The remaining actor selection, component-preserving branch, other component
 rows and invariant-constituent analysis remain with qt-d-10-nona5-central-hall-orders.
 The last theorem is an input to its original separation proof, not an assertion
 of SeedAnalysisAt or SourceNonnormalCentralHallAt.
 Source: Aschbacher--Smith D.3.5--7 and10.1.1, printed pp.195--199 and741.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02

private theorem simple_product_faithful
    {S P : Type*} [Group S] [IsSimpleGroup S] [Group P]
    (hZ : center S = ⊥) (f : S × S →* P)
    (hl : ∃ x, f (x,1) ≠ 1) (hr : ∃ x, f (1,x) ≠ 1) :
    Function.Injective f := by
  have hi (g : S →* P) (hg : ∃ x, g x ≠ 1) : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff g).mp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal g.ker inferInstance with hb | ht
    · exact hb
    · obtain ⟨x,hx⟩ := hg
      have hxk : x ∈ g.ker := ht.symm ▸ mem_top x
      exact (hx hxk).elim
  have hiL := hi (f.comp (MonoidHom.inl S S)) hl
  have hiR := hi (f.comp (MonoidHom.inr S S)) hr
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  rintro ⟨x,y⟩ hxy
  have hf : f (x,y) = 1 := hxy
  have hx : x ∈ center S := by
    apply mem_center_iff.mpr
    intro a
    apply hiL
    change f (a*x,1) = f (x*a,1)
    have hc : f ((a,1)*(x,y)) = f ((x,y)*(a,1)) := by simp only [map_mul,hf,mul_one,one_mul]
    have hc' := congrArg (fun z : P => z * f (1,y⁻¹)) hc
    simpa only [←map_mul,Prod.mk_mul_mk,one_mul,mul_one,mul_assoc,mul_inv_cancel] using hc'
  have hx1 : x = 1 := mem_bot.mp (hZ ▸ hx)
  have hy1 : y = 1 := hiR (by change f (1,y) = f (1,1); simpa only [hx1, show (1,1) = (1 : S × S) from rfl, map_one] using hf)
  exact mem_bot.mpr (Prod.ext hx1 hy1)

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance seedTensorElementary : IsElementaryAbelian 2 D.seed := by
  let := D.module_elementary
  exact IsElementaryAbelian.of_injective
    (inclusion (show D.seed ≤ D.moduleSubgroup from le_componentOrbit D.seed T))
    (inclusion_injective _)

/-- The literal marked product acts irreducibly on the unchanged original seed. -/
theorem original_seed_product_action
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (e : (L ⧸ pCore 2 L) ≃* S)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ∃ q : localOrbit T L →* S × S,
      Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
      (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1)) ∧
      (∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l))) ∧
      ∃ σ : Representation (ZMod 2) (S × S) (Additive D.seed),
        σ.IsIrreducible ∧ σ.comp q = originalSeedAction D := by
  obtain ⟨q,hq,hk,hleft,hright⟩ := HallGeometry.marked_pair_projection D e c.nonnormal ht htn
  let ρ := originalSeedAction D
  let : ρ.IsIrreducible := originalSeedAction_irreducible D c
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  have hker : pCore 2 (localOrbit T L) ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let E : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* S × S :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective q hq)
  let τ := quotientOfLEKer ρ _ hker
  let σ := τ.comp E.symm.toMonoidHom
  refine ⟨q,hq,hk,hleft,hright,σ,?_,?_⟩
  · exact (irreducible_comp_surjective_iff E.symm.toMonoidHom E.symm.surjective τ).mpr
      ((quotientOfLEKer_irreducible_iff ρ _ hker).mpr inferInstance)
  · apply MonoidHom.ext
    intro x
    apply LinearMap.ext
    intro v
    change τ (E.symm (E (QuotientGroup.mk' _ x))) v = ρ x v
    rw [E.symm_apply_apply]
    rfl

/-- Failure of original separation makes the descended simple-square action faithful. -/
theorem original_seed_product_faithful_of_not_separated
    {S : Type*} [Group S] [IsSimpleGroup S]
    (e : (L ⧸ pCore 2 L) ≃* S)
    {t : G} (ht : t ∈ (T : Subgroup G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (q : localOrbit T L →* S × S)
    (hleft : ∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1))
    (hright : ∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l)))
    (σ : Representation (ZMod 2) (S × S) (Additive D.seed))
    (hσ : σ.comp q = originalSeedAction D) : Function.Injective σ := by
  let := D.quasisimple
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hZ : center S = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp h))
  have hact (x : localOrbit T L) (v : Additive D.seed) :
      σ (q x) v = originalSeedAction D x v :=
    LinearMap.congr_fun (DFunLike.congr_fun hσ x) v
  have hL : ∃ x : S, σ (x,1) ≠ 1 := by
    by_contra hn
    push Not at hn
    apply hsep
    right
    intro v hv l hl
    have hh := hact ⟨l,le_componentOrbit L T hl⟩ (Additive.ofMul (⟨v,hv⟩ : D.seed))
    rw [hleft ⟨l,hl⟩,hn] at hh
    have he := congrArg (fun w : Additive D.seed => (w.toMul : G)) hh
    change v = l*v*l⁻¹ at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm)
  have hR : ∃ x : S, σ (1,x) ≠ 1 := by
    by_contra hn
    push Not at hn
    apply hsep
    left
    rintro v hv _ ⟨l,hl,rfl⟩
    have hh := hact (originalConjugateOrbitInclusion ht ⟨l,hl⟩)
      (Additive.ofMul (⟨v,hv⟩ : D.seed))
    rw [hright,hn] at hh
    have he := congrArg (fun w : Additive D.seed => (w.toMul : G)) hh
    change v = (t*l*t⁻¹)*v*(t*l*t⁻¹)⁻¹ at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm)
  have hf := simple_product_faithful hZ σ.asGroupHom
    (hL.imp fun x hx he => hx (congrArg Units.val he))
    (hR.imp fun x hx he => hx (congrArg Units.val he))
  intro x y he
  exact hf (Units.ext he)

/-- In the tensor-support branch the original seed kernel is precisely O₂(L₀). -/
theorem original_seed_kernel_of_not_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    (originalSeedAction D).ker = pCore 2 (localOrbit T L) := by
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  obtain ⟨q,_,hk,hl,hr,σ,_,hσ⟩ := original_seed_product_action D c (MulEquiv.refl _) ht htn
  have hf := original_seed_product_faithful_of_not_separated D (MulEquiv.refl _) ht
    hsep q hl hr σ hσ
  rw [←hσ]
  ext x
  change σ (q x) = 1 ↔ x ∈ pCore 2 (localOrbit T L)
  rw [←map_one σ,hf.eq_iff]
  exact SetLike.ext_iff.mp hk x


/-- Conjugation on the unchanged original seed by its actual normalizer. -/
@[expose] def originalSeedNormalizerAction :
    Representation (ZMod 2) (normalizer (D.seed : Set G)) (Additive D.seed) :=
  elementaryRepresentation D.seed.normalizerMonoidHom

/-- A seed-preserving exchanger that squares to one on the seed exchanges
the two literal quotient actions. Its ambient square need not be one. -/
theorem original_seed_product_exchange
    {S : Type*} [Group S]
    (e : (L ⧸ pCore 2 L) ≃* S)
    {t : G} (ht : t ∈ (T : Subgroup G)) (hs : t ∈ normalizer (D.seed : Set G))
    (q : localOrbit T L →* S × S)
    (hleft : ∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1))
    (hright : ∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l)))
    (σ : Representation (ZMod 2) (S × S) (Additive D.seed))
    (hσ : σ.comp q = originalSeedAction D)
    (h2 : originalSeedNormalizerAction D ⟨t,hs⟩ * originalSeedNormalizerAction D ⟨t,hs⟩ = 1) :
    ∀ g v, originalSeedNormalizerAction D ⟨t,hs⟩ (σ g v) =
      σ (g.2,g.1) (originalSeedNormalizerAction D ⟨t,hs⟩ v) := by
  let U := originalSeedNormalizerAction D ⟨t,hs⟩
  have hU (v : Additive D.seed) : U (U v) = v := LinearMap.congr_fun h2 v
  have hact (x : localOrbit T L) (v : Additive D.seed) :
      σ (q x) v = originalSeedAction D x v :=
    LinearMap.congr_fun (DFunLike.congr_fun hσ x) v
  have hfirst (g : S) (v : Additive D.seed) : U (σ (g,1) v) = σ (1,g) (U v) := by
    obtain ⟨l,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
    dsimp only [Function.comp_apply]
    rw [←hleft l,←hright l,hact,hact]
    apply Additive.toMul.injective
    apply Subtype.ext
    change t*((l:G)*(v.toMul:G)*(l:G)⁻¹)*t⁻¹ =
      (t*(l:G)*t⁻¹)*(t*(v.toMul:G)*t⁻¹)*(t*(l:G)*t⁻¹)⁻¹
    group
  have hsecond (g : S) (v : Additive D.seed) : U (σ (1,g) v) = σ (g,1) (U v) := by
    have hh := congrArg U (hfirst g (U v))
    simpa only [hU] using hh.symm
  rintro ⟨x,y⟩ v
  change U (σ (x,y) v) = σ (y,x) (U v)
  have hp : σ (x,y) = σ (x,1) * σ (1,y) := by
    rw [←map_mul]
    simp
  rw [hp,Module.End.mul_apply,hfirst,hsecond,←Module.End.mul_apply,←map_mul]
  simp

/-- In the nonseparated Suzuki branch the original seed itself has the
required product degree; there is no replacement constituent or quotient. -/
theorem original_seed_suzuki_degree_of_not_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (r : ℕ) (hr : 0 < r)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    8 * (2*r+1) ≤ Module.finrank (ZMod 2) (Additive D.seed) := by
  let : Fact (0 < r) := ⟨hr⟩
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  obtain ⟨q,_,_,hl,hright,σ,hi,hσ⟩ := original_seed_product_action D c e ht htn
  exact Suzuki.binary_square_finrank_ge r hr σ hi
    (original_seed_product_faithful_of_not_separated D e ht hsep q hl hright σ hσ)

/-- The genuine seed-preserving Suzuki exchanger moves at least three times
the field degree. Only its action on the seed is required to be involutory. -/
theorem original_seed_suzuki_exchange_displacement
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (r : ℕ) (hr : 0 < r)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hs : t ∈ normalizer (D.seed : Set G))
    (h2 : originalSeedNormalizerAction D ⟨t,hs⟩ * originalSeedNormalizerAction D ⟨t,hs⟩ = 1)
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    3 * (2*r+1) ≤ Module.finrank (ZMod 2)
      (originalSeedNormalizerAction D ⟨t,hs⟩ - 1).range := by
  let : Fact (0 < r) := ⟨hr⟩
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  obtain ⟨q,_,_,hl,hright,σ,hi,hσ⟩ := original_seed_product_action D c e ht htn
  exact Suzuki.binary_square_exchange_displacement_ge r hr σ hi
    (original_seed_product_faithful_of_not_separated D e ht hsep q hl hright σ hσ)
    (originalSeedNormalizerAction D ⟨t,hs⟩) h2
    (original_seed_product_exchange D e ht hs q hl hright σ hσ h2)

/-- The source's small-exchanger budget forces separation of the original
Suzuki seed. Constructing that actor, or handling actors preserving both
components, remains part of the original SeedAnalysisAt assembly. -/
theorem original_seed_separated_of_suzuki_small_exchange
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (r : ℕ) (hr : 0 < r)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hs : t ∈ normalizer (D.seed : Set G))
    (h2 : originalSeedNormalizerAction D ⟨t,hs⟩ * originalSeedNormalizerAction D ⟨t,hs⟩ = 1)
    (hsmall : Module.finrank (ZMod 2) (originalSeedNormalizerAction D ⟨t,hs⟩ - 1).range ≤
      2 * (2*r+2)) :
    D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G) := by
  by_contra hsep
  have hb := original_seed_suzuki_exchange_displacement D c r hr e ht htn hs h2 hsep
  omega


/-- The original Suzuki seed is separated whenever a ratio-at-most-two
 elementary actor in its full linear normalizer contains a genuine Sylow
 exchanger. The displacement budget and involution on the seed are derived. -/
theorem original_seed_separated_of_suzuki_elementary_exchange
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (r : ℕ) (hr : 0 < r)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hs : t ∈ normalizer (D.seed : Set G))
    (A : Subgroup (Module.End (ZMod 2) (Additive D.seed))ˣ)
    [IsElementaryAbelian 2 A]
    (hA : A ≤ linearNormalizer (originalSeedAction D))
    (htA : (originalSeedNormalizerAction D).asGroupHom ⟨t,hs⟩ ∈ A)
    (hsmall : fixedCodim (Units.coeHom (Module.End (ZMod 2) (Additive D.seed))) A ≤
      2 * rank A) :
    D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G) := by
  by_contra hsep
  let : Fact (0 < r) := ⟨hr⟩
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  obtain ⟨q,hq,_,hl,hright,σ,hi,hσ⟩ := original_seed_product_action D c e ht htn
  have hf := original_seed_product_faithful_of_not_separated D e ht hsep q hl hright σ hσ
  have himage : actionImage (originalSeedAction D) = actionImage σ := by
    rw [←hσ]
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨q l,Units.ext (by simp only [Representation.asGroupHom_apply]; rfl)⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨l,Units.ext (by simp only [Representation.asGroupHom_apply]; rfl)⟩
  have hAσ : A ≤ linearNormalizer σ := by
    change A ≤ normalizer (actionImage σ : Set _)
    rw [←himage]
    exact hA
  let C := A.subgroupOf (linearNormalizer σ)
  let E : C ≃* A := subgroupOfEquivOfLe hAσ
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective E.toMonoidHom E.injective
  let a : linearNormalizer σ := ⟨(originalSeedNormalizerAction D).asGroupHom ⟨t,hs⟩,hAσ htA⟩
  have ha : a ∈ C := htA
  have h2 : originalSeedNormalizerAction D ⟨t,hs⟩ *
      originalSeedNormalizerAction D ⟨t,hs⟩ = 1 := by
    have he := congrArg Units.val (elemPow_eq_one_of_isElementaryAbelian (p := 2)
      ((originalSeedNormalizerAction D).asGroupHom ⟨t,hs⟩) htA)
    simpa only [pow_two,Units.val_mul,Units.val_one,Representation.asGroupHom_apply] using he
  have hswap : ∀ g v, normalizerRepresentation σ a (σ g v) =
      σ (g.2,g.1) (normalizerRepresentation σ a v) :=
    original_seed_product_exchange D e ht hs q hl hright σ hσ h2
  have hb := Suzuki.binary_square_exchanged_actor_strict_bound r hr σ hi hf C a ha hswap
  have hcod : fixedCodim (normalizerRepresentation σ) C =
      fixedCodim (Units.coeHom (Module.End (ZMod 2) (Additive D.seed))) A := by
    change fixedCodim ((Units.coeHom _).comp (linearNormalizer σ).subtype) C = _
    unfold fixedCodim
    rw [fixedSpace_comp_map,show C.map (linearNormalizer σ).subtype = A from
      map_subgroupOf_eq_of_le hAσ]
  have hrank : rank C = rank A := congrArg (Nat.log 2) (Nat.card_congr E.toEquiv)
  rw [hcod,hrank] at hb
  omega
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
