module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ModelCases
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.OddLinearFixed
public import BenderSuzuki.External.Huppert.II.theorem_6_13
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Odd-prime component obstructions in 15.4.20

For an actual PSL₂(p) component at a Fermat or Mersenne prime p ≥ 7,
1.1.5 supplies a faithful inner action of the central four-group. Restricting
the actual local Sylow subgroup along the component's subnormal inclusion
and using the computed center bound gives a contradiction. Relative
subnormality suffices; the component need not be normal in the overgroup.

For PSL₂(5), a faithful Sylow-fixing action of a group of order four fills
all inner automorphisms from the Sylow subgroup. Any commuting actor
therefore fixes the Sylow subgroup and acts trivially on each normalized
three-group quotient D/O₂(D). For two component projections, injectivity
of the combined map detects O₂(X). The factor stabilizer then acts trivially
on X/O₂(X), bounding the full action image by its index, at most two.
This is incompatible with the D₈ image constructed in `FactorDihedral`.
The three-group condition on each projected quotient is derived from X.

The pair theorem requires the actual injective component projections,
Sylow normalization, and intertwined actions. These must be supplied from
the source component product in final assembly; no product identification
or source embedding alternative is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 1.1.5(3), printed pp.501–502, and Lemma 15.4.20, printed p.1164.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup

private theorem centerless_of_simple_perfect {L : Type*} [Group L]
    [Group.IsPerfect L] [IsSimpleGroup L] : center L = ⊥ := by
  rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp h)).elim

/-- A perfect group with the actual PSL₂ model has trivial center. -/
theorem odd_linear_component_center_eq_bot {L : Type*} [Group L]
    [Group.IsPerfect L] {p : ℕ} (hp : 5 ≤ p) (hm : ClassicalGroup.IsPSL L 2 p) :
    center L = ⊥ := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    BenderSuzuki.External.huppert_II_6_13 2 (by decide)
      (Or.inr (by omega)) (Or.inr (by omega))
  let : IsSimpleGroup L := (MulEquiv.isSimpleGroup_congr e).mpr inferInstance
  exact centerless_of_simple_perfect

private theorem ambient_inner_action_bound {G : Type*} [Group G] [Finite G]
    {L U Z : Subgroup G} (hZL : Z ≤ normalizer (L : Set G))
    (P : Sylow 2 L) (hPU : (P : Subgroup L).map L.subtype ≤ U)
    (hZU : Z ≤ U) (hU : IsPGroup 2 U) (hZC : Z ≤ centralizer (U : Set G))
    (hcenter : center L = ⊥) (hfaith : Z ⊓ centralizer (L : Set G) = ⊥)
    (hinner : ∀ z : Z, ∃ l : L, ∀ x : L,
      (z : G) * (x : G) * (z : G)⁻¹ = (l : G) * (x : G) * (l : G)⁻¹) :
    Nat.card Z ≤ Nat.card (center P) := by
  let α : Z →* MulAut L := L.normalizerMonoidHom.comp (inclusion hZL)
  have hinj : Function.Injective α := by
    apply (MonoidHom.ker_eq_bot_iff α).mp
    apply eq_bot_iff.mpr
    intro z hz
    have hfix : ∀ l : L, (z : G) * (l : G) * (z : G)⁻¹ = (l : G) := by
      intro l
      exact congrArg Subtype.val (DFunLike.congr_fun (MonoidHom.mem_ker.mp hz) l)
    have hc : (z : G) ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
      (mul_inv_eq_iff_eq_mul.mp (hfix ⟨l,hl⟩)).symm
    exact Subtype.ext (mem_bot.mp (hfaith ▸ (show (z : G) ∈ Z ⊓ centralizer (L : Set G) from
      ⟨z.property,hc⟩)))
  have hαinner : ∀ z : Z, ∃ l : L, MulAut.conj l = α z := by
    intro z
    obtain ⟨l,hl⟩ := hinner z
    exact ⟨l,MulEquiv.ext fun x => Subtype.ext (hl x).symm⟩
  have hfixed : ∀ z : Z, ∀ q : P, α z q = q := by
    intro z q
    apply Subtype.ext
    have hqU : ((q : L) : G) ∈ U := hPU ⟨q,q.property,rfl⟩
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp (hZC z.property) _ hqU).symm)
  exact faithful_inner_action_card_le_sylow_center P hcenter α hinj
    (hU.to_le hZU) hαinner hfixed

/-- The inner central four-group action contradicts the odd-prime Sylow-center bound. -/
theorem no_odd_linear_component_central_four {G : Type*} [Group G] [Finite G]
    {L U Z : Subgroup G} [Group.IsPerfect L]
    (hZL : Z ≤ normalizer (L : Set G))
    (P : Sylow 2 L) (hPU : (P : Subgroup L).map L.subtype ≤ U)
    (hZU : Z ≤ U) (hU : IsPGroup 2 U) (hZC : Z ≤ centralizer (U : Set G))
    (hcard : Nat.card Z = 4) (hfaith : Z ⊓ centralizer (L : Set G) = ⊥)
    (hinner : ∀ z : Z, ∃ l : L, ∀ x : L,
      (z : G) * (x : G) * (z : G)⁻¹ = (l : G) * (x : G) * (l : G)⁻¹)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (hmodel : ClassicalGroup.IsPSL L 2 p) : False := by
  have hcenter := odd_linear_component_center_eq_bot (by omega : 5 ≤ p) hmodel
  have hh := (ambient_inner_action_bound hZL P hPU hZU hU hZC hcenter hfaith hinner).trans
    (odd_linear_sylow_center_card_le_two hp hp7 hmodel P)
  omega

/-- Commuting with the faithful central four-group forces pointwise Sylow fixation. -/
theorem five_component_commuting_actor_fixes_sylow
    {L Z : Type*} [Group L] [Finite L] [Group.IsPerfect L] [Group Z] [Finite Z]
    (hmodel : ClassicalGroup.IsPSL L 2 5) (P : Sylow 2 L)
    (α : Z →* MulAut L) (hα : Function.Injective α) (hcard : Nat.card Z = 4)
    (hfix : ∀ z : Z, ∀ x ∈ P, α z x = x)
    (β : MulAut L) (hcomm : ∀ z : Z, β * α z = α z * β) :
    ∀ x ∈ P, β x = x := by
  classical
  have hcenter := odd_linear_component_center_eq_bot (by decide : 5 ≤ 5) hmodel
  have hconj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    apply hcenter.le
    apply mem_center_iff.mpr
    intro y
    have hh := DFunLike.congr_fun (MonoidHom.mem_ker.mp hx) y
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hex : ∀ z : Z, ∃ x : P, α z = MulAut.conj (x : L) := by
    intro z
    obtain ⟨x,hx,he⟩ := odd_linear_five_fixed_inner hmodel P (α z) (hfix z)
    exact ⟨⟨x,hx⟩,he⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro z w he
    apply hα
    rw [hf z,hf w,he]
  have hsurj : Function.Surjective f := by
    let : Fintype Z := Fintype.ofFinite Z
    let : Fintype P := Fintype.ofFinite P
    apply (Fintype.bijective_iff_injective_and_card f).mpr _ |>.2
    refine ⟨hinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    change Nat.card Z = Nat.card (P : Subgroup L)
    exact hcard.trans (odd_linear_five_sylow_card hmodel P).symm
  intro x hx
  obtain ⟨z,hz⟩ := hsurj ⟨x,hx⟩
  have hz' : (f z : L) = x := congrArg Subtype.val hz
  have hh := hcomm z
  rw [hf z,hz'] at hh
  apply hconj
  apply MulEquiv.ext
  intro y
  have he := congrArg (fun a : MulAut L => a (β⁻¹ y)) hh
  simpa only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
    MulAut.apply_inv_self] using he

/-- The same actor induces the identity on a normalized three-group quotient. -/
theorem five_component_commuting_actor_trivial_quotient
    {L Z : Type*} [Group L] [Finite L] [Group.IsPerfect L] [Group Z] [Finite Z]
    (hmodel : ClassicalGroup.IsPSL L 2 5) (P : Sylow 2 L)
    (α : Z →* MulAut L) (hα : Function.Injective α) (hcard : Nat.card Z = 4)
    (hfix : ∀ z : Z, ∀ x ∈ P, α z x = x)
    (β : MulAut L) (hcomm : ∀ z : Z, β * α z = α z * β)
    (D : Subgroup L) (hn : (P : Subgroup L) ≤ normalizer (D : Set L))
    (hq : IsPGroup 3 (D ⧸ pCore 2 D)) :
    ∃ hD : D.map β.toMonoidHom = D,
      quotientAut (pCore 2 D) ((β.subgroupMap D).trans (MulEquiv.subgroupCongr hD)) = 1 := by
  exact odd_linear_five_fixed_quotient hmodel P D hn hq β
    (five_component_commuting_actor_fixes_sylow hmodel P α hα hcard hfix β hcomm)


private theorem displacement_in_core
    {X D : Type*} [Group X] [Group D] (β : MulAut X) (f : X →* D) (γ : MulAut D)
    (he : ∀ x, f (β x) = γ (f x)) (hq : quotientAut (pCore 2 D) γ = 1) (x : X) :
    f (β x * x⁻¹) ∈ pCore 2 D := by
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' (pCore 2 D) (f (β x * x⁻¹)) = 1
  have hh := congrArg (fun a : MulAut (D ⧸ pCore 2 D) =>
    a (QuotientGroup.mk' (pCore 2 D) (f x))) hq
  rw [quotientAut_apply_mk] at hh
  change QuotientGroup.mk' (pCore 2 D) (γ (f x)) = QuotientGroup.mk' (pCore 2 D) (f x) at hh
  rw [map_mul,map_inv,he,map_mul,map_inv,hh,mul_inv_cancel]

private theorem quotient_trivial_of_injective_pair
    {X D₁ D₂ : Type*} [Group X] [Group D₁] [Group D₂]
    (f₁ : X →* D₁) (f₂ : X →* D₂) (hf : Function.Injective (f₁.prod f₂))
    (β : MulAut X) (γ₁ : MulAut D₁) (γ₂ : MulAut D₂)
    (h₁ : ∀ x, f₁ (β x) = γ₁ (f₁ x)) (h₂ : ∀ x, f₂ (β x) = γ₂ (f₂ x))
    (hq₁ : quotientAut (pCore 2 D₁) γ₁ = 1)
    (hq₂ : quotientAut (pCore 2 D₂) γ₂ = 1) :
    quotientAut (pCore 2 X) β = 1 := by
  let C := (pCore 2 D₁).prod (pCore 2 D₂)
  have hp : IsPGroup 2 C := by
    apply IsPGroup.of_equiv (G := (pCore 2 D₁) × (pCore 2 D₂)) _
      ((pCore 2 D₁).prodEquiv (pCore 2 D₂)).symm
    intro x
    obtain ⟨i,hi⟩ := (pCore_isPGroup (p := 2) (G := D₁)) x.1
    obtain ⟨j,hj⟩ := (pCore_isPGroup (p := 2) (G := D₂)) x.2
    refine ⟨i+j,Prod.ext ?_ ?_⟩
    · change x.1 ^ (2 ^ (i+j)) = 1
      rw [pow_add,pow_mul,hi,one_pow]
    · change x.2 ^ (2 ^ (i+j)) = 1
      rw [Nat.add_comm i j,pow_add,pow_mul,hj,one_pow]
  have hcore : C.comap (f₁.prod f₂) ≤ pCore 2 X :=
    le_sSup ⟨inferInstance,hp.comap_of_injective _ hf⟩
  apply MulEquiv.ext
  intro q
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) q
  rw [quotientAut_apply_mk]
  change QuotientGroup.mk' (pCore 2 X) (β x) = QuotientGroup.mk' (pCore 2 X) x
  apply QuotientGroup.eq_iff_div_mem.mpr
  simpa only [div_eq_mul_inv] using hcore ⟨displacement_in_core β f₁ γ₁ h₁ hq₁ x,displacement_in_core β f₂ γ₂ h₂ hq₂ x⟩

private theorem intertwine_range_action
    {X L : Type*} [Group X] [Group L]
    (f : X →* L) (β : MulAut X) (γ : MulAut L)
    (h : ∀ x, f (β x) = γ (f x)) (hD : f.range.map γ.toMonoidHom = f.range) :
    ∀ x, f.rangeRestrict (β x) =
      ((γ.subgroupMap f.range).trans (MulEquiv.subgroupCongr hD)) (f.rangeRestrict x) := by
  intro x
  exact Subtype.ext (h x)

private theorem three_quotient_of_surjective
    {X D : Type*} [Group X] [Group D] (f : X →* D) (hf : Function.Surjective f)
    (hq : IsPGroup 3 (X ⧸ pCore 2 X)) : IsPGroup 3 (D ⧸ pCore 2 D) := by
  have hn : ((pCore 2 X).map f).Normal := Normal.map inferInstance f hf
  have hc : (pCore 2 X).map f ≤ pCore 2 D := le_sSup ⟨hn,pCore_isPGroup.map f⟩
  have hle := map_le_iff_le_comap.mp hc
  exact hq.of_surjective (QuotientGroup.map (pCore 2 X) (pCore 2 D) f hle)
    (QuotientGroup.map_surjective_of_surjective _ _ f
      ((QuotientGroup.mk'_surjective (pCore 2 D)).comp hf) hle)

/-- Two genuine PSL₂(5) component projections force the action on X/O₂(X)
to have order at most two. The factor stabilizer and all intertwining maps
are explicit, and the intrinsic two-core is detected by injectivity. -/
theorem five_pair_quotient_action_card_le_two
    {X U Z L₁ L₂ : Type*} [Group X] [Finite X] [Group U] [Finite U]
    [Group Z] [Finite Z] [Group L₁] [Finite L₁] [Group.IsPerfect L₁]
    [Group L₂] [Finite L₂] [Group.IsPerfect L₂]
    (hm₁ : ClassicalGroup.IsPSL L₁ 2 5) (hm₂ : ClassicalGroup.IsPSL L₂ 2 5)
    (P₁ : Sylow 2 L₁) (P₂ : Sylow 2 L₂)
    (α₁ : Z →* MulAut L₁) (α₂ : Z →* MulAut L₂)
    (ha₁ : Function.Injective α₁) (ha₂ : Function.Injective α₂) (hZ : Nat.card Z = 4)
    (hfix₁ : ∀ z : Z, ∀ x ∈ P₁, α₁ z x = x)
    (hfix₂ : ∀ z : Z, ∀ x ∈ P₂, α₂ z x = x)
    (f₁ : X →* L₁) (f₂ : X →* L₂) (hf : Function.Injective (f₁.prod f₂))
    (hn₁ : (P₁ : Subgroup L₁) ≤ normalizer (f₁.range : Set L₁))
    (hn₂ : (P₂ : Subgroup L₂) ≤ normalizer (f₂.range : Set L₂))
    (hq : IsPGroup 3 (X ⧸ pCore 2 X))
    (θ : U →* MulAut X) (N : Subgroup U) (hN : N.index ≤ 2)
    (γ₁ : N →* MulAut L₁) (γ₂ : N →* MulAut L₂)
    (he₁ : ∀ n : N, ∀ x, f₁ (θ n x) = γ₁ n (f₁ x))
    (he₂ : ∀ n : N, ∀ x, f₂ (θ n x) = γ₂ n (f₂ x))
    (hc₁ : ∀ n : N, ∀ z : Z, γ₁ n * α₁ z = α₁ z * γ₁ n)
    (hc₂ : ∀ n : N, ∀ z : Z, γ₂ n * α₂ z = α₂ z * γ₂ n) :
    Nat.card ((quotientAut (pCore 2 X)).comp θ).range ≤ 2 := by
  let δ := (quotientAut (pCore 2 X)).comp θ
  have hq₁ := three_quotient_of_surjective f₁.rangeRestrict f₁.rangeRestrict_surjective hq
  have hq₂ := three_quotient_of_surjective f₂.rangeRestrict f₂.rangeRestrict_surjective hq
  have hker : N ≤ δ.ker := by
    intro n hn
    let n' : N := ⟨n,hn⟩
    obtain ⟨hD₁,hqD₁⟩ := five_component_commuting_actor_trivial_quotient hm₁ P₁ α₁ ha₁ hZ
      hfix₁ (γ₁ n') (hc₁ n') f₁.range hn₁ hq₁
    obtain ⟨hD₂,hqD₂⟩ := five_component_commuting_actor_trivial_quotient hm₂ P₂ α₂ ha₂ hZ
      hfix₂ (γ₂ n') (hc₂ n') f₂.range hn₂ hq₂
    have hinj : Function.Injective (f₁.rangeRestrict.prod f₂.rangeRestrict) := by
      intro x y he
      apply hf
      exact Prod.ext (congrArg (fun v => ((v.1 : f₁.range) : L₁)) he)
        (congrArg (fun v => ((v.2 : f₂.range) : L₂)) he)
    exact quotient_trivial_of_injective_pair f₁.rangeRestrict f₂.rangeRestrict hinj (θ n)
      _ _ (intertwine_range_action f₁ (θ n) (γ₁ n') (he₁ n') hD₁)
      (intertwine_range_action f₂ (θ n) (γ₂ n') (he₂ n') hD₂) hqD₁ hqD₂
  have hd := index_antitone hker
  rw [index_ker] at hd
  exact hd.trans hN


/-- Restrict the actual local Sylow subgroup to a relatively subnormal component. -/
theorem sylow_intersection_image_of_relative_subnormal
    {G : Type*} [Group G] [Finite G] {H L U : Subgroup G}
    (hLH : L ≤ H) (hsub : (L.subgroupOf H).IsSubnormal)
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U) :
    ∃ Q : Sylow 2 L, (Q : Subgroup L).map L.subtype = U ⊓ L := by
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_subnormal (L.subgroupOf H) hsub
  let e := subgroupOfEquivOfLe hLH
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨Q',?_⟩
  have hmaps : (Q' : Subgroup L).map L.subtype =
      ((Q : Subgroup (L.subgroupOf H)).map (L.subgroupOf H).subtype).map H.subtype := by
    change ((Q : Subgroup (L.subgroupOf H)).map e.toMonoidHom).map L.subtype = _
    rw [map_map,map_map]
    rfl
  rw [hmaps,hQ,subgroupOf_map_subtype,map_inf _ _ _ H.subtype_injective,
    hP,map_subgroupOf_eq_of_le hLH]

/-- The odd-prime component obstruction using the actual ambient Sylow and
component commutators from 1.1.5. No normality of the component in H is assumed. -/
theorem no_odd_linear_subnormal_component
    {G : Type*} [Group G] [Finite G] {H L U Z : Subgroup G}
    [Group.IsPerfect L] (hL : L ≠ ⊥)
    (hLH : L ≤ H) (hsub : (L.subgroupOf H).IsSubnormal)
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U)
    (hZU : Z ≤ U) (hZC : Z ≤ centralizer (U : Set G)) (hcard : Nat.card Z = 4)
    (hcomm : ∀ z ∈ Z, z ≠ 1 → ⁅L,zpowers z⁆ = L)
    (hinner : ∀ z : Z, ∃ l : L, ∀ x : L,
      (z : G) * (x : G) * (z : G)⁻¹ = (l : G) * (x : G) * (l : G)⁻¹)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (hmodel : ClassicalGroup.IsPSL L 2 p) : False := by
  have hZL : Z ≤ normalizer (L : Set G) := by
    intro z hz
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨l,hl⟩ := hinner ⟨z,hz⟩
      change z*x*z⁻¹ ∈ L
      rw [hl ⟨x,hx⟩]
      exact L.mul_mem (L.mul_mem l.property hx) (L.inv_mem l.property)
    · intro x hx
      obtain ⟨l,hl⟩ := hinner ⟨z⁻¹,Z.inv_mem hz⟩
      have hmem : z⁻¹*x*z ∈ L := by
        have hh : z⁻¹*x*(z⁻¹)⁻¹ = (l : G)*x*(l : G)⁻¹ := hl ⟨x,hx⟩
        rw [inv_inv] at hh
        rw [hh]
        exact L.mul_mem (L.mul_mem l.property hx) (L.inv_mem l.property)
      exact ⟨z⁻¹*x*z,hmem,by simp [MulAut.conj_apply,mul_assoc]⟩
  obtain ⟨Q,hQ⟩ := sylow_intersection_image_of_relative_subnormal hLH hsub P hP
  exact no_odd_linear_component_central_four hZL Q (hQ ▸ inf_le_left)
    hZU (hP ▸ P.isPGroup'.map H.subtype) hZC hcard
    (faithful_of_component_commutators hL hcomm) hinner hp hp7 hmodel

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
