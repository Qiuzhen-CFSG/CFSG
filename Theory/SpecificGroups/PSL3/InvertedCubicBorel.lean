module
public import Theory.SpecificGroups.PSL3.BorelCubicAction
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Inverted cubics in lifted projective linear-three Borels

In a finite two-core cover of PSL₃(2ⁿ), a solvable subgroup normalized
by the specified Sylow two-subgroup lies in its normalizer. Its actual
normalizer quotient is the split torus modulo the cubic scalar subgroup.
The quotient map has precisely that Sylow as kernel and intertwines any
specified compatible automorphism.

For n ≥ 4, a two-power actor with cubic displacement on this torus has
trivial torus action. Aligning the original Sylow with the upper root
subgroup allows the cubic-displacement theorem to make the actor inner;
an inner Borel actor fixes its abelian quotient. No complement to the
original two-core, or to the projective scalar kernel, is assumed.

Source: Aschbacher–Smith 14.7.41(2), printed p.1061,
refs/quasithin.pdf; the automorphism calculation is also used in 12.6.31.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.InvertedCubicBorel
open LinearThree CartanActions.BorelQuotient
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

omit [Finite G] in
private theorem normalizer_core (P : Sylow 2 G) :
    pCore 2 (normalizer (P : Set G)) = (P : Subgroup G).subgroupOf (normalizer (P : Set G)) := by
  let : ((P : Subgroup G).subgroupOf (normalizer (P : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer le_rfl
  apply le_antisymm
  · exact pCore_isPGroup.le_sylow_of_normal (P.subtype (P : Subgroup G).le_normalizer)
  · exact le_sSup ⟨inferInstance,P.isPGroup'.comap_subtype⟩

omit [CharP F 2] in
/-- A solvable subgroup normalized by the specified Sylow lies in its normalizer. -/
theorem solvable_sylow_normalized_le_normalizer
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (q : G →* PSL(3,F)) (hq : Function.Surjective q) (P : Sylow 2 G)
    (hk : q.ker ≤ (P : Subgroup G))
    (A : Subgroup G) [Group.IsSolvable A]
    (hnorm : (P : Subgroup G) ≤ normalizer (A : Set G)) :
    A ≤ normalizer (P : Set G) := by
  let := P.isPGroup'.isNilpotent
  let : Group.IsSolvable (A ⊔ (P : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes A P hnorm
  let H := (A ⊔ (P : Subgroup G)).map q
  have hs : Group.IsSolvable H :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  have hN := SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le F hn hF
    (P.mapSurjective hq) H hs (map_mono le_sup_right)
  have hc := (map_le_iff_le_comap).mp hN
  change A ⊔ (P : Subgroup G) ≤
    (normalizer ((P : Subgroup G).map q : Set PSL(3,F))).comap q at hc
  rw [comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self hk] at hc
  exact le_sup_left.trans hc

private theorem inner_of_sylow_cubic_displacement {n : ℕ} (hn : 4 ≤ n) (hF : Nat.card F = 2^n)
    (P : Sylow 2 PSL(3,F)) (a : MulAut PSL(3,F))
    (ha : ∃ k : ℕ, a ^ (2^k) = 1)
    (hP : (P : Subgroup PSL(3,F)).map a.toMonoidHom = P)
    (hc : ∀ x ∈ normalizer (P : Set PSL(3,F)), (a x * x⁻¹)^3 ∈ P) :
    a ∈ MulAut.innerSubgroup PSL(3,F) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) P
    (unipotentSylow F (by omega : 0 < n) hF)
  let e := MulAut.conj g
  have hPe : (P : Subgroup PSL(3,F)).map e.toMonoidHom = unipotent F := by
    change ((g • P : Sylow 2 PSL(3,F)) : Subgroup PSL(3,F)) = _
    rw [hg]
    rfl
  let b := MulAut.congr e a
  have hact (x : PSL(3,F)) : b (e x) = e (a x) := by
    change e (a (e.symm (e x))) = _
    rw [e.symm_apply_apply]
  have hU : (unipotent F).map b.toMonoidHom = unipotent F := by
    have heq : b.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.toMonoidHom :=
      MonoidHom.ext hact
    rw [←hPe,Subgroup.map_map,heq,←Subgroup.map_map,hP]
  have hN : (normalizer (P : Set PSL(3,F))).map e.toMonoidHom = borel F := by
    change (normalizer ((P : Subgroup PSL(3,F)) : Set PSL(3,F))).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq,hPe,normalizer_unipotent F (by omega) hF]
  have hbc : ∀ x ∈ borel F, (b x * x⁻¹)^3 ∈ unipotent F := by
    intro x hx
    rw [←hN] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    have hh := mem_map_of_mem e.toMonoidHom (hc y hy)
    rw [hPe] at hh
    simpa only [map_pow,map_mul,map_inv,MulEquiv.coe_toMonoidHom,hact] using hh
  have hbp : ∃ k : ℕ, b ^ (2^k) = 1 := by
    obtain ⟨k,hk⟩ := ha
    exact ⟨k,by rw [show b = MulAut.congr e a from rfl,←map_pow,hk,map_one]⟩
  obtain ⟨x,hx⟩ := BorelCubicAction.inner_of_cubic_displacement hn hF b hbp hU hbc
  refine ⟨e.symm x,?_⟩
  apply (MulAut.congr e).injective
  rw [MulAut.congr_conj,e.apply_symm_apply]
  exact hx

/-- The actual normalizer torus action; cubic displacement is trivial above degree three. -/
theorem exists_normalizer_torus_action
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (q : G →* PSL(3,F)) (hq : Function.Surjective q) (P : Sylow 2 G)
    (hk : IsPGroup 2 q.ker) (α : MulAut G) (β : MulAut PSL(3,F))
    (hβ : ∃ k : ℕ, β^(2^k) = 1)
    (he : ∀ x, q (α x) = β (q x))
    (hP : (P : Subgroup G).map α.toMonoidHom = P) :
    ∃ f : normalizer (P : Set G) →* ((Fˣ × Fˣ) ⧸ cubicScalars F),
      ∃ τ : MulAut ((Fˣ × Fˣ) ⧸ cubicScalars F),
      Function.Surjective f ∧
      (∀ x, f x = 1 ↔ (x : G) ∈ P) ∧
      (∀ x y : normalizer (P : Set G), α x = y → f y = τ (f x)) ∧
      (4 ≤ n → (∀ z, (τ z * z⁻¹)^3 = 1) → τ = 1) := by
  let Q := P.mapSurjective hq
  let N := normalizer (P : Set G)
  let M := normalizer (Q : Set PSL(3,F))
  have hNq : N.map q = M := P.normalizer_map_surjective q hq
  let f₀ : N →* M := (q.comp N.subtype).codRestrict M (fun x =>
    hNq.le (mem_map_of_mem q x.property))
  have hf₀ : Function.Surjective f₀ := by
    intro y
    obtain ⟨x,hx,he⟩ := hNq.ge y.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have hk₀ : IsPGroup 2 f₀.ker := by
    have hh : f₀.ker = q.ker.comap N.subtype := by
      ext x
      exact Subtype.ext_iff
    rw [hh]
    exact hk.comap_subtype
  let eQ := sylowNormalizerQuotientEquiv F hn hF Q
  let eN := (f₀.pCoreQuotientEquiv hf₀ hk₀).trans eQ
  let f := eN.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
  have hf : Function.Surjective f := eN.surjective.comp (QuotientGroup.mk'_surjective _)
  have hαN : N.map α.toMonoidHom = N := by
    change (normalizer (P : Set G)).map α.toMonoidHom = normalizer (P : Set G)
    have hh := map_normalizer_eq_of_bijective (f := α.toMonoidHom) (P : Subgroup G) α.bijective
    rw [hP] at hh
    exact hh
  let αN := (α.subgroupMap N).trans (MulEquiv.subgroupCongr hαN)
  let τ := MulAut.congr eN ((pCore 2 N).quotientAut αN)
  have hact (x : N) : τ (f x) = f (αN x) := by
    change eN ((pCore 2 N).quotientAut αN (eN.symm (eN (QuotientGroup.mk' _ x)))) = _
    rw [eN.symm_apply_apply,quotientAut_apply_mk]
    rfl
  refine ⟨f,τ,hf,?_,?_,?_⟩
  · intro x
    change eN (QuotientGroup.mk' (pCore 2 N) x) = 1 ↔ _
    rw [eN.map_eq_one_iff]
    change (QuotientGroup.mk x : N ⧸ pCore 2 N) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff,normalizer_core]
    rfl
  · intro x y hxy
    rw [hact]
    congr 1
    exact Subtype.ext hxy.symm
  · intro hn4 hc
    have hQ : (Q : Subgroup PSL(3,F)).map β.toMonoidHom = Q := by
      have heq : β.toMonoidHom.comp q = q.comp α.toMonoidHom := MonoidHom.ext (fun x => (he x).symm)
      change ((P : Subgroup G).map q).map β.toMonoidHom = (P : Subgroup G).map q
      rw [Subgroup.map_map,heq,←Subgroup.map_map,hP]
    have hcube : ∀ x ∈ M, (β x * x⁻¹)^3 ∈ Q := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := hNq.ge hx
      let b : N := ⟨y,hy⟩
      have hh := hc (f b)
      rw [hact,←map_inv,←map_mul,←map_pow] at hh
      change eQ (QuotientGroup.mk' (pCore 2 M) (f₀ ((αN b * b⁻¹)^3))) = 1 at hh
      have hm := (QuotientGroup.eq_one_iff _).mp (eQ.map_eq_one_iff.mp hh)
      rw [normalizer_core] at hm
      change q ((α b * (b : G)⁻¹)^3) ∈ (Q : Subgroup PSL(3,F)) at hm
      change (β (q y) * (q y)⁻¹)^3 ∈ (Q : Subgroup PSL(3,F))
      simpa only [map_pow,map_mul,map_inv,he,b] using hm
    obtain ⟨g,hg⟩ := inner_of_sylow_cubic_displacement hn4 hF Q β hβ hQ hcube
    have hgM : g ∈ M := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      rwa [hg]
    apply MulEquiv.ext
    intro z
    obtain ⟨b,rfl⟩ := hf z
    rw [hact]
    let gM : M := ⟨g,hgM⟩
    have hconj : f₀ (αN b) = gM * f₀ b * gM⁻¹ := by
      apply Subtype.ext
      change q (α b) = g * q b * g⁻¹
      rw [he,←hg]
      rfl
    change eQ (QuotientGroup.mk' (pCore 2 M) (f₀ (αN b))) =
      eQ (QuotientGroup.mk' (pCore 2 M) (f₀ b))
    rw [hconj,map_mul,map_mul,map_inv,map_mul,map_mul,map_inv]
    rw [mul_comm (eQ (QuotientGroup.mk' (pCore 2 M) gM)) _, mul_inv_cancel_right]
end Matrix.PSL3.InvertedCubicBorel
