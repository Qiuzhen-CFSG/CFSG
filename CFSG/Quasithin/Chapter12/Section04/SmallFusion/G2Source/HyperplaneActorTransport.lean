module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.HyperplaneNormalizers
public import Theory.GroupTheory.PRegularLift
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.Representation.G2OrthogonalCover.HyperplaneComponentActors

/-!
# Original actors for a G₂ cover hyperplane

The marked chosen action identifies an escaping hyperplane with a six-space
avoiding the scalar line. Odd subgroups lift isomorphically through O₂(L),
and the coprime normalizer theorem lifts a normalizer of the chosen cubic.
Thus both alternatives in the model argument give literal ambient actors.
The mover has no square-fixing condition; the component comparison uses
the two hyperplanes symmetrically.

Source: Aschbacher--Smith, Lemma 12.4.8, printed p.815.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Module Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 ChapterE ChapterB.QuasisimpleSource Atlas.G2.Natural
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
local notation "F" => ZMod 2
local notation "E" => TraceZero F
local notation "Q" => commutator (Atlas.G2.Model F)

private theorem prime_lift
    {A B : Type*} [Group A] [Finite A] [Group B]
    (q : A →* B) (hq : Function.Surjective q)
    (hk : Nat.Coprime 3 (Nat.card q.ker))
    (Y : Subgroup B) (hY : IsPGroup 3 Y) :
    ∃ P : Subgroup A, IsPGroup 3 P ∧ P.map q = Y ∧
      ∃ e : P ≃* Y, ∀ p : P, (e p : B) = q p := by
  let R := Y.comap q
  let r : R →* Y := q.subgroupComap Y
  have hr : Function.Surjective r := q.subgroupComap_surjective_of_surjective Y hq
  let S : Sylow 3 R := Sylow.nonempty.some
  have hS : (S.mapSurjective hr : Subgroup Y) = ⊤ := by
    apply top_unique
    exact (hY.to_subgroup ⊤).le_sylow_of_normal _
  let P := (S : Subgroup R).map R.subtype
  have hP : IsPGroup 3 P := S.isPGroup'.map R.subtype
  have hm : P.map q = Y := by
    have hh := congrArg (Subgroup.map Y.subtype) hS
    change ((S : Subgroup R).map r).map Y.subtype = (⊤ : Subgroup Y).map Y.subtype at hh
    rw [map_map, ← MonoidHom.range_eq_map, range_subtype] at hh
    change (S : Subgroup R).map (q.comp R.subtype) = Y at hh
    simpa only [P, map_map] using hh
  let f : P →* Y := (q.comp P.subtype).codRestrict Y
    (fun p => hm ▸ mem_map_of_mem q p.property)
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      exact injective_comp_subtype_of_coprime_ker q hk P hP (congrArg Subtype.val he)
    · intro y
      have hy : (y : B) ∈ P.map q := by rw [hm]; exact y.property
      obtain ⟨a, ha, he⟩ := hy
      exact ⟨⟨a,ha⟩,Subtype.ext he⟩
  exact ⟨P,hP,hm,MulEquiv.ofBijective f hf,fun _ => rfl⟩

private theorem cover_coordinates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : fixedSubgroup L V ≠ ⊥)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    ∃ (b : V ≃* Multiplicative E) (W : Submodule F E),
      finrank F W = 6 ∧ identity F ∉ W ∧
      (∀ w : E, w ∈ W ↔ (b.symm (Multiplicative.ofAdd w) : G) ∈ U) ∧
      ∀ (l : L) (w : E),
        (b.symm (Multiplicative.ofAdd (traceZeroAction F
          (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)).val w)) : G) =
          (l : G) * (b.symm (Multiplicative.ofAdd w) : G) * (l : G)⁻¹ := by
  classical
  let _ := D.elementary
  have hg := escaping_cover_subspaces h D structural e hne hUV hcor hescape
  obtain ⟨z,hz,hfix,_,_,_,_⟩ := exists_fixed_involution_setup h D structural e hne
  obtain ⟨b,φ,hφ,hφL⟩ := exists_normalizer_full_g2_actor_marked h D structural e hne
  let c : Additive V ≃ₗ[F] E := by
    let ca : Additive V ≃+ E := {
      toFun v := (b v.toMul).toAdd
      invFun x := Additive.ofMul (b.symm (Multiplicative.ofAdd x))
      left_inv v := congrArg Additive.ofMul (b.symm_apply_apply v.toMul)
      right_inv x := congrArg Multiplicative.toAdd (b.apply_symm_apply _)
      map_add' v w := congrArg Multiplicative.toAdd (map_mul b v.toMul w.toMul) }
    exact { ca with map_smul' := ZMod.map_smul ca }
  let W₀ := AddSubgroup.toZModSubmodule 2 (U.subgroupOf V).toAddSubgroup
  let W := W₀.map c.toLinearMap
  have hW (x : E) : x ∈ W ↔ (b.symm (Multiplicative.ofAdd x) : G) ∈ U := by
    constructor
    · rintro ⟨v,hv,rfl⟩
      change (b.symm (b v.toMul) : G) ∈ U
      rwa [b.symm_apply_apply]
    · intro hx
      refine ⟨Additive.ofMul (b.symm (Multiplicative.ofAdd x)),hx,?_⟩
      change (b (b.symm (Multiplicative.ofAdd x))).toAdd = x
      rw [b.apply_symm_apply]
      exact toAdd_ofAdd x
  have hd : finrank F W = 6 := by
    change finrank F (W₀.map c.toLinearMap) = 6
    rw [c.finrank_map_eq]
    let eu : W₀ ≃ U := {
      toFun v := ⟨v.val.toMul,v.property⟩
      invFun u := ⟨Additive.ofMul ⟨u,hUV u.property⟩,u.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    have hc : Nat.card W₀ = 64 := (Nat.card_congr eu).trans hg.1
    rw [Module.natCard_eq_pow_finrank (K := F),Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa using hc)
  let zi : V := b.symm (Multiplicative.ofAdd (identity F))
  have hzi1 : (zi : G) ≠ 1 := by
    intro heq
    have he : zi = 1 := Subtype.ext heq
    have hh := congrArg (fun v : V => (b v).toAdd) he
    have hi : identity F = 0 := by
      change (b (b.symm (Multiplicative.ofAdd (identity F)))).toAdd = (b 1).toAdd at hh
      rw [b.apply_symm_apply,map_one] at hh
      simpa only [toAdd_ofAdd,toAdd_one] using hh
    exact Atlas.SplitOctonion.unit_ne_zero (congrArg Subtype.val hi)
  have hziL : (zi : G) ∈ centralizer (L : Set G) := by
    intro l hl
    have hh := hφ ⟨l,L.le_normalizer hl⟩ (identity F)
    rw [traceZeroAction_identity] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  have hzieq : (zi : G) = z := by
    have hzmem : (zi : G) ∈ zpowers z := hfix ▸ ⟨zi.property,hziL⟩
    rw [mem_zpowers_iff_mem_range_orderOf,hz] at hzmem
    obtain ⟨n,hn,hnz⟩ := Finset.mem_image.mp hzmem
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · exact (hzi1 (by simpa using hnz.symm)).elim
    · simpa using hnz.symm
  refine ⟨b,W,hd,?_,hW,?_⟩
  · intro hin
    have hzU : z ∈ U := hzieq ▸ (hW (identity F)).mp hin
    apply hg.2.1
    change V ⊓ centralizer (L : Set G) ≤ U
    rw [hfix]
    exact zpowers_le.mpr hzU
  · intro l w
    simpa only [hφL] using hφ ⟨l,L.le_normalizer l.property⟩ w

private theorem actor_normalizes_iff
    {U : Subgroup G} (hUV : U ≤ V)
    (b : V ≃* Multiplicative E) (q : L →* Q) (W : Submodule F E)
    (hW : ∀ w : E, w ∈ W ↔ (b.symm (Multiplicative.ofAdd w) : G) ∈ U)
    (hc : ∀ (l : L) (w : E),
      (b.symm (Multiplicative.ofAdd (traceZeroAction F (q l).val w)) : G) =
        (l : G) * (b.symm (Multiplicative.ofAdd w) : G) * (l : G)⁻¹)
    (l : L) :
    (q l).val ∈ subspaceStabilizer (traceZeroAction F) W ↔
      (l : G) ∈ normalizer (U : Set G) := by
  constructor
  · intro hl
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨u,hu,rfl⟩
      let v : V := ⟨u,hUV hu⟩
      have hv : (b v).toAdd ∈ W := by
        rw [hW,ofAdd_toAdd,b.symm_apply_apply]
        exact hu
      have hv' := (hW _).mp ((hl _).mpr hv)
      rw [hc] at hv'
      change (l : G) * (b.symm (b v) : G) * (l : G)⁻¹ ∈ U at hv'
      rw [b.symm_apply_apply] at hv'
      exact hv'
    · rw [card_map_of_injective (MulAut.conj (l : G)).injective]
  · intro hl w
    rw [hW,hW,hc]
    exact (mem_normalizer_iff.mp hl _).symm

omit [Finite G] in
private theorem actor_centralizes_iff
    {U : Subgroup G} (hUV : U ≤ V)
    (b : V ≃* Multiplicative E) (q : L →* Q) (W : Submodule F E)
    (hW : ∀ w : E, w ∈ W ↔ (b.symm (Multiplicative.ofAdd w) : G) ∈ U)
    (hc : ∀ (l : L) (w : E),
      (b.symm (Multiplicative.ofAdd (traceZeroAction F (q l).val w)) : G) =
        (l : G) * (b.symm (Multiplicative.ofAdd w) : G) * (l : G)⁻¹)
    (l : L) :
    (∀ w ∈ W, traceZeroAction F (q l).val w = w) ↔
      (l : G) ∈ centralizer (U : Set G) := by
  constructor
  · intro hl u hu
    let v : V := ⟨u,hUV hu⟩
    have hv : (b v).toAdd ∈ W := by
      rw [hW,ofAdd_toAdd,b.symm_apply_apply]
      exact hu
    have he := hc l (b v).toAdd
    rw [hl _ hv,ofAdd_toAdd,b.symm_apply_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  · intro hl w hw
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    apply Subtype.ext
    rw [hc,←hl _ ((hW _).mp hw),mul_inv_cancel_right]

/-- The two source actors, with the cubic normalizer relation lifted through
the two-kernel and every action condition on the original ambient U. -/
theorem exists_cover_hyperplane_component_actors
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : fixedSubgroup L V ≠ ⊥)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    (∃ Y : Subgroup G, Y ≤ L ∧ IsExtraspecial 3 Y ∧ Nat.card Y = 27 ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ Y ≤ normalizer (U : Set G) ∧
      Disjoint Y (centralizer (U : Set G))) ∨
    (∃ x l : G, x ∈ L ∧ orderOf x = 3 ∧ x ∈ normalizer (U : Set G) ∧
      x ∉ centralizer (U : Set G) ∧ l ∈ L ∧
      l ∈ normalizer (zpowers x : Set G) ∧ l ∉ normalizer (U : Set G)) := by
  classical
  let q : L →* Q := e.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q :=
    e.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    change IsPGroup 2 (e.groupEquiv.toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 L))).ker
    rw [MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hk3 : Nat.Coprime 3 (Nat.card q.ker) := by
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  obtain ⟨b,W,hd,hi,hW,hc⟩ := cover_coordinates h D structural e hne hUV hcor hescape
  change ∀ (l : L) (w : E),
    (b.symm (Multiplicative.ofAdd (traceZeroAction F (q l).val w)) : G) =
      (l : G) * (b.symm (Multiplicative.ofAdd w) : G) * (l : G)⁻¹ at hc
  have hnorm := actor_normalizes_iff hUV b q W hW hc
  have hcent := actor_centralizes_iff hUV b q W hW hc
  rcases OrthogonalCover.Hyperplanes.cover_hyperplane_component_actors W hd hi with
    ⟨Y,hYQ,hYextra,hYcard,hYexp,hYN,hYfaith⟩ |
    ⟨x₀,l₀,hx₀,hx₀N,hx₀C,_,hl₀N,hl₀move⟩
  · let Y₀ := Y.subgroupOf Q
    let eY : Y₀ ≃* Y := subgroupOfEquivOfLe hYQ
    let _ : IsExtraspecial 3 Y := hYextra
    have hpY : IsPGroup 3 Y₀ := (IsExtraspecial.isPGroup 3 Y).of_equiv eY.symm
    obtain ⟨P,hP,hPQ,ep,hep⟩ := prime_lift q hq hk3 Y₀ hpY
    let A := P.map L.subtype
    let ea : P ≃* A := equivMapOfInjective P L.subtype L.subtype_injective
    let eAY : A ≃* Y := ea.symm.trans (ep.trans eY)
    have hPq (p : L) (hp : p ∈ P) : (q p).val ∈ Y := by
      have hh : q p ∈ Y₀ := hPQ ▸ mem_map_of_mem q hp
      exact hh
    have hAexp : ∀ y ∈ A, y ^ 3 = 1 := by
      rintro y ⟨p,hp,rfl⟩
      have hp3 : (⟨p,hp⟩ : P) ^ 3 = 1 := by
        apply (ep.trans eY).injective
        rw [map_pow,map_one]
        apply Subtype.ext
        exact hYexp _ ((ep.trans eY) ⟨p,hp⟩).property
      exact congrArg (fun z : P => ((z : L) : G)) hp3
    have hAN : A ≤ normalizer (U : Set G) := by
      rintro y ⟨p,hp,rfl⟩
      exact (hnorm p).mp (hYN (hPq p hp))
    have hAC : Disjoint A (centralizer (U : Set G)) := by
      rw [disjoint_def]
      rintro y ⟨p,hp,rfl⟩ hyC
      have hqp : q p = 1 := by
        apply Subtype.ext
        exact hYfaith _ (hPq p hp) ((hcent p).mpr hyC)
      have hp1 : (⟨p,hp⟩ : P) = 1 :=
        injective_comp_subtype_of_coprime_ker q hk3 P hP (by
          change q p = q 1
          rw [hqp,map_one])
      exact congrArg (fun z : P => ((z : L) : G)) hp1
    exact Or.inl ⟨A,map_subtype_le P,IsExtraspecial.of_mulEquiv eAY.symm hYextra,
      (Nat.card_congr eAY.toEquiv).trans hYcard,hAexp,hAN,hAC⟩
  · obtain ⟨x,hxodd,hqx⟩ := q.exists_pRegular_lift hq 2 Nat.prime_two x₀
      (by rw [hx₀]; decide)
    have hx : orderOf x = 3 := by
      have ho := q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x
        (Nat.prime_two.coprime_iff_not_dvd.mpr hxodd)
      rw [hqx,hx₀] at ho
      exact ho.symm
    let X := zpowers x
    have hX : IsPGroup 3 X := IsPGroup.of_card (n := 1)
      (by simpa only [X,Nat.card_zpowers,pow_one] using hx)
    let _ : Fact (IsPGroup 3 X) := ⟨hX⟩
    have hm : X.map q = zpowers x₀ := by rw [MonoidHom.map_zpowers,hqx]
    have hlmap : l₀ ∈ (normalizer (X : Set L)).map q := by
      rw [←normalizer_map_eq_of_coprime_kernel 3 X q hq hk3,hm]
      exact hl₀N
    obtain ⟨l,hlN,hql⟩ := hlmap
    have hxN : (x : G) ∈ normalizer (U : Set G) := by
      apply (hnorm x).mp
      rw [hqx]
      exact (subspace_map_eq_iff (traceZeroAction F) W x₀.val).mp hx₀N
    have hxC : (x : G) ∉ centralizer (U : Set G) := by
      intro hcU
      obtain ⟨w,hw,hwx⟩ := hx₀C
      have hh := (hcent x).mpr hcU w hw
      rw [hqx] at hh
      exact hwx hh
    have hlX : (l : G) ∈ normalizer (zpowers (x : G) : Set G) := by
      have hh := X.le_normalizer_map L.subtype (mem_map_of_mem L.subtype hlN)
      simpa only [X,MonoidHom.map_zpowers,Subgroup.subtype_apply] using hh
    have hlU : (l : G) ∉ normalizer (U : Set G) := by
      intro hlU
      have hh := (hnorm l).mpr hlU
      rw [hql] at hh
      exact hl₀move ((subspace_map_eq_iff (traceZeroAction F) W l₀.val).mpr hh)
    exact Or.inr ⟨x,l,x.property,(orderOf_coe x).trans hx,hxN,hxC,l.property,hlX,hlU⟩


end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
