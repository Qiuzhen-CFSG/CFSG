module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.OddComponent
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv

/-!
# Constructing the five-component pair obstruction

The actual component inclusions give commuting factors; the PSL₂(5) center
calculation makes their intersection trivial. Inverting the multiplication
isomorphism constructs two jointly injective projections of X. Uniqueness
of multiplication coordinates intertwines conjugation with the component
actions. Restricting the local Sylow to the subnormal components proves
that their Sylows normalize the projected subgroups. The factor stabilizer
has index at most two, and the checked odd-component quotient calculation
bounds the action on X/O₂(X) by that index, contradicting its D₈ model.

The field-four endpoint uses the genuine PSL₂(4) ≃ A₅ ≃ PSL₂(5) maps.
The source assembly must supply the ordinary component pair, its models,
and the commutator/action clauses of 1.1.5. No projection, intertwining,
or action-order bound is a premise here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.4.20, printed p.1164; 1.1.5(3), printed pp.501–503.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
variable {G : Type*} [Group G]

private theorem product_coordinates {A B X : Subgroup G}
    (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G)) (hX : X ≤ A ⊔ B) :
    ∃ f : X →* A × B, Function.Injective f ∧
      ∀ x : X, ((f x).1 : G) * ((f x).2 : G) = x := by
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  let f := e.symm.toMonoidHom.comp (inclusion hX)
  refine ⟨f, e.symm.injective.comp (inclusion_injective hX), ?_⟩
  intro x
  exact (he _ _).symm.trans (congrArg Subtype.val (e.apply_symm_apply (inclusion hX x)))

private theorem coordinates_intertwine {A B X : Subgroup G}
    (hd : Disjoint A B) (f : X →* A × B)
    (hf : ∀ x : X, ((f x).1 : G) * ((f x).2 : G) = x)
    (β : MulAut X) (γ₁ : MulAut A) (γ₂ : MulAut B) (g : G)
    (hx : ∀ x : X, (β x : G) = g * x * g⁻¹)
    (h₁ : ∀ x : A, (γ₁ x : G) = g * x * g⁻¹)
    (h₂ : ∀ x : B, (γ₂ x : G) = g * x * g⁻¹) (x : X) :
    f (β x) = (γ₁ (f x).1, γ₂ (f x).2) := by
  apply mul_injective_of_disjoint hd
  change ((f (β x)).1 : G) * ((f (β x)).2 : G) =
    (γ₁ (f x).1 : G) * (γ₂ (f x).2 : G)
  rw [hf,hx,h₁,h₂]
  simp only [mul_assoc, inv_mul_cancel_left]
  rw [← mul_assoc ((f x).1 : G), hf]

private theorem range_invariant {X A : Type*} [Group X] [Group A]
    (f : X →* A) (β : MulAut X) (γ : MulAut A)
    (he : ∀ x, f (β x) = γ (f x)) : f.range.map γ.toMonoidHom = f.range := by
  rw [← MonoidHom.range_comp]
  have h : γ.toMonoidHom.comp f = f.comp β.toMonoidHom := MonoidHom.ext fun x => (he x).symm
  rw [h,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr β.surjective,MonoidHom.range_eq_map]

private theorem faithful_conjugation {L Z : Subgroup G}
    (hn : Z ≤ normalizer (L : Set G))
    (hc : Z ⊓ centralizer (L : Set G) = ⊥) :
    Function.Injective (L.normalizerMonoidHom.comp (inclusion hn)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro z hz
  have hz' : inclusion hn z ∈ L.normalizerMonoidHom.ker := hz
  rw [normalizerMonoidHom_ker] at hz'
  exact Subtype.ext (mem_bot.mp (hc ▸ (show (z : G) ∈ Z ⊓ centralizer (L : Set G) from
    ⟨z.property,hz'⟩)))

private theorem conjugation_actions_commute {L Z N U : Subgroup G}
    (hZ : Z ≤ centralizer (U : Set G)) (hN : N ≤ U)
    (hzL : Z ≤ normalizer (L : Set G)) (hnL : N ≤ normalizer (L : Set G))
    (n : N) (z : Z) :
    (L.normalizerMonoidHom.comp (inclusion hnL)) n *
        (L.normalizerMonoidHom.comp (inclusion hzL)) z =
      (L.normalizerMonoidHom.comp (inclusion hzL)) z *
        (L.normalizerMonoidHom.comp (inclusion hnL)) n := by
  have hc : (n : G) * z = (z : G) * n := mem_centralizer_iff.mp (hZ z.property) _ (hN n.property)
  have hh := congrArg L.normalizerMonoidHom (show
      inclusion hnL n * inclusion hzL z = inclusion hzL z * inclusion hnL n from Subtype.ext hc)
  simpa only [map_mul,MonoidHom.comp_apply] using hh

variable [Finite G]

/-- Construct both projections, their intertwined factor-stabilizer actions,
and the normalization of their ranges by the actual component Sylows.
The order bound is then the checked PSL₂(5) calculation. -/
theorem five_pair_action_bound
    {H X U Z : Subgroup G} (L : Bool → Subgroup G)
    (a : TwoFactors.MixedLocal.FactorPairAction U L)
    (hLH : ∀ i, L i ≤ H) (hcomp : ∀ i, IsComponent H ((L i).subgroupOf H))
    (hm : ∀ i, ClassicalGroup.IsPSL (L i) 2 5)
    (hX : X ≤ L false ⊔ L true) (hUX : U ≤ normalizer (X : Set G))
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U)
    (hZC : Z ≤ centralizer (U : Set G)) (hcard : Nat.card Z = 4)
    (hZL : ∀ i, Z ≤ normalizer (L i : Set G))
    (hcomm : ∀ i, ∀ z ∈ Z, z ≠ 1 → ⁅L i, zpowers z⁆ = L i)
    (hq : IsPGroup 3 (X ⧸ pCore 2 X)) :
    Nat.card ((quotientAut (pCore 2 X)).comp
      (X.normalizerMonoidHom.comp (inclusion hUX))).range ≤ 2 := by
  have hperfect (i : Bool) : Group.IsPerfect (L i) := by
    let : IsQuasisimple ((L i).subgroupOf H) := (hcomp i).2
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe (hLH i)).toMonoidHom)
      (subgroupOfEquivOfLe (hLH i)).surjective
  let : Group.IsPerfect (L false) := hperfect false
  let : Group.IsPerfect (L true) := hperfect true
  have hne : (L false).subgroupOf H ≠ (L true).subgroupOf H := by
    intro he
    have hh := congrArg (Subgroup.map H.subtype) he
    rw [map_subgroupOf_eq_of_le (hLH false),map_subgroupOf_eq_of_le (hLH true)] at hh
    exact Bool.false_ne_true (a.distinct hh)
  have hc : L false ≤ centralizer (L true : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    have he := congrArg (Subgroup.map H.subtype)
      ((hcomp false).commutator_eq_bot_of_ne (hcomp true) hne)
    simpa only [map_commutator,map_subgroupOf_eq_of_le (hLH false),
      map_subgroupOf_eq_of_le (hLH true),Subgroup.map_bot] using he
  have hd : Disjoint (L false) (L true) := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hy
    have hz : (⟨x,hx⟩ : L false) ∈ center (L false) := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext ((mem_centralizer_iff.mp (hc y.property) x hy).symm)
    have he := odd_linear_component_center_eq_bot (by decide : 5 ≤ 5) (hm false)
    have hx1 : (⟨x,hx⟩ : L false) = 1 := mem_bot.mp (he ▸ hz)
    exact congrArg Subtype.val hx1
  obtain ⟨f,hf,hdecomp⟩ := product_coordinates hd hc hX
  let f₁ := (MonoidHom.fst (L false) (L true)).comp f
  let f₂ := (MonoidHom.snd (L false) (L true)).comp f
  have hpair : Function.Injective (f₁.prod f₂) := hf
  obtain ⟨P₁,hP₁⟩ := sylow_intersection_image_of_relative_subnormal (hLH false) (hcomp false).1 P hP
  obtain ⟨P₂,hP₂⟩ := sylow_intersection_image_of_relative_subnormal (hLH true) (hcomp true).1 P hP
  let θ := X.normalizerMonoidHom.comp (inclusion hUX)
  let α₁ := (L false).normalizerMonoidHom.comp (inclusion (hZL false))
  let α₂ := (L true).normalizerMonoidHom.comp (inclusion (hZL true))
  have hLne (i : Bool) : L i ≠ ⊥ := by
    intro hh
    let : IsQuasisimple ((L i).subgroupOf H) := (hcomp i).2
    let : IsSimpleGroup (((L i).subgroupOf H) ⧸ center ((L i).subgroupOf H)) := IsQuasisimple.simple
    have hn : Nontrivial ((L i).subgroupOf H) :=
      (QuotientGroup.mk'_surjective (center ((L i).subgroupOf H))).nontrivial
    exact (nontrivial_iff_ne_bot ((L i).subgroupOf H)).mp hn (by rw [hh,bot_subgroupOf])
  have ha₁ := faithful_conjugation (hZL false) (faithful_of_component_commutators (hLne false) (hcomm false))
  have ha₂ := faithful_conjugation (hZL true) (faithful_of_component_commutators (hLne true) (hcomm true))
  have hfixed (i : Bool) (Q : Sylow 2 (L i)) (hQ : (Q : Subgroup (L i)).map (L i).subtype = U ⊓ L i) :
      ∀ z : Z, ∀ x ∈ Q, ((L i).normalizerMonoidHom.comp (inclusion (hZL i))) z x = x := by
    intro z x hx
    apply Subtype.ext
    have hxU : (x : G) ∈ U := (hQ ▸ (show (x : G) ∈ (Q : Subgroup (L i)).map (L i).subtype from ⟨x,hx,rfl⟩)).1
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp (hZC z.property) _ hxU).symm)
  have hn₁ : (P₁ : Subgroup (L false)) ≤ normalizer (f₁.range : Set (L false)) := by
    intro p hp
    have hpU : (p : G) ∈ U := (hP₁ ▸ (show (p : G) ∈ (P₁ : Subgroup (L false)).map (L false).subtype from ⟨p,hp,rfl⟩)).1
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply range_invariant f₁ (θ ⟨p,hpU⟩) (MulAut.conj p)
    intro x
    exact congrArg Prod.fst (coordinates_intertwine hd f hdecomp (θ ⟨p,hpU⟩) (MulAut.conj p) 1 p
      (fun _ => rfl) (fun _ => rfl) (fun b => by
        change (b : G) = (p : G) * b * (p : G)⁻¹
        exact (mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp (hc p.property) b b.property).symm)).symm) x)
  have hn₂ : (P₂ : Subgroup (L true)) ≤ normalizer (f₂.range : Set (L true)) := by
    intro p hp
    have hpU : (p : G) ∈ U := (hP₂ ▸ (show (p : G) ∈ (P₂ : Subgroup (L true)).map (L true).subtype from ⟨p,hp,rfl⟩)).1
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply range_invariant f₂ (θ ⟨p,hpU⟩) (MulAut.conj p)
    intro x
    exact congrArg Prod.snd (coordinates_intertwine hd f hdecomp (θ ⟨p,hpU⟩) 1 (MulAut.conj p) p
      (fun _ => rfl) (fun b => by
        change (b : G) = (p : G) * b * (p : G)⁻¹
        exact (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp (hc b.property) p p.property)).symm)
      (fun _ => rfl) x)
  let N := a.permutation.ker
  have hN : N.index ≤ 2 := by
    rw [index_ker]
    have hh := Nat.card_le_card_of_injective a.permutation.range.subtype a.permutation.range.subtype_injective
    simpa [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_perm] using hh
  have hnL (i : Bool) : N.map U.subtype ≤ normalizer (L i : Set G) := by
    rintro _ ⟨n,hn,rfl⟩
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he := a.conjugation n i
    have hn' : a.permutation n = 1 := hn
    change (L i).map (MulAut.conj (n : G)).toMonoidHom = L i
    simpa only [hn',Equiv.Perm.one_apply] using he
  let j : N →* N.map U.subtype := U.subtype.subgroupMap N
  let γ₁ := ((L false).normalizerMonoidHom.comp (inclusion (hnL false))).comp j
  let γ₂ := ((L true).normalizerMonoidHom.comp (inclusion (hnL true))).comp j
  have he₁ (n : N) (x : X) : f₁ (θ n x) = γ₁ n (f₁ x) :=
    congrArg Prod.fst (coordinates_intertwine hd f hdecomp (θ n) (γ₁ n) (γ₂ n) (n : U)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) x)
  have he₂ (n : N) (x : X) : f₂ (θ n x) = γ₂ n (f₂ x) :=
    congrArg Prod.snd (coordinates_intertwine hd f hdecomp (θ n) (γ₁ n) (γ₂ n) (n : U)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) x)
  have hc₁ (n : N) (z : Z) : γ₁ n * α₁ z = α₁ z * γ₁ n :=
    conjugation_actions_commute hZC (map_subtype_le N) (hZL false) (hnL false) (j n) z
  have hc₂ (n : N) (z : Z) : γ₂ n * α₂ z = α₂ z * γ₂ n :=
    conjugation_actions_commute hZC (map_subtype_le N) (hZL true) (hnL true) (j n) z
  exact five_pair_quotient_action_card_le_two (hm false) (hm true) P₁ P₂ α₁ α₂ ha₁ ha₂ hcard
    (hfixed false P₁ hP₁) (hfixed true P₂ hP₂) f₁ f₂ hpair hn₁ hn₂ hq θ N hN γ₁ γ₂ he₁ he₂ hc₁ hc₂

/-- Transport through the genuine exceptional projective-group isomorphisms. -/
theorem five_model_of_four {A : Type*} [Group A] (hm : ClassicalGroup.IsPSL A 2 4) :
    ClassicalGroup.IsPSL A 2 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  obtain ⟨e₅⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  exact ⟨ZMod 5,inferInstance,inferInstance,Nat.card_zmod 5,⟨(e.trans e₄).trans e₅.symm⟩⟩

/-- The actual dihedral quotient action contradicts the constructed five-pair bound. -/
theorem no_five_pair_dihedral_action
    {H X U Z : Subgroup G} (L : Bool → Subgroup G)
    (a : TwoFactors.MixedLocal.FactorPairAction U L)
    (hLH : ∀ i, L i ≤ H) (hcomp : ∀ i, IsComponent H ((L i).subgroupOf H))
    (hm : ∀ i, ClassicalGroup.IsPSL (L i) 2 5)
    (hX : X ≤ L false ⊔ L true) (hUX : U ≤ normalizer (X : Set G))
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U)
    (hZC : Z ≤ centralizer (U : Set G)) (hcard : Nat.card Z = 4)
    (hZL : ∀ i, Z ≤ normalizer (L i : Set G))
    (hcomm : ∀ i, ∀ z ∈ Z, z ≠ 1 → ⁅L i, zpowers z⁆ = L i)
    (hq : IsPGroup 3 (X ⧸ pCore 2 X))
    (hD : Nonempty (((quotientAut (pCore 2 X)).comp
      (X.normalizerMonoidHom.comp (inclusion hUX))).range ≃* DihedralGroup 4)) : False := by
  have hb := five_pair_action_bound L a hLH hcomp hm hX hUX P hP hZC hcard hZL hcomm hq
  obtain ⟨e⟩ := hD
  have hc : Nat.card ((quotientAut (pCore 2 X)).comp
      (X.normalizerMonoidHom.comp (inclusion hUX))).range = 8 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  omega

/-- The field-four pair is excluded using the actual PSL₂(4) ≃ PSL₂(5) comparison. -/
theorem no_four_pair_dihedral_action
    {H X U Z : Subgroup G} (L : Bool → Subgroup G)
    (a : TwoFactors.MixedLocal.FactorPairAction U L)
    (hLH : ∀ i, L i ≤ H) (hcomp : ∀ i, IsComponent H ((L i).subgroupOf H))
    (hm : ∀ i, ClassicalGroup.IsPSL (L i) 2 4)
    (hX : X ≤ L false ⊔ L true) (hUX : U ≤ normalizer (X : Set G))
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U)
    (hZC : Z ≤ centralizer (U : Set G)) (hcard : Nat.card Z = 4)
    (hZL : ∀ i, Z ≤ normalizer (L i : Set G))
    (hcomm : ∀ i, ∀ z ∈ Z, z ≠ 1 → ⁅L i, zpowers z⁆ = L i)
    (hq : IsPGroup 3 (X ⧸ pCore 2 X))
    (hD : Nonempty (((quotientAut (pCore 2 X)).comp
      (X.normalizerMonoidHom.comp (inclusion hUX))).range ≃* DihedralGroup 4)) : False :=
  no_five_pair_dihedral_action L a hLH hcomp (fun i => five_model_of_four (hm i))
    hX hUX P hP hZC hcard hZL hcomm hq hD

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
