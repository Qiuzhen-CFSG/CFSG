module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.AxisCases.SL3
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.Sp4.Symplectic
public import Theory.SpecificGroups.SymplecticFour.ReciprocalSmallActors
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.RankOne.Projection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.Cardinalities
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# The two natural summands and the original flag plane

The literal starred Sylow image gives |V:B| = q. The internal product
P = B × Bʰ and the actual natural marking give |B| = qʲ, so the two
remaining seed dimensions force j = 2 in SL₃ and j = 3 in Sp₄.

The latter is impossible: Bʰ acts faithfully on V and fixes B pointwise.
Its q³ fixed points exclude a semilinear field twist in each involutory
actor. The scalar commutant then makes the action symplectic. Orthogonality
bounds its displacement dimension by one, hence its order by q, contrary
to |Bʰ| = q³. This argument retains field order four.

In SL₃ the earlier natural V_H action makes C_V(V_H) an actual field
subspace in V's marking. Sylow invariance and flag uniqueness identify it
with the original V₂. No compatibility with P's natural field marking is
assumed. The source consumer constructs the pair marking by the preceding
rank-one recognition and proves multiplicity two, |P| = q⁴, P ∩ V = V₂,
and normalization of P by the original T.

Only exact preceding 11.3.7 inputs remain explicit; their final discharge
belongs to qt-d-1222-shadow-common-core using qt-d-1222-shadow-common-action.
The literal radical image, V_K construction, SL₃ block and final local
core recovery remain with qt-d-1222-shadow-common-identification.

The symplectic invariant-form calculation adapts the existing
CommonCore/Action/Transvection/Reciprocal/Sp4/Symplectic proof to the
literal Bʰ actor. Source: Aschbacher--Smith, combined manuscript,
1 March 2004, printed p.774, second paragraph of refs/quasithin.pdf.
-/

set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {h : G} {F : BinaryField}

theorem axis_card_mul_field
    (s : Hypothesis1131At D S U₁ H)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H)) :
    Nat.card (axis V H) * (2 ^ S.field.degree) = Nat.card V := by
  have hVH : V ≤ H := D.le_sylow.trans s.outside.1.1.2
  let q : V →* Star T H := (starProjection T H).comp (inclusion hVH)
  have hr : q.range = (R : Subgroup (residualStar T H)).map (residualStar T H).subtype := by
    rw [hR,MonoidHom.range_comp,inclusion_range]
  have hk : q.ker = (axis V H).subgroupOf V := by
    ext v
    change starProjection T H (inclusion hVH v) = 1 ↔ _
    rw [show starProjection T H = QuotientGroup.mk'
      ((centralizer (omegaClosure T H : Set G)).subgroupOf H) from rfl,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have he := source_star_denominator_eq_core s hmodel
    rw [he]
    change inclusion hVH v ∈ pCore 2 H ↔ (v : G) ∈ axis V H
    constructor
    · intro hv
      exact ⟨v.property,mem_map_of_mem H.subtype hv⟩
    · rintro ⟨_,x,hx,he⟩
      exact (show x = inclusion hVH v from Subtype.ext he) ▸ hx
  have hcK : Nat.card q.ker = Nat.card (axis V H) := by
    rw [hk]
    exact Nat.card_congr (subgroupOfEquivOfLe (show axis V H ≤ V from inf_le_left)).toEquiv
  obtain ⟨_,e,_⟩ := source_compatible_matrix_equivs s hmodel
  have hcR : Nat.card q.range = 2 ^ S.field.degree := by
    rw [hr,card_map_of_injective (residualStar T H).subtype_injective]
    let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
    have hc : Nat.card R = Nat.card R' :=
      (Nat.card_congr ((R : Subgroup _).equivMapOfInjective e.toMonoidHom e.injective).toEquiv)
    rw [hc]
    exact (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive
      S.field.Carrier 2 R').symm.toEquiv).trans S.field.card_eq
  simpa only [index_ker,hcK,hcR] using q.ker.card_mul_index

theorem PairNaturalMarking.axis_card (c : PairNaturalMarking V H h F)
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hz : V ⊓ V.map (MulAut.conj h).toMonoidHom = ⊥) :
    Nat.card (axis V H) = (2 ^ F.degree) ^ c.multiplicity := by
  have he := (pairCore_card s hh hz).symm.trans c.card
  rw [Nat.mul_comm 2, pow_mul] at he
  exact (Nat.pow_left_injective (by decide : 2 ≠ 0)) he


theorem PairNaturalMarking.multiplicity_of_seed_card (c : PairNaturalMarking V H h F)
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hz : V ⊓ V.map (MulAut.conj h).toMonoidHom = ⊥)
    (hdegree : F.degree = S.field.degree)
    (hindex : Nat.card (axis V H) * (2 ^ S.field.degree) = Nat.card V)
    {d : ℕ} (hv : Nat.card V = (2 ^ S.field.degree) ^ d) :
    c.multiplicity + 1 = d := by
  rw [c.axis_card s hh hz,hdegree,hv,←pow_succ] at hindex
  exact Nat.pow_right_injective (by
    have := Nat.one_lt_pow S.field.degree_pos.ne' (by decide : 1 < 2)
    omega) hindex

private theorem seed_card (c : Coordinates D S.field)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Nat.card V = Nat.card c.Space := by
  have hi : Function.Injective c.projection := by
    apply c.projection.ker_eq_bot_iff.mp
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact hfixed.le ⟨v.property,(c.projection_eq_one_iff v).mp hv⟩
  exact Nat.card_congr (Equiv.ofBijective c.projection ⟨hi,c.projection_surjective⟩)

/-- The literal SL₃ seed forces two natural summands, over any marking of the
same field order; no compatibility between the two fields is used. -/
theorem PairNaturalMarking.sl3_multiplicity (c : PairNaturalMarking V H h F)
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hz : V ⊓ V.map (MulAut.conj h).toMonoidHom = ⊥)
    (hdegree : F.degree = S.field.degree)
    (hindex : Nat.card (axis V H) * (2 ^ S.field.degree) = Nat.card V)
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) : c.multiplicity = 2 := by
  have hv : Nat.card V = (2 ^ S.field.degree) ^ 3 := by
    rw [seed_card (.sl3 a) hfixed]
    change Nat.card (Fin 3 → S.field.Carrier) = _
    rw [Nat.card_fun,Nat.card_fin,S.field.card_eq]
  have := c.multiplicity_of_seed_card s hh hz hdegree hindex hv
  omega

/-- The Sp₄ branch would require three summands. This is the exact order
constraint used by its subsequent faithful-transvection exclusion. -/
theorem PairNaturalMarking.sp4_multiplicity (c : PairNaturalMarking V H h F)
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hz : V ⊓ V.map (MulAut.conj h).toMonoidHom = ⊥)
    (hdegree : F.degree = S.field.degree)
    (hindex : Nat.card (axis V H) * (2 ^ S.field.degree) = Nat.card V)
    (a : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) : c.multiplicity = 3 := by
  have hv : Nat.card V = (2 ^ S.field.degree) ^ 4 := by
    rw [seed_card (.sp4 a) hfixed]
    change Nat.card (Fin 2 ⊕ Fin 2 → S.field.Carrier) = _
    rw [Nat.card_fun,Nat.card_sum,Nat.card_fin,S.field.card_eq]
  have := c.multiplicity_of_seed_card s hh hz hdegree hindex hv
  omega

/-- The original axis is invariant under the original Sylow subgroup. -/
theorem axis_normalized (s : Hypothesis1131At D S U₁ H) :
    (T : Subgroup G) ≤ normalizer (axis V H : Set G) :=
  (le_inf S.sylow_normalizes
    (s.outside.1.1.2.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))).trans
    inf_normalizer_le_normalizer_inf

private theorem projection_injective (c : Coordinates D S.field)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) : Function.Injective c.projection := by
  apply c.projection.ker_eq_bot_iff.mp
  apply bot_unique
  intro v hv
  apply Subtype.ext
  exact hfixed.le ⟨v.property,(c.projection_eq_one_iff v).mp hv⟩

/-- A field-linear action makes its literal centralizer a field subspace.
The projection is the original V → V/C_V(L), with its kernel discharged. -/
theorem axis_is_field_subspace (c : Coordinates D S.field)
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hn : omegaClosure T H ≤ normalizer (V : Set G))
    (hlinear : ∀ w : omegaClosure T H, ∀ (r : S.field.Carrier) v,
      c.conjugationAction (hn.trans (WeakClosure.seed_normalizer_le D S)) hn w (r • v) =
        r • c.conjugationAction (hn.trans (WeakClosure.seed_normalizer_le D S)) hn w v) :
    ∃ U : Submodule S.field.Carrier c.Space, c.preimage U = axis V H := by
  let ρ := c.conjugationAction (hn.trans (WeakClosure.seed_normalizer_le D S)) hn
  let U : Submodule S.field.Carrier c.Space :=
    { carrier := {v | ∀ w : omegaClosure T H, ρ w v = v}
      zero_mem' := fun w => map_zero (ρ w)
      add_mem' := fun hx hy w => by rw [map_add,hx w,hy w]
      smul_mem' := fun r v hv w => by rw [hlinear,hv w] }
  refine ⟨U,?_⟩
  rw [axis_eq_fixed s p hc]
  apply le_antisymm
  · intro v hv
    have hvV : v ∈ V := D.centralQuotientPreimage_le _ hv
    refine ⟨hvV,?_⟩
    intro w hw
    have he := (c.mem_preimage U ⟨v,hvV⟩).mp hv ⟨w,hw⟩
    change ρ ⟨w,hw⟩ (c.projection ⟨v,hvV⟩).toAdd = _ at he
    rw [c.conjugationAction_projection] at he
    have he' := congrArg Subtype.val (projection_injective c hfixed
      (Multiplicative.toAdd.injective he))
    exact mul_inv_eq_iff_eq_mul.mp he'
  · rintro v ⟨hvV,hv⟩
    apply (c.mem_preimage U ⟨v,hvV⟩).mpr
    intro w
    change ρ w (c.projection ⟨v,hvV⟩).toAdd = _
    rw [c.conjugationAction_projection]
    have he : V.normalizerMonoidHom (inclusion hn w) ⟨v,hvV⟩ = ⟨v,hvV⟩ :=
      Subtype.ext (mul_inv_eq_iff_eq_mul.mpr (hv w w.property))
    exact congrArg (fun u => (c.projection u).toAdd) he

/-- Uniqueness of the source flag identifies its actual two-dimensional axis. -/
theorem axis_eq_plane_of_field_subspace (c : Coordinates D S.field)
    (f : InvariantFlag c) (hu : f.IsUnique)
    (s : Hypothesis1131At D S U₁ H)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hcard : Nat.card (axis V H) = (2 ^ S.field.degree) ^ 2)
    (U : Submodule S.field.Carrier c.Space) (hU : c.preimage U = axis V H) :
    axis V H = f.Vi 1 := by
  have hd : Module.finrank S.field.Carrier U = 2 := by
    have he := Closure.Nonabelian.card_preimage c hfixed U
    rw [hU,hcard] at he
    exact (Nat.pow_right_injective (by
      have := Nat.one_lt_pow S.field.degree_pos.ne' (by decide : 1 < 2)
      omega) he).symm
  have he := hu 1 U hd (hU.symm ▸ axis_normalized s)
  rw [←hU,he]
  rfl

open Theory.SpecificGroups.SymplecticFour

private theorem linear_of_large_fixed
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (a : Vector F →+ Vector F) (ha : Function.Involutive a)
    (hsemi : ∃ σ : F ≃+* F, ∀ c v, a (c • v) = σ c • a v)
    (hcard : Nat.card F ^ 3 ≤ Nat.card (a.eqLocus (AddMonoidHom.id _))) :
    ∀ (c : F) v, a (c • v) = c • a v := by
  obtain ⟨σ,hσ⟩ := hsemi
  have hs : σ = RingEquiv.refl F := by
    by_contra hn
    have hi : Function.Involutive σ := by
      intro c
      have h := ha (c • (Pi.single (Sum.inl 0) 1 : Vector F))
      rw [hσ,hσ,ha] at h
      simpa using congrFun h (Sum.inl 0)
    have he := Representation.SemilinearInvolution.fixed_card_sq σ hi hn a ha hσ
    have hb := Nat.pow_le_pow_left hcard 2
    rw [he,Nat.card_fun,Nat.card_sum,Nat.card_fin,←pow_mul] at hb
    have ht := Nat.pow_lt_pow_right (Finite.one_lt_card (α := F)) (by decide : 4 < 3*2)
    norm_num only [Nat.reduceAdd,Nat.reduceMul] at hb ht
    omega
  simpa only [hs,RingEquiv.refl_apply] using hσ

private theorem involutive_normalizer_preserves_form
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (a : Vector F →ₗ[F] Vector F) (ha : Function.Involutive a)
    (hnat : ∀ x : Sp F, ∃ y : Sp F, ∀ v, a (x • v) = y • a v) :
    ∀ v w, form F (a v) (a w) = form F v w := by
  let B := (form F).comp a a
  let Q : Module.End F (Vector F) :=
    ((form F).toDual TwoLocalCover.form_nondegenerate).symm.toLinearMap.comp B
  have hQ (v w : Vector F) : form F (Q v) w = form F (a v) (a w) :=
    LinearMap.BilinForm.apply_toDual_symm_apply
      (hB := TwoLocalCover.form_nondegenerate) (B v) w
  have hB (x : Sp F) (v w : Vector F) :
      form F (a (x • v)) (a (x • w)) = form F (a v) (a w) := by
    obtain ⟨y, hy⟩ := hnat x
    rw [hy,hy]
    exact preserves_form y (a v) (a w)
  obtain ⟨c,hc⟩ :=
    SymplecticConjugatePair.Ambient.Normalizer.Commutant.natural_centralizer_scalar
      Q.toAddMonoidHom (by
        intro x v
        change Q (x.val • v) = x.val • Q v
        apply ((form F).toDual TwoLocalCover.form_nondegenerate).injective
        apply LinearMap.ext
        intro w
        obtain ⟨w,rfl⟩ : ∃ z : Vector F, x.val • z = w :=
          ⟨x.val⁻¹ • w,by simp⟩
        change form F (Q (x.val • v)) (x.val • w) =
          form F (x.val • Q v) (x.val • w)
        rw [hQ,hB,←hQ]
        exact (preserves_form x.val (Q v) w).symm)
  have hmul (v w : Vector F) : form F (a v) (a w) = c * form F v w := by
    rw [←hQ,show Q v = c • v from hc v]
    simp
  have hsq : c ^ 2 = 1 := by
    have h := hmul (a (Pi.single (.inl 0) 1)) (a (Pi.single (.inr 0) 1))
    rw [ha,ha,hmul] at h
    simpa [form_apply,Pi.single_apply,pow_two] using h.symm
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa using hsq)
  simpa only [hc1,one_mul] using hmul


private theorem normalizer_sp4_intertwines
    (a : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (z : normalizer (V : Set G)) (x : Sp S.field.Carrier) :
    ∃ y : Sp S.field.Carrier, ∀ v : Vector S.field.Carrier,
      (Coordinates.sp4 a).conjugationAction (WeakClosure.seed_normalizer_le D S) le_rfl z (x • v) =
        symplecticNatural (k := S.field.Carrier) 2 y
          ((Coordinates.sp4 a).conjugationAction (WeakClosure.seed_normalizer_le D S) le_rfl z v) := by
  let c := Coordinates.sp4 a
  let N := normalizer (V : Set G)
  let J := L.subgroupOf N
  let e : J ≃* L := subgroupOfEquivOfLe D.normalizes
  let q : J →* c.ModelGroup := c.quotientMap.comp e.toMonoidHom
  let hNV := WeakClosure.seed_normalizer_le D S
  let _ : J.Normal := normal_subgroupOf_of_le_normalizer hNV
  let ρ := c.conjugationAction hNV le_rfl
  have hnat (j : J) (v : c.Space) : ρ (j : N) v = c.modelAction (q j) v := by
    obtain ⟨u,hu⟩ := c.projection_surjective (Multiplicative.ofAdd v)
    rw [←show (c.projection u).toAdd = v from congrArg Multiplicative.toAdd hu]
    change ρ (j : N) (c.projection u).toAdd =
      c.modelAction (c.quotientMap (e j)) (c.projection u).toAdd
    rw [c.conjugationAction_projection,←c.projection_component_conjugation]
    rfl
  obtain ⟨j,hj⟩ := (c.quotientMap_surjective.comp e.surjective) x
  let b := J.normalizerMonoidHom ⟨z,J.normalizer_eq_top ▸ mem_top z⟩
  change q j = x at hj
  refine ⟨q (b j),?_⟩
  change ∀ v : c.Space, ρ z (c.modelAction x v) = c.modelAction (q (b j)) (ρ z v)
  intro v
  rw [←hj,←hnat j v,←hnat (b j) (ρ z v)]
  change ρ z (ρ (j : N) v) = ρ (z * (j : N) * z⁻¹) (ρ z v)
  simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]

/-- A faithful elementary actor of order q³ cannot centralize q³ points in
an original natural symplectic four-space. The semilinear ambiguity is
removed by the actual fixed-point count, including q=4. -/
private theorem no_large_sp4_actor
    (a : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 a))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (A B : Subgroup G) (hAV : A ≤ normalizer (V : Set G))
    (hBV : B ≤ V) (hBA : B ≤ centralizer (A : Set G))
    (hA2 : ∀ x : A, x ^ 2 = 1)
    (hfaithful : A ⊓ centralizer (V : Set G) = ⊥)
    (hA : Nat.card A = Nat.card S.field.Carrier ^ 3)
    (hB : Nat.card B = Nat.card S.field.Carrier ^ 3) : False := by
  let c := Coordinates.sp4 a
  let : Finite c.Space := by change Finite (Vector S.field.Carrier); infer_instance
  let hNV := WeakClosure.seed_normalizer_le D S
  let ρ := (c.conjugationAction hNV le_rfl).comp (inclusion hAV)
  have hi := projection_injective c hfixed
  have hact (w : A) (v : V) :
      ρ w (c.projection v).toAdd =
        (c.projection (V.normalizerMonoidHom (inclusion hAV w) v)).toAdd :=
    c.conjugationAction_projection hNV le_rfl (inclusion hAV w) v
  have hfix (w : A) (v : B) :
      ρ w (c.projection (inclusion hBV v)).toAdd =
        (c.projection (inclusion hBV v)).toAdd := by
    rw [hact]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hBA v.property w w.property)
  have hinv (w : A) : Function.Involutive (ρ w) := by
    intro v
    rw [←Module.End.mul_apply,←map_mul,←pow_two,hA2,map_one]
    rfl
  let E : Closure.Geometry D :=
    { input := S, point := c.binarySubspace (f.space 0)
      plane := c.binarySubspace (f.space 1)
      threeSpace := c.binarySubspace (f.space 2)
      X := ⊥, z := 1, H := ⊥ }
  let F₀ : Closure.Nonabelian.MarkedFlag E :=
    { action := .sp4 a, flag := f, point_eq := rfl, plane_eq := rfl, threeSpace_eq := rfl }
  have hlin (w : A) : ∀ (r : S.field.Carrier) v, ρ w (r • v) = r • ρ w v := by
    apply linear_of_large_fixed (ρ w).toAddMonoidHom (hinv w)
    · exact Closure.Nonabelian.LineAlignment.normalizer_semilinear F₀ hNV (inclusion hAV w)
    · let j : B → (ρ w).toAddMonoidHom.eqLocus (AddMonoidHom.id _) :=
        fun v => ⟨(c.projection (inclusion hBV v)).toAdd,hfix w v⟩
      rw [←hB]
      apply Nat.card_le_card_of_injective j
      intro v z he
      apply (inclusion_injective hBV)
      exact hi (Multiplicative.toAdd.injective (congrArg Subtype.val he))
  let l (w : A) : Vector S.field.Carrier →ₗ[S.field.Carrier] Vector S.field.Carrier :=
    { toFun := ρ w, map_add' := (ρ w).map_add, map_smul' := hlin w }
  have hp (w : A) : ∀ v z,
      form S.field.Carrier (l w v) (l w z) = form S.field.Carrier v z :=
    involutive_normalizer_preserves_form (l w) (hinv w)
      (normalizer_sp4_intertwines a (inclusion hAV w))
  let αfun (w : A) : Sp S.field.Carrier :=
    ⟨LinearMap.toMatrix' (l w), by
      apply SymplecticGroup.mem_iff'.mpr
      have he := Matrix.toBilin'_comp (-Matrix.J (Fin 2) S.field.Carrier)
        (LinearMap.toMatrix' (l w)) (LinearMap.toMatrix' (l w))
      have hp' : (form S.field.Carrier).comp (l w) (l w) = form S.field.Carrier := by
        apply LinearMap.ext
        intro v
        apply LinearMap.ext
        intro z
        exact hp w v z
      simp only [Matrix.toLin'_toMatrix'] at he
      have hm := Matrix.toBilin'.injective (he.symm.trans hp')
      simpa [Matrix.mul_neg,Matrix.neg_mul,form] using hm⟩
  let α : A →* Sp S.field.Carrier :=
    { toFun := αfun
      map_one' := by
        apply Subtype.ext
        change LinearMap.toMatrix' (l 1) = 1
        have hl : l 1 = 1 := by
          apply LinearMap.ext
          intro v
          change ρ 1 v = v
          rw [map_one]; rfl
        rw [hl,LinearMap.toMatrix'_one]
      map_mul' := by
        intro w z
        apply Subtype.ext
        change LinearMap.toMatrix' (l (w*z)) = LinearMap.toMatrix' (l w) * LinearMap.toMatrix' (l z)
        have hl : l (w*z) = l w * l z := by
          apply LinearMap.ext
          intro v
          change ρ (w*z) v = ρ w (ρ z v)
          rw [map_mul]; rfl
        rw [hl,LinearMap.toMatrix'_mul] }
  have hα (w : A) (v : Vector S.field.Carrier) : α w • v = ρ w v :=
    LinearMap.toMatrix'_mulVec (l w) v
  have hαi : Function.Injective α := by
    apply α.ker_eq_bot_iff.mp
    apply bot_unique
    intro w hw
    apply Subtype.ext
    apply hfaithful.le
    refine ⟨w.property,?_⟩
    intro v hv
    have he := hact w ⟨v,hv⟩
    rw [←hα,show α w = 1 from hw,one_smul] at he
    have he' := congrArg Subtype.val (hi (Multiplicative.toAdd.injective he.symm))
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  have hcA : Nat.card α.range = Nat.card S.field.Carrier ^ 3 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hαi).toEquiv,hA]
  let j : B → TwoLocalCover.fixedSpace α.range := fun v =>
    ⟨(c.projection (inclusion hBV v)).toAdd,by
      rintro w ⟨w,rfl⟩
      rw [hα]
      exact hfix w v⟩
  have hj : Function.Injective j := by
    intro v z he
    apply inclusion_injective hBV
    exact hi (Multiplicative.toAdd.injective (congrArg Subtype.val he))
  have hb := Nat.card_le_card_of_injective j hj
  rw [hB] at hb
  rw [Module.natCard_eq_pow_finrank (K := S.field.Carrier)
    (V := TwoLocalCover.fixedSpace α.range)] at hb
  have hd := (Nat.pow_le_pow_iff_right (Finite.one_lt_card (α := S.field.Carrier))).mp hb
  have horth : Module.finrank S.field.Carrier (TwoLocalCover.fixedSpace α.range) =
      4 - Module.finrank S.field.Carrier (displacementSpace α.range) := by
    rw [←orthogonal_displacementSpace,LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate]
    simp [Theory.SpecificGroups.SymplecticFour.Vector]
  have hdim := (displacementSpace α.range).finrank_le
  have hvdim : Module.finrank S.field.Carrier (Vector S.field.Carrier) = 4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
  rw [hvdim] at hdim
  have hsmall : Module.finrank S.field.Carrier (displacementSpace α.range) ≤ 1 := by omega
  have hbA := card_actor_le_displacement_dimension α.range
  rw [hcA] at hbA
  have hbound : (Module.finrank S.field.Carrier (displacementSpace α.range)) ^ 2 ≤ 1 := by
    nlinarith
  have hpows := (Nat.pow_le_pow_iff_right (Finite.one_lt_card (α := S.field.Carrier))).mp hbA
  omega

/-- The common pair excludes the Sp₄ branch of the original chosen module.
Only the preceding starred Sylow image supplies the axis index. -/
theorem PairNaturalMarking.not_sp4
    (c : PairNaturalMarking V H h F)
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hk : outsideResidual H ≤ pairGroup V h)
    (hdegree : F.degree = S.field.degree)
    (hindex : Nat.card (axis V H) * (2 ^ S.field.degree) = Nat.card V)
    (a : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 a))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) : False := by
  have hz := pair_intersection_eq_bot s hf hk
  have hm := c.sp4_multiplicity s hh hz hdegree hindex a hfixed
  have hB : Nat.card (axis V H) = Nat.card S.field.Carrier ^ 3 := by
    rw [c.axis_card s hh hz,hm,hdegree,S.field.card_eq]
  let A := (axis V H).map (MulAut.conj h).toMonoidHom
  have hA : Nat.card A = Nat.card S.field.Carrier ^ 3 := by
    rw [card_map_of_injective (MulAut.conj h).injective,hB]
  have hAV : A ≤ normalizer (V : Set G) :=
    ((conjugate_axis_eq hh).le.trans inf_le_right).trans (core_normalizes_seed s)
  let := pairCore_elementary s hh hz
  have hBA : axis V H ≤ centralizer (A : Set G) :=
    (show axis V H ≤ pairCore V H h from le_sup_left).trans
      ((pairCore V H h).le_centralizer.trans (centralizer_le (show A ≤ pairCore V H h from le_sup_right)))
  apply no_large_sp4_actor a f hfixed A (axis V H) hAV inf_le_left hBA
    (fun x => ?_) (conjugate_axis_faithful s hf hh hk) hA hB
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian (A := pairCore V H h) (p := 2)
    (x : G) ((show A ≤ pairCore V H h from le_sup_right) x.property)

/-- The earlier natural action makes B an actual field plane of the SL₃ seed.
This uses the field of V and does not identify it with the marking on P. -/
theorem source_axis_eq_plane
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a)) (hu : f.IsUnique)
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (cK : NaturalQuotientMarking T H S.field)
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H))
    (hcard : Nat.card (axis V H) = (2 ^ S.field.degree) ^ 2) :
    axis V H = f.Vi 1 := by
  let c := Coordinates.sl3 a
  let := source_residualQuotient_simple hmodel
  obtain ⟨n⟩ := cK.sylowCoordinates hf s.outside.1.1.2 s.moves_omega_center
    (D.le_sylow.trans s.outside.1.1.2) R hR
  have hn : omegaClosure T H ≤ normalizer (V : Set G) :=
    (omegaClosure_eq_omegaOrbit (T := T) (H := H)).symm ▸
      (ParameterComponent.omegaOrbit_le_sylow s).trans S.sylow_normalizes
  have hv1 : V.map (MulAut.conj (1 : G)).toMonoidHom = V := by
    have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext; simp
    rw [he,map_id]
  have hn1 : omegaClosure T H ≤ normalizer (V.map (MulAut.conj (1 : G)).toMonoidHom : Set G) :=
    hv1.symm ▸ hn
  let n1 : NaturalSylowCoordinates T H (V.map (MulAut.conj (1 : G)).toMonoidHom)
      S.field cK.multiplicity := hv1.symm ▸ n
  have he (w : omegaClosure T H) (v : c.Space) :
      c.conjugationAction (hn.trans (WeakClosure.seed_normalizer_le D S)) hn w v =
        Reciprocal.reciprocalAction c 1 hn1 w v := by
    obtain ⟨u,hu⟩ := c.projection_surjective (Multiplicative.ofAdd v)
    rw [←show (c.projection u).toAdd = v from congrArg Multiplicative.toAdd hu,
      c.conjugationAction_projection,Reciprocal.reciprocalAction_projection]
    have he : inclusion hn w = Reciprocal.reciprocalNormalizerHom 1 hn1 w := by
      apply Subtype.ext
      simp [Reciprocal.reciprocalNormalizerHom]
    rw [he]
  obtain ⟨U,hU⟩ := axis_is_field_subspace c s p hc hfixed hn (by
    intro w r v
    rw [he,he]
    exact Reciprocal.sl3_reciprocal_action_linear a f 1 n1 hn1 w r v)
  exact axis_eq_plane_of_field_subspace c f hu s hfixed hcard U hU

/-- Characteristicity of the identified pair core gives normalization by H,
so in particular the original Sylow subgroup preserves the later complement. -/
theorem pairCore_normalized_by_local
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hk : outsideResidual H ≤ pairGroup V h)
    (hcore : pairCore V H h = (pairGroup V h).pCoreIn 2) :
    H ≤ normalizer (pairCore V H h : Set G) := by
  rw [hcore]
  exact ((normal_subgroupOf_iff_le_normalizer (pairGroup_le s hh)).mp
    (pairGroup_normal_in_H s hh hk)).trans
      (normalizer_le_normalizer_characteristic_image (pairGroup V h) (pCore 2 (pairGroup V h)))

/-- The original counterexample has an SL₃ action and a pair with exactly two
natural summands. The unchanged source flag plane is the literal P ∩ V.
Earlier 11.3.7 inputs are discharged by qt-d-1222-shadow-common-core using
qt-d-1222-shadow-common-action; no multiplicity or axis-identification
callback remains. This precedes construction of the SL₃ block and local cores. -/
theorem source_pair_two_summands
    (cL : Coordinates D S.field) (flag : InvariantFlag cL)
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H) (hh : h ∈ H)
    (hm : h ∉ normalizer (L : Set G))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hnot : ¬ V ≤ H.pCoreIn 2)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H))
    (cK : NaturalQuotientMarking T H S.field)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hAL : oddCartanPart A ≤ L) :
    ∃ (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
      (c : PairNaturalMarking V H h S.field),
      c.multiplicity = 2 ∧
      pairCore V H h = (pairGroup V h).pCoreIn 2 ∧
      pairCore V H h = (outsideResidual H).pCoreIn 2 ∧
      Nat.card (pairCore V H h) = (2 ^ S.field.degree) ^ 4 ∧
      (T : Subgroup G) ≤ normalizer (pairCore V H h : Set G) ∧
      ∀ f : InvariantFlag (.sl3 a), f.IsUnique →
        axis V H = f.Vi 1 ∧ pairCore V H h ⊓ V = f.Vi 1 := by
  have hk := source_residual_le_pairGroup s hh hm hnot hmodel R hR
  have hz := pair_intersection_eq_bot s hf hk
  have hindex := axis_card_mul_field s hmodel R hR
  obtain ⟨hcore,⟨c⟩⟩ := source_pair_recognition s hh hm hf hnot hmodel cK
    R hR A hA hHall hAL
  have hsl : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) := by
    cases cL with
    | sl3 a => exact ⟨a⟩
    | sp4 b => exact (c.not_sp4 s hh hf hk rfl hindex b flag hfixed).elim
    | g2 b => exact (hG2 ⟨b⟩).elim
  obtain ⟨a⟩ := hsl
  have hm := c.sl3_multiplicity s hh hz rfl hindex a hfixed
  have hcard : Nat.card (axis V H) = (2 ^ S.field.degree) ^ 2 := by
    rw [c.axis_card s hh hz,hm]
  refine ⟨a,c,hm,hcore,pairCore_eq_residual_core_of_moved s hh hk hcore c.commutator_eq,?_,
    s.outside.1.1.2.trans (pairCore_normalized_by_local s hh hk hcore),?_⟩
  · rw [c.card,hm]
  · intro f hu
    have he := source_axis_eq_plane a f hu s p hc hfixed hf hmodel cK R hR hcard
    exact ⟨he,(pairCore_inf_seed hh).trans he⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
