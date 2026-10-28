module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.Orbit
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.Action
public import Theory.Representation.SemilinearInvolutionFixedCard

/-!
# The literal reciprocal Sp₄ displacement orbit

The existing original-action commutant theorem supplies semilinearity.
For an involution with a nontrivial field twist, the square of its displacement
order is q⁴, contradicting the forward bound q. Thus the actual reciprocal
action is field-linear. A nonzero displacement then contains a field line,
and the exact commutator order forces equality. Component line transitivity
supplies the original x*g transporter.

The coordinate commutator arguments adapt the checked SL₃ SmallCommutator
proof, preserving the literal original quotient and selected conjugator.
The source consumer still takes the original line marking; MarkedLine.HallSpectrum
supplies it in the final source assembly. Genuine symplectic matrix realization
and the common-axis multiplicity calculation are separate local obligations.
Source: Aschbacher--Smith 11.3.7(4), printed p.773 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
  {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- The size of one actual displacement is bounded by the original commutator. -/
private theorem displacement_card_le_commutator (c : Coordinates D S.field) (A : Subgroup G)
    (hAL : A ≤ normalizer (L : Set G)) (hAV : A ≤ normalizer (V : Set G)) (a : A) :
    Nat.card ((c.conjugationAction hAL hAV a).toAddMonoidHom -
      AddMonoidHom.id _).range ≤ Nat.card (⁅A, V⁆ : Subgroup G) := by
  let ρ := c.conjugationAction hAL hAV
  let δ := (ρ a).toAddMonoidHom - AddMonoidHom.id c.Space
  have hC : ⁅A, V⁆ ≤ V := le_normalizer_iff_commutator_le_right.mp hAV
  let p : (⁅A, V⁆ : Subgroup G) →* Multiplicative c.Space :=
    c.projection.comp (inclusion hC)
  let : Finite p.range := Finite.of_surjective p.rangeRestrict p.rangeRestrict_surjective
  have hδ (x : δ.range) : Multiplicative.ofAdd x.val ∈ p.range := by
    obtain ⟨v, hv⟩ := x.property
    obtain ⟨w, hw⟩ := c.projection_surjective (Multiplicative.ofAdd v)
    let z : V := V.normalizerMonoidHom (inclusion hAV a) w * w⁻¹
    have hz : (z : G) ∈ ⁅A, V⁆ := commutator_mem_commutator a.property w.property
    refine ⟨⟨z, hz⟩, ?_⟩
    change c.projection z = Multiplicative.ofAdd x.val
    apply Multiplicative.toAdd.injective
    change (c.projection z).toAdd = x.val
    rw [← hv]
    change (c.projection (V.normalizerMonoidHom (inclusion hAV a) w * w⁻¹)).toAdd =
      ρ a v - v
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    rw [← c.conjugationAction_projection hAL hAV, hw]
    rfl
  let j : δ.range → p.range := fun x => ⟨Multiplicative.ofAdd x.val, hδ x⟩
  exact (Nat.card_le_card_of_injective j (by
    intro x y h
    exact Subtype.ext (congrArg (fun z : p.range => z.val.toAdd) h))).trans
      (Nat.card_le_card_of_surjective p.rangeRestrict p.rangeRestrict_surjective)

private theorem sp4_linear_of_small_displacement
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (a : (Fin 2 ⊕ Fin 2 → F) →+ (Fin 2 ⊕ Fin 2 → F))
    (ha : Function.Involutive a)
    (hsemi : ∃ σ : F ≃+* F, ∀ c v, a (c • v) = σ c • a v)
    (hcard : Nat.card (a - AddMonoidHom.id _).range ≤ Nat.card F) :
    ∀ (c : F) v, a (c • v) = c • a v := by
  obtain ⟨σ,hσ⟩ := hsemi
  have hs : σ = RingEquiv.refl F := by
    by_contra hn
    have hi : Function.Involutive σ := by
      intro c
      have h := ha (c • (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F))
      rw [hσ,hσ,ha] at h
      simpa using congrFun h (Sum.inl 0)
    let δ := a - AddMonoidHom.id (Fin 2 ⊕ Fin 2 → F)
    have hk : δ.ker = a.eqLocus (AddMonoidHom.id _) := by
      ext v
      exact sub_eq_zero
    have he := Representation.SemilinearInvolution.fixed_card_sq σ hi hn a ha hσ
    rw [← hk] at he
    have hc := δ.ker.card_mul_index
    rw [AddSubgroup.index_ker] at hc
    have hp : 0 < Nat.card δ.ker := Nat.card_pos
    have hr : Nat.card δ.range = Nat.card δ.ker := by nlinarith
    have hsquare : Nat.card δ.range ^ 2 = Nat.card F ^ 4 := by
      rw [hr,he,Nat.card_fun,Nat.card_sum,Nat.card_fin]
    have hF : 1 < Nat.card F := Finite.one_lt_card
    have hh : Nat.card δ.range ^ 2 ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hcard 2
    have hq : Nat.card F ^ 2 < Nat.card F ^ 4 := Nat.pow_lt_pow_right hF (by decide)
    omega
  simpa only [hs,RingEquiv.refl_apply] using hσ

set_option backward.isDefEq.respectTransparency false in
/-- The literal reciprocal action on the original symplectic marking is
field-linear; the small-commutator bound excludes every nontrivial field twist. -/
theorem sp4_reciprocal_action_linear
    (a : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 a)) (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    ∀ (w : omegaClosure T H) (r : S.field.Carrier) v,
      reciprocalAction (.sp4 a) g hN w (r • v) =
        r • reciprocalAction (.sp4 a) g hN w v := by
  let E : Closure.Geometry D :=
    { input := S
      point := (Coordinates.sp4 a).binarySubspace (f.space 0)
      plane := (Coordinates.sp4 a).binarySubspace (f.space 1)
      threeSpace := (Coordinates.sp4 a).binarySubspace (f.space 2)
      X := ⊥, z := g, H := H }
  let F₀ : Closure.Nonabelian.MarkedFlag E :=
    { action := .sp4 a, flag := f, point_eq := rfl, plane_eq := rfl, threeSpace_eq := rfl }
  let c := Coordinates.sp4 a
  let ρ := reciprocalAction c g hN
  intro w
  apply sp4_linear_of_small_displacement (ρ w).toAddMonoidHom
  · intro v
    change ρ w (ρ w v) = v
    rw [← Module.End.mul_apply,← map_mul,← pow_two,n.square_eq_one w,map_one]
    rfl
  · exact Closure.Nonabelian.LineAlignment.normalizer_semilinear F₀
      (WeakClosure.seed_normalizer_le D S) (reciprocalNormalizerHom g hN w)
  · let B := (zpowers (w : G)).map (MulAut.conj g⁻¹).toMonoidHom
    have hBV := cyclic_normalizes_seed g hN w
    have hBL := hBV.trans (WeakClosure.seed_normalizer_le D S)
    let b : B := ⟨(MulAut.conj g⁻¹) (w : G), mem_map_of_mem _ (mem_zpowers (w : G))⟩
    have he : c.conjugationAction hBL hBV b = ρ w := by
      apply LinearMap.ext
      intro v
      obtain ⟨u,hu⟩ := c.projection_surjective (Multiplicative.ofAdd v)
      rw [← show (c.projection u).toAdd = v from congrArg Multiplicative.toAdd hu,
        c.conjugationAction_projection,reciprocalAction_projection]
      rfl
    rw [← he]
    exact (displacement_card_le_commutator c B hBL hBV b).trans
      (cyclic_commutator_card_le g n w)

private theorem projection_injective (c : Coordinates D S.field)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Function.Injective c.projection := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro v hv
  apply mem_bot.mpr
  apply Subtype.ext
  apply mem_bot.mp
  rw [← hfixed]
  exact ⟨v.property, (c.projection_eq_one_iff v).mp hv⟩

private theorem projection_commutator (c : Coordinates D S.field) (A : Subgroup G)
    (hAL : A ≤ normalizer (L : Set G)) (hAV : A ≤ normalizer (V : Set G))
    (a : A) (v : V) :
    (c.projection
      (V.normalizerMonoidHom (inclusion hAV a) v * v⁻¹)).toAdd =
        c.conjugationAction hAL hAV a
          (c.projection v).toAdd -
          (c.projection v).toAdd := by
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
  rw [← c.conjugationAction_projection]

/-- A nontrivial commutator under field-linear actors contains an actual
field line. Its scalar multiples are displacements of scalar multiples
of one moving vector. -/
private theorem exists_fieldLine_le_commutator (c : Coordinates D S.field)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (A : Subgroup G) (hAL : A ≤ normalizer (L : Set G))
    (hAV : A ≤ normalizer (V : Set G)) (hne : ⁅A, V⁆ ≠ ⊥)
    (hlinear : ∀ a : A, ∀ (r : S.field.Carrier) v,
      c.conjugationAction hAL hAV a (r • v) =
        r • c.conjugationAction hAL hAV a v) :
    ∃ U : Submodule S.field.Carrier c.Space,
      Module.finrank S.field.Carrier U = 1 ∧
        c.preimage U ≤ ⁅A, V⁆ := by
  let ρ := c.conjugationAction hAL hAV
  obtain ⟨a, x, hx⟩ : ∃ a : A, ∃ x : c.Space, ρ a x ≠ x := by
    by_contra! h
    apply hne
    apply bot_unique
    apply commutator_le.mpr
    intro a ha v hv
    let a' : A := ⟨a, ha⟩
    let v' : V := ⟨v, hv⟩
    let z : V := V.normalizerMonoidHom (inclusion hAV a') v' * v'⁻¹
    have hz : z = 1 := by
      apply projection_injective c hfixed
      apply Multiplicative.toAdd.injective
      rw [map_one]
      change (c.projection z).toAdd = 0
      rw [projection_commutator c A hAL hAV, h, sub_self]
    exact mem_bot.mpr (congrArg Subtype.val hz)
  let w := ρ a x - x
  have hw : w ≠ 0 := sub_ne_zero.mpr hx
  refine ⟨Submodule.span S.field.Carrier {w}, finrank_span_singleton hw, ?_⟩
  intro v hv
  let v' : V := ⟨v, D.centralQuotientPreimage_le _ hv⟩
  have hv' := (c.mem_preimage _ v').mp hv
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hv'
  obtain ⟨y, hy⟩ := c.projection_surjective (Multiplicative.ofAdd (r • x))
  let z : V := V.normalizerMonoidHom (inclusion hAV a) y * y⁻¹
  have hz : z = v' := by
    apply projection_injective c hfixed
    apply Multiplicative.toAdd.injective
    rw [projection_commutator c A hAL hAV, hy]
    change ρ a (r • x) - r • x = (c.projection v').toAdd
    rw [hlinear, ← smul_sub]
    exact hr
  have hm : (z : G) ∈ ⁅A, V⁆ := commutator_mem_commutator a.property y.property
  rwa [hz] at hm

/-- Every nonzero individual reciprocal displacement is an actual field line
of the original symplectic quotient, transported by the same selected g. -/
theorem sp4_commutator_field_line
    (a : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 a))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (w : omegaClosure T H)
    (hw : (w : G) ∉ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    ∃ U : Submodule S.field.Carrier (Coordinates.sp4 a).Space,
      Module.finrank S.field.Carrier U = 1 ∧
      ⁅V.map (MulAut.conj g).toMonoidHom, zpowers (w : G)⁆ =
        ((Coordinates.sp4 a).preimage U).map (MulAut.conj g).toMonoidHom := by
  let c := Coordinates.sp4 a
  let B := (zpowers (w : G)).map (MulAut.conj g⁻¹).toMonoidHom
  have hBV := cyclic_normalizes_seed g hN w
  have hBL := hBV.trans (WeakClosure.seed_normalizer_le D S)
  have hc := cyclic_commutator_eq (V := V) g w
  have hne : ⁅B,V⁆ ≠ ⊥ := by
    rw [hc]
    intro he
    exact NaturalSylowCoordinates.vector_commutator_ne_bot w hw
      ((map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).mp he)
  have hlin : ∀ b : B, ∀ (r : S.field.Carrier) v,
      c.conjugationAction hBL hBV b (r • v) = r • c.conjugationAction hBL hBV b v := by
    intro b r v
    obtain ⟨u,hu,hub⟩ := b.property
    have huW : u ∈ omegaClosure T H := (zpowers_le.mpr w.property) hu
    let u' : omegaClosure T H := ⟨u,huW⟩
    have he : c.conjugationAction hBL hBV b = reciprocalAction c g hN u' := by
      apply LinearMap.ext
      intro x
      obtain ⟨z,hz⟩ := c.projection_surjective (Multiplicative.ofAdd x)
      rw [← show (c.projection z).toAdd = x from congrArg Multiplicative.toAdd hz,
        c.conjugationAction_projection,reciprocalAction_projection]
      rw [show inclusion hBV b = reciprocalNormalizerHom g hN u' from Subtype.ext hub.symm]
    rw [he]
    exact sp4_reciprocal_action_linear a f g n hN u' r v
  obtain ⟨U,hU,hle⟩ := exists_fieldLine_le_commutator c hfixed B hBL hBV hne hlin
  have hsize : Nat.card (⁅B,V⁆ : Subgroup G) = Nat.card S.field.Carrier := by
    rw [hc,card_map_of_injective (MulAut.conj g⁻¹).injective,n.card_vector_commutator w hw]
  have he : c.preimage U = ⁅B,V⁆ := eq_of_le_of_card_ge hle (by
    rw [Closure.Nonabelian.card_preimage c hfixed U,hU,pow_one,← S.field.card_eq,hsize])
  refine ⟨U,hU,?_⟩
  have hh := congrArg (map (MulAut.conj g).toMonoidHom) he
  rw [hc,map_conj_inv_conj] at hh
  exact hh.symm

private theorem sp4_no_g2_marking
    (a : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) := by
  rintro ⟨b⟩
  have h := Nat.card_congr (a.linearEquiv.symm.trans b.linearEquiv).toEquiv
  have hR : Nat.card (Atlas.G2.Natural.Space S.field.Carrier) = Nat.card S.field.Carrier ^ 6 := by
    rw [Module.natCard_eq_pow_finrank (K := S.field.Carrier), Atlas.G2.Natural.finrank_space]
  simp only [Nat.card_fun,Nat.card_sum,Nat.card_fin,hR] at h
  have he := Nat.pow_right_injective (show 2 ≤ Nat.card S.field.Carrier by
    have := Finite.one_lt_card (α := S.field.Carrier); omega) h
  norm_num at he

/-- The exact source displacement orbit for the actual Sp₄ action. -/
theorem sp4_commutator_line_geometry
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}
    (a : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 a))
    (hline : U₁ = (Coordinates.sp4 a).binarySubspace (f.space 0))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (w : omegaClosure T H)
    (hw : (w : G) ∉ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    ∃ x ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G),
      ⁅V.map (MulAut.conj g).toMonoidHom,zpowers (w : G)⁆ =
        (D.centralQuotientPreimage U₁).map (MulAut.conj (x*g)).toMonoidHom := by
  obtain ⟨U,hU,hc⟩ := sp4_commutator_field_line a f hfixed g n hN w hw
  obtain ⟨x,hx,he⟩ := displacement_line_transporter (.sp4 a) f hline
    (sp4_no_g2_marking a) g U hU
  exact ⟨x,hx,hc.trans he⟩

/-- Apply the reciprocal Sp₄ orbit to the published source consumer, retaining
only the earlier identification of the original line in compatible coordinates. -/
theorem source_seed_eq_sp4
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hcounter : ¬ Proposition1132At D S U₁ H)
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (a : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 a))
    (hline : U₁ = (Coordinates.sp4 a).binarySubspace (f.space 0))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (U : Submodule S.field.Carrier (Fin m → Fin 2 → S.field.Carrier))
    (hU : Module.finrank S.field.Carrier U = 1) (hfix : U ≤ n.fixedSpace)
    (hmarked : n.liftSpace U = D.centralQuotientPreimage U₁) :
    (∃ x ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G),
      (D.centralQuotientPreimage U₁).map (MulAut.conj (x*g)).toMonoidHom =
        D.centralQuotientPreimage U₁) ∧ V.map (MulAut.conj g).toMonoidHom = V :=
  source_seed_eq_of_commutator_line_geometry s p hcounter halt g n U hU hfix hmarked
    (sp4_commutator_line_geometry a f hline hfixed g n hN)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
