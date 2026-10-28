module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Natural
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Nilpotent
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Transfer
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# The radical Frattini and quaternion actions

Subnormal Sylow restriction identifies T ∩ L₀ with a Sylow two-subgroup of
L₀. Its actual image in the local two-core quotient acts irreducibly on the
omega–Frattini quotient and contains a faithful Q₈ action, in both alternatives
of A.3.6. The quotient equivalences intertwine conjugation, so these properties
transfer to the actual radical Frattini quotient.

Frattini's argument factors an actor containing O₂(X) through the normalizer
of each Sylow p-complement. Since O₂(X) acts trivially on X/O₂(X), the
complement's Frattini action inherits both properties. This proves the
L₀-normalizer irreducibility and rules out a cyclic T-automizer using the
quaternion subgroup coming from T ∩ L₀.

The only earlier classification input is the full universal A.3.6 implication.
No Ξ-membership, irreducibility certificate, center–Frattini equality, or
exponent-one hypothesis on a homocyclic core is required.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6 on
pp.43–45, the radical construction preceding 1.3.3 on p.509, and the actions
in the proof of 1.3.8 on pp.513–514.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
namespace CFSG.Quasithin.Chapter1.RadicalActions

private theorem irreducible_transport
    {A B R S : Type*} [Group A] [Group B] [Group R] [Group S]
    (e : A ≃* B) (ρ : R →* MulAut A) (σ : S →* MulAut B)
    (he : ∀ s, ∃ r, ∀ a, e (ρ r a) = σ s (e a))
    (hi : ∀ D : Subgroup B, (∀ s b, b ∈ D → σ s b ∈ D) → D = ⊥ ∨ D = ⊤)
    (D : Subgroup A) (hD : ∀ r a, a ∈ D → ρ r a ∈ D) : D = ⊥ ∨ D = ⊤ := by
  have hmap : ∀ s b, b ∈ D.map e.toMonoidHom → σ s b ∈ D.map e.toMonoidHom := by
    intro s b hb
    obtain ⟨r, hr⟩ := he s
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨ρ r a, hD r a ha, hr a⟩
  rcases hi (D.map e.toMonoidHom) hmap with hb | ht
  · exact Or.inl ((D.map_eq_bot_iff_of_injective e.injective).mp hb)
  · right
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective e.toMonoidHom e.surjective]
    exact ht

private theorem quaternion_transport
    {A B R S : Type*} [Group A] [Group B] [Group R] [Group S]
    (e : A ≃* B) (ρ : R →* MulAut A) (σ : S →* MulAut B)
    (he : ∀ s, ∃ r, ∀ a, e (ρ r a) = σ s (e a))
    (hq : ∃ f : QuaternionGroup 2 →* σ.range, Function.Injective f) :
    ∃ f : QuaternionGroup 2 →* ρ.range, Function.Injective f := by
  obtain ⟨f₀, hf₀⟩ := hq
  let c := MulAut.congr e
  let f := c.symm.toMonoidHom.comp (σ.range.subtype.comp f₀)
  have hf : Function.Injective f :=
    c.symm.injective.comp (σ.range.subtype_injective.comp hf₀)
  have hm (x : QuaternionGroup 2) : f x ∈ ρ.range := by
    obtain ⟨s, hs⟩ := (f₀ x).property
    obtain ⟨r, hr⟩ := he s
    refine ⟨r, ?_⟩
    apply c.injective
    change c (ρ r) = c (c.symm (f₀ x))
    rw [c.apply_symm_apply, ← hs]
    ext b : 1
    change e (ρ r (e.symm b)) = σ s b
    rw [hr, e.apply_symm_apply]
  exact ⟨f.codRestrict ρ.range hm, fun x y hxy => hf (congrArg Subtype.val hxy)⟩

private theorem xiFrattiniAction_subgroup
    {G : Type*} [Group G] {U V X : Subgroup G}
    (hUV : U ≤ V) (hV : V ≤ normalizer X) (u : U) (x : XiFrattiniQuotient X) :
    xiFrattiniAction U X (hUV.trans hV) u x =
      xiFrattiniAction V X hV (inclusion hUV u) x := by
  induction x using QuotientGroup.induction_on with | H x =>
    induction x using QuotientGroup.induction_on with | H x => rfl

private theorem fitting_card_dvd_of_equiv
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B] (e : A ≃* B) :
    Nat.card (fittingSubgroup A) ∣ Nat.card (fittingSubgroup B) := by
  have hle : (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    rintro N ⟨hN, hnil⟩
    apply map_le_iff_le_comap.mp
    let := hnil
    exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩
  rw [Nat.card_congr (e.subgroupMap (fittingSubgroup A)).toEquiv]
  exact card_dvd_of_le hle

universe u
private theorem component_sylow_actions
    {𝒦 : GroupClass.{u}} {E : Type u} [Group E] [Finite E]
    (hE : IsSQTK 𝒦 E) (hO : pCore 2 E = ⊥)
    {C : Subgroup E} (hC : C.IsCComponent) (ha : A36Conclusion C)
    (hn : ¬ IsQuasisimple C) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup C)) (S : Sylow 2 C) :
    (∀ A : Subgroup (omegaCore p C ⧸ frattini (omegaCore p C)),
      (∀ (s : S) x, x ∈ A → omegaFrattiniAction p C s x ∈ A) → A = ⊥ ∨ A = ⊤) ∧
      ∃ f : QuaternionGroup 2 →*
        ((omegaFrattiniAction p C).comp (S : Subgroup C).subtype).range,
        Function.Injective f := by
  rcases RadicalStructure.nonsimple_radical (C := C) ha hn with hnat | hnil
  · exact natural_sylow_actions hnat hd S
  · exact Nilpotent.nilpotent_sylow_actions hE hO hC hnil ha.2 ho hd S

variable {G : Type u} [Group G] [Finite G]

private theorem intersection_equivariant
    {K : Type*} [Group K] {T L₀ : Subgroup G}
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (e : XiQuotient L₀ ≃* K)
    (t : (T ⊓ L₀ : Subgroup G)) (a : XiFrattiniQuotient (XiP p L₀)) :
    let v := (xiPFrattiniEquivCore ho L₀).trans (omegaFrattiniEquiv p e)
    v (xiFrattiniAction (T ⊓ L₀) (XiP p L₀)
      (inf_le_right.trans (XiP_invariant p L₀.le_normalizer)) t a) =
      omegaFrattiniAction p K
        (e (QuotientGroup.mk' _ (inclusion (show T ⊓ L₀ ≤ L₀ from inf_le_right) t)))
        (v a) := by
  dsimp only [MulEquiv.trans_apply]
  rw [xiFrattiniAction_subgroup inf_le_right (XiP_invariant p L₀.le_normalizer),
    xiPFrattiniEquivCore_equivariant, omegaFrattiniEquiv_equivariant]

/-- The actual action of T ∩ L₀ is irreducible and contains an injective Q₈.
The local-family Sylow hypothesis supplies the restricted Sylow two-subgroup. -/
theorem XiP_intersection_actions_of_A36 {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    {T L₀ : Subgroup G} (hL : L₀ ∈ L G T)
    (hQ : IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀))) :
    let ρ := xiFrattiniAction (T ⊓ L₀) (XiP p L₀)
      (inf_le_right.trans (XiP_invariant p L₀.le_normalizer))
    (∀ A : Subgroup (XiFrattiniQuotient (XiP p L₀)),
      (∀ t a, a ∈ A → ρ t a ∈ A) → A = ⊥ ∨ A = ⊤) ∧
      ∃ f : QuaternionGroup 2 →* ρ.range, Function.Injective f := by
  let C := radicalLocalImage T L₀
  let e : XiQuotient L₀ ≃* C := radicalLocalQuotientEquiv hL
  let q : L₀ →* C := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L₀))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨S, hS⟩ := IndexTwo.isSylowIn_inf_of_subnormal hL.2.1 le_sup_left hL.1.subnormal
  let S' : Sylow 2 C := S.mapSurjective hq
  have hC : C.IsCComponent := by
    let := pCore_isNilpotent (p := 2) (G := (L₀ ⊔ T : Subgroup G))
    exact hL.1.map_quotient _
  have ha : A36Conclusion C := proposition_1_2_1_four_earlier_conclusion hA36 hQ hL.1
  have hnC : ¬ IsQuasisimple C := by
    intro hc
    let := hc
    exact hn (IsQuasisimple.of_mulEquiv e.symm)
  have hdC := hd.trans (fitting_card_dvd_of_equiv e)
  have hiq := component_sylow_actions hQ (pCore_quotient_pCore_eq_bot 2)
    hC ha hnC ho hdC S'
  let v := (xiPFrattiniEquivCore ho L₀).trans (omegaFrattiniEquiv p e)
  let ρ := xiFrattiniAction (T ⊓ L₀) (XiP p L₀)
    (inf_le_right.trans (XiP_invariant p L₀.le_normalizer))
  let σ := (omegaFrattiniAction p C).comp (S' : Subgroup C).subtype
  have hv : ∀ s : S', ∃ t : (T ⊓ L₀ : Subgroup G), ∀ a,
      v (ρ t a) = σ s (v a) := by
    intro s
    obtain ⟨l, hl, hls⟩ := s.property
    have hlU : (l : G) ∈ T ⊓ L₀ := hS ▸ mem_map_of_mem L₀.subtype hl
    refine ⟨⟨l, hlU⟩, ?_⟩
    intro a
    change v (ρ ⟨l, hlU⟩ a) = omegaFrattiniAction p C s (v a)
    exact (intersection_equivariant ho e ⟨l, hlU⟩ a).trans
      (congrArg (fun g : C => omegaFrattiniAction p C g (v a)) hls)
  exact ⟨irreducible_transport v ρ σ hv hiq.1, quaternion_transport v ρ σ hv hiq.2⟩

omit [Finite G] in
private theorem xi_irreducible_mono
    {U V X : Subgroup G} (hUV : U ≤ V) (hV : V ≤ normalizer X)
    (hi : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ u a, a ∈ A → xiFrattiniAction U X (hUV.trans hV) u a ∈ A) →
        A = ⊥ ∨ A = ⊤) :
    ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ v a, a ∈ A → xiFrattiniAction V X hV v a ∈ A) → A = ⊥ ∨ A = ⊤ := by
  intro A hA
  apply hi A
  intro u a ha
  rw [xiFrattiniAction_subgroup]
  exact hA (inclusion hUV u) a ha

private theorem normalizer_quaternion {U X : Subgroup G}
    (hU : U ≤ normalizer X) (hcU : X.pCoreIn 2 ≤ U)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hq : IsPGroup p (XiQuotient X))
    (P : Sylow p X)
    (hquat : ∃ f : QuaternionGroup 2 →* (xiFrattiniAction U X hU).range,
      Function.Injective f) :
    let P₀ := (P : Subgroup X).map X.subtype
    ∃ f : QuaternionGroup 2 →*
      (frattiniConjugationAction (U ⊓ normalizer P₀) P₀ inf_le_right).range,
      Function.Injective f := by
  let P₀ := (P : Subgroup X).map X.subtype
  let N := U ⊓ normalizer P₀
  let e := sylowFrattiniEquiv ho hq P
  let ρ := frattiniConjugationAction N P₀ inf_le_right
  let σ := xiFrattiniAction U X hU
  apply quaternion_transport e ρ σ _ hquat
  intro u
  have hN : N ≤ normalizer (X.pCoreIn 2 : Set G) :=
    inf_le_left.trans (hU.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  have hu : (u : G) ∈ X.pCoreIn 2 ⊔ N := normalizer_factor hU hcU hq P ▸ u.property
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hN] at hu
  obtain ⟨c, hc, n, hn, hcn⟩ := hu
  let cU : U := ⟨c, hcU hc⟩
  let nU : U := ⟨n, hn.1⟩
  have heu : u = cU * nU := Subtype.ext hcn.symm
  refine ⟨⟨n, hn⟩, ?_⟩
  intro a
  change e (ρ ⟨n, hn⟩ a) = xiFrattiniAction U X hU u (e a)
  rw [heu, map_mul]
  change e (ρ ⟨n, hn⟩ a) = xiFrattiniAction U X hU cU
    (xiFrattiniAction U X hU nU (e a))
  rw [core_fixes_frattini hU cU hc]
  exact sylowFrattiniEquiv_equivariant hU ho hq P ⟨n, hn⟩ a

private theorem not_isCyclic_of_quaternion
    {A : Type*} [Group A]
    (hq : ∃ f : QuaternionGroup 2 →* A, Function.Injective f) : ¬ IsCyclic A := by
  intro hcyc
  let := hcyc
  obtain ⟨f, hf⟩ := hq
  let := isCyclic_of_injective f hf
  let : CommGroup (QuaternionGroup 2) := IsCyclic.commGroup
  have hc := mul_comm (QuaternionGroup.a 1 : QuaternionGroup 2) (QuaternionGroup.xa 0)
  have hn : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide
  exact hn hc

/-- Irreducibility of the actual T-action in the radical construction. -/
theorem XiP_irreducible_of_A36 {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    {T L₀ : Subgroup G} (hL : L₀ ∈ L G T)
    (hQ : IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) (hT : T ≤ normalizer L₀)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀))) :
    ∀ A : Subgroup (XiFrattiniQuotient (XiP p L₀)),
      (∀ t a, a ∈ A → xiFrattiniAction T (XiP p L₀) (XiP_invariant p hT) t a ∈ A) →
      A = ⊥ ∨ A = ⊤ := by
  exact xi_irreducible_mono inf_le_left (XiP_invariant p hT)
    (XiP_intersection_actions_of_A36 hA36 hL hQ hn ho hd).1

/-- The full local normalizer is irreducible on each Sylow complement's Frattini quotient. -/
theorem XiP_normalizer_irreducible_of_A36 {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    {T L₀ : Subgroup G} (hL : L₀ ∈ L G T)
    (hQ : IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)))
    (P : Sylow p (XiP p L₀)) :
    let P₀ := (P : Subgroup (XiP p L₀)).map (XiP p L₀).subtype
    ∀ A : Subgroup (P₀ ⧸ frattini P₀),
      (∀ g : (L₀ ⊓ normalizer P₀ : Subgroup G), ∀ a ∈ A,
        frattiniConjugationAction (L₀ ⊓ normalizer P₀) P₀ inf_le_right g a ∈ A) →
      A = ⊥ ∨ A = ⊤ := by
  have hi := xi_irreducible_mono inf_le_right (XiP_invariant p L₀.le_normalizer)
    (XiP_intersection_actions_of_A36 hA36 hL hQ hn ho hd).1
  exact normalizer_irreducible (XiP_invariant p L₀.le_normalizer)
    ((pCoreIn_le 2 (XiP p L₀)).trans (XiP_le p L₀)) hi ho
    (XiP_oddQuotient_of_A36 hA36 hL hQ hn ho hd).2.isPGroup P

/-- The action induced by T ∩ L₀ on every complement contains an actual quaternion subgroup. -/
theorem XiP_sylow_frattini_quaternion_of_A36 {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    {T L₀ : Subgroup G} (hL : L₀ ∈ L G T)
    (hQ : IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)))
    (P : Sylow p (XiP p L₀)) :
    let P₀ := (P : Subgroup (XiP p L₀)).map (XiP p L₀).subtype
    ∃ f : QuaternionGroup 2 →*
      (frattiniConjugationAction ((T ⊓ L₀) ⊓ normalizer P₀) P₀ inf_le_right).range,
      Function.Injective f := by
  have hc : (XiP p L₀).pCoreIn 2 ≤ T ⊓ L₀ := by
    have hcL := pCoreIn_mono_of_normalizes (XiP_le p L₀)
      (XiP_invariant p L₀.le_normalizer) (p := 2)
    obtain ⟨S, hS⟩ := IndexTwo.isSylowIn_inf_of_subnormal hL.2.1 le_sup_left hL.1.subnormal
    exact hcL.trans ((pCoreIn_le_sylow L₀ S).trans_eq hS)
  exact normalizer_quaternion (inf_le_right.trans (XiP_invariant p L₀.le_normalizer)) hc ho
    (XiP_oddQuotient_of_A36 hA36 hL hQ hn ho hd).2.isPGroup P
    (XiP_intersection_actions_of_A36 hA36 hL hQ hn ho hd).2

/-- The quaternion subgroup from T ∩ L₀ rules out a cyclic T-automizer. -/
theorem XiP_automizer_not_isCyclic_of_A36 {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    {T L₀ : Subgroup G} (hL : L₀ ∈ L G T)
    (hQ : IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)))
    (P : Sylow p (XiP p L₀)) :
    ¬ IsCyclic (XiEmbedding.automizer T ((P : Subgroup (XiP p L₀)).map (XiP p L₀).subtype)) := by
  have hnot := automizer_not_isCyclic_of_frattini (not_isCyclic_of_quaternion
    (XiP_sylow_frattini_quaternion_of_A36 hA36 hL hQ hn ho hd P))
  intro hc
  let := hc
  exact hnot (isCyclic_of_injective (inclusion (automizer_mono (show T ⊓ L₀ ≤ T from inf_le_left)))
    (inclusion_injective _))

end CFSG.Quasithin.Chapter1.RadicalActions
