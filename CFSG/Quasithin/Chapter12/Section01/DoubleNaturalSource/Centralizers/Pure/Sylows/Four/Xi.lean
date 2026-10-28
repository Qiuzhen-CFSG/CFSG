module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Normalizer
public import CFSG.Quasithin.Chapter1.Section03.Basic
public import Theory.GroupTheory.WreathTwoCoreQuotient
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The actual Xi residual and its escaping overgroup

The quotient of N_LT(J(T)) by its two-core is the binary-plane wreath
actor. Its Sylow two-subgroups are maximal, so a Sylow-invariant subgroup
of the residual Frattini quotient is either trivial or the whole quotient.
This proves every Xi clause for the actual embedded two-residual X, whose
own two-core quotient is C3 x C3. Residual functoriality gives X <= L and
XT = N_LT(J(T)). The original escaping Sylow T0 then constructs
H = <T0,XT> in H(XT), contained in N_G(J(T)) and escaping M.

The private Xi argument specializes the earlier proof in
Chapter15/Section02/SourceChosenGeometry/Residuals/Wreath to its minimal
imports and the binary-plane wreath model; no later Chapter 15 geometry
is imported. All source applications retain the original point, quotient
and Sylows. No MS-classification or module-splitting premise is used.
The full reduced-module splitting, nonnormality of X in H, component
exclusions and final fusion/closure remain with qt-d-double-natural-pure-fusion;
qt-d-double-natural-centralizers retains the earlier-input assembly.

Source: Aschbacher--Smith, 12.1.4, printed p.790; Definition 1.3.1, p.508.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open Chapter1
variable {G : Type*} [Group G] [Finite G]

private instance : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    exact (by decide +kernel : ∀ x : Multiplicative (Fin 2 → ZMod 3), x^3 = 1)

private theorem residual_xi {K : Type*} [Group K] [Finite K]
    (S : Sylow 2 K) (htop : (⊤ : Subgroup K) ∈ H K)
    (e : (K ⧸ pCore 2 K) ≃* WreathTwoResidual.Actor) :
    pResidual 2 K ∈ Xi K (S : Subgroup K) := by
  obtain ⟨r⟩ := WreathTwoResidual.residual_core_quotient_equiv_elementaryNine e
  let : IsElementaryAbelian 3 (XiQuotient (pResidual 2 K)) :=
    IsElementaryAbelian.of_injective r.toMonoidHom r.injective
  have hc : Nat.card (XiQuotient (pResidual 2 K)) = 3 ^ 2 := by
    rw [Nat.card_congr r.toEquiv]
    simp [Nat.card_eq_fintype_card]
  let X := pResidual 2 K
  have hn : (S : Subgroup K) ≤ normalizer (X : Set K) := le_normalizer_of_normal
  refine ⟨isPPerfect_pResidual 2, hn, ?_, ⟨3, by decide, by decide,
    Or.inl ⟨inferInstance, hc⟩⟩, ?_⟩
  · simpa only [pResidual_sup_sylow_eq_top] using htop
  · intro A hA
    let f : X →* XiFrattiniQuotient X :=
      (QuotientGroup.mk' (frattini (XiQuotient X))).comp
        (QuotientGroup.mk' (pCore 2 X))
    have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
      (QuotientGroup.mk'_surjective _)
    let B := A.comap f
    let N := B.map X.subtype
    have hBN : B.Normal := inferInstance
    have hXN : X ≤ normalizer (N : Set K) := by
      have hh := B.le_normalizer_map X.subtype
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
    have hSN : (S : Subgroup K) ≤ normalizer (N : Set K) := by
      apply le_normalizer_iff.mpr
      rintro s hs x ⟨y,hy,rfl⟩
      let z : X := ⟨s * (y : K) * s⁻¹,
        (mem_normalizer_iff.mp (hn hs) (y : K)).mp y.property⟩
      refine ⟨z,?_,rfl⟩
      change f z ∈ A
      have hh := hA (⟨s,hs⟩ : (S : Subgroup K)) (f y) hy
      change xiFrattiniAction (S : Subgroup K) X hn ⟨s,hs⟩
        (QuotientGroup.mk' _ (QuotientGroup.mk' _ y)) ∈ A at hh
      simp only [xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk] at hh
      exact hh
    have hN : N.Normal := normalizer_eq_top_iff.mp (top_unique (by
      rw [← pResidual_sup_sylow_eq_top S]
      exact sup_le hXN hSN))
    let _ := hN
    by_cases hNS : N ≤ (S : Subgroup K)
    · left
      have hNQ : N ≤ pCore 2 K := le_sSup ⟨hN,S.isPGroup'.to_le hNS⟩
      have hBQ : B ≤ pCore 2 X := by
        apply le_sSup
        refine ⟨hBN,?_⟩
        have hb : B ≤ (pCore 2 K).subgroupOf X := by
          intro x hx
          exact hNQ (mem_map_of_mem X.subtype hx)
        exact (pCore_isPGroup (p := 2) (G := K)).comap_subtype.to_le hb
      apply bot_unique
      intro a ha
      obtain ⟨x,rfl⟩ := hf a
      have hx : x ∈ pCore 2 X := hBQ ha
      change f x = 1
      dsimp only [f,MonoidHom.comp_apply]
      have hxq : QuotientGroup.mk' (pCore 2 X) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr hx
      rw [hxq,map_one]
    · right
      have hs : N ⊔ (S : Subgroup K) = ⊤ := by
        rcases (WreathTwoResidual.sylow_isCoatom_of_core_quotient S e).le_iff.mp
          (show (S : Subgroup K) ≤ N ⊔ (S : Subgroup K) from le_sup_right) with h | h
        · exact h
        · exact (hNS (h ▸ le_sup_left)).elim
      have hXN' : X ≤ N := sInf_le ⟨hN,
        isPGroup_quotient_of_sup_eq_top N (S : Subgroup K) S.isPGroup' hs⟩
      apply top_unique
      intro a _
      obtain ⟨x,rfl⟩ := hf a
      obtain ⟨y,hy,hyx⟩ := hXN' x.property
      have hyx' : y = x := X.subtype_injective hyx
      exact hyx' ▸ hy

/-- The actual normalizer of J(T) inside LT, regarded in the original G. -/
@[expose] def normalizerJoin (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G) ⊓
    (L ⊔ (T : Subgroup G))

/-- The source X is the embedded two-residual of that normalizer. -/
@[expose] def residual (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  (pResidual 2 (normalizerJoin T L)).map (normalizerJoin T L).subtype

variable (T : Sylow 2 G) (L : Subgroup G)

omit [Finite G] in
theorem sylow_le_normalizerJoin : (T : Subgroup G) ≤ normalizerJoin T L :=
  le_inf ((T : Subgroup G).le_normalizer.trans
    (normalizer_le_normalizer_elementaryAbelianMaxJ _)) le_sup_right

/-- The residual and the original Sylow generate precisely the normalizer. -/
theorem residual_sup_sylow : residual T L ⊔ (T : Subgroup G) = normalizerJoin T L := by
  have he := congrArg (map (normalizerJoin T L).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype (sylow_le_normalizerJoin T L)))
  simpa only [residual, Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le (sylow_le_normalizerJoin T L),
    ← MonoidHom.range_eq_map, range_subtype] using he

omit [Finite G] in
/-- A nontrivial Thompson subgroup supplies the required nontrivial two-core. -/
theorem normalizerJoin_mem_H (hne : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≠ ⊥) :
    normalizerJoin T L ∈ H G := by
  let J := Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hJN : J ≤ normalizerJoin T L := hJT.trans (sylow_le_normalizerJoin T L)
  have hJQ : J ≤ (normalizerJoin T L).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le hJT) hJN inf_le_left
  exact fun he => hne (bot_unique (hJQ.trans_eq he))

/-- Every clause of Xi uses the original residual and Sylow. -/
theorem residual_mem_Xi
    (hne : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≠ ⊥)
    (e : (normalizerJoin T L ⧸ pCore 2 (normalizerJoin T L)) ≃* WreathTwoResidual.Actor) :
    residual T L ∈ Xi G (T : Subgroup G) := by
  let N := normalizerJoin T L
  have hn := normalizerJoin_mem_H T L hne
  have htop : (⊤ : Subgroup N) ∈ H N := by
    intro hb
    apply hn
    have hm := congrArg (Subgroup.map N.subtype) hb
    rw [map_pCoreIn_of_injective 2 _ N.subtype N.subtype_injective] at hm
    simpa only [←MonoidHom.range_eq_map,range_subtype,Subgroup.map_bot] using hm
  have hx := (mem_Xi_map_iff N.subtype N.subtype_injective).mpr
    (residual_xi (T.subtype (sylow_le_normalizerJoin T L)) htop e)
  change residual T L ∈ Xi G (((T : Subgroup G).subgroupOf N).map N.subtype) at hx
  rwa [map_subgroupOf_eq_of_le (sylow_le_normalizerJoin T L)] at hx

/-- The literal residual quotient, by its own two-core, is C3 x C3. -/
theorem residual_quotient
    (e : (normalizerJoin T L ⧸ pCore 2 (normalizerJoin T L)) ≃* WreathTwoResidual.Actor) :
    Nonempty ((residual T L ⧸ pCore 2 (residual T L)) ≃*
      Multiplicative (Fin 2 → ZMod 3)) := by
  obtain ⟨r⟩ := WreathTwoResidual.residual_core_quotient_equiv_elementaryNine e
  let a := (pResidual 2 (normalizerJoin T L)).equivMapOfInjective
    (normalizerJoin T L).subtype (normalizerJoin T L).subtype_injective
  exact ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans r⟩

/-- Transport the already proved LT-normalizer quotient to its ambient subgroup. -/
noncomputable def normalizerQuotient
    (e : (((normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G)).subgroupOf
      (L ⊔ (T : Subgroup G))) ⧸ pCore 2 ((normalizer
      (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G)).subgroupOf
        (L ⊔ (T : Subgroup G)))) ≃* WreathTwoResidual.Actor) :
    (normalizerJoin T L ⧸ pCore 2 (normalizerJoin T L)) ≃* WreathTwoResidual.Actor := by
  let a : (normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G)).subgroupOf
      (L ⊔ (T : Subgroup G)) ≃* normalizerJoin T L := {
    toFun := fun x => ⟨x.val.val,x.property,x.val.property⟩
    invFun := fun x => ⟨⟨x.val,x.property.2⟩,x.property.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  exact (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans e

omit [Finite G] in
/-- The source residual stays in the original component. -/
theorem residual_le_component (hL : IsPPerfect 2 L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) : residual T L ≤ L := by
  have he := embedded_pResidual_join_pGroup L (T : Subgroup G) hL T.isPGroup' hTL
  exact (embedded_pResidual_mono 2 (show normalizerJoin T L ≤ L ⊔ (T : Subgroup G) from
    inf_le_right)).trans he.le

omit [Finite G] in
/-- The escaping Sylow and XT generate an actual member of H(XT),
inside the original full Thompson normalizer. -/
theorem escaping_overgroup (P : Sylow 2 G)
    (hne : elementaryAbelianMaxJ (T : Subgroup G) ≠ ⊥)
    (hP : (P : Subgroup G) ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ (P : Subgroup G) ≤ normalizer (L : Set G)) :
    let U := (P : Subgroup G) ⊔ normalizerJoin T L
    U ∈ HOver G (normalizerJoin T L : Set G) ∧
      normalizerJoin T L < U ∧
      U ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      ¬ U ≤ normalizer (L : Set G) := by
  let U := (P : Subgroup G) ⊔ normalizerJoin T L
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hJN : J ≤ normalizerJoin T L := hJT.trans (sylow_le_normalizerJoin T L)
  have hUN : U ≤ normalizer (J : Set G) := sup_le hP inf_le_left
  have hJU : J ≤ U := hJN.trans le_sup_right
  have hJQ : J ≤ U.pCoreIn 2 := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hJT) hJU hUN
  have hH : U ∈ H G := fun he => hne (bot_unique (hJQ.trans_eq he))
  refine ⟨⟨hH,fun _ hx => mem_sup_right hx⟩,lt_of_le_of_ne le_sup_right ?_,hUN,?_⟩
  · intro he
    apply hout
    have hPN : (P : Subgroup G) ≤ normalizerJoin T L := he ▸ le_sup_left
    exact hPN.trans (inf_le_right.trans (sup_le L.le_normalizer hTL))
  · exact fun hh => hout (le_sup_left.trans hh)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original contrary ambient Sylow branch constructs the source Xi
member with its precise join and elementary-nine quotient. -/
theorem doubleNatural_four_pure_xi_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      let X := PureFourXi.residual T L
      let N := PureFourXi.normalizerJoin T L
      X ∈ Chapter1.Xi G (T : Subgroup G) ∧ X ⊔ (T : Subgroup G) = N ∧
        Nonempty ((N ⧸ pCore 2 N) ≃* WreathTwoResidual.Actor) ∧
        Nonempty ((X ⧸ pCore 2 X) ≃* Multiplicative (Fin 2 → ZMod 3)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  obtain ⟨e⟩ := D.doubleNatural_four_pure_thompson_normalizer_model_of_many h hmany B S w hw hp hfix hf
  let f := PureFourXi.normalizerQuotient T L e
  have hne : elementaryAbelianMaxJ (T : Subgroup G) ≠ ⊥ := by
    intro he
    have hm := (D.doubleNatural_four_pure_thompson_moves_of_many h hmany B S w hw hp hfix hf).2
    exact hm (he ▸ bot_le)
  exact ⟨PureFourXi.residual_mem_Xi T L hne f, PureFourXi.residual_sup_sylow T L,
    ⟨f⟩, PureFourXi.residual_quotient T L f⟩
/-- The contrary original Sylow gives the exact overgroup H = <T0,XT>
used in the source embedding argument. Xi membership and the literal
containment X <= L have no classification premise. -/
theorem doubleNatural_four_pure_xi_overgroup_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      let X := PureFourXi.residual T L
      X ∈ Chapter1.Xi G (T : Subgroup G) ∧ X ≤ L ∧
        ∃ P : Sylow 2 G, B.pointSylow w < (P : Subgroup G) ∧
          (P : Subgroup G) ≤ B.pointCentralizer w ∧
          (P : Subgroup G) ⊓ normalizer (L : Set G) = B.pointSylow w ∧
          let U := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
          U ∈ Chapter1.HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
            X ⊔ (T : Subgroup G) < U ∧
            U ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
            ¬ U ≤ normalizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  have hx := (D.doubleNatural_four_pure_xi_of_many h hmany B S w hw hp hfix hf).1
  obtain ⟨_,P,hlt,hPC,hPM,hout,hN⟩ :=
    D.doubleNatural_four_pure_thompson_escape_of_many h hmany B S w hw hp hfix hf
  have hne : elementaryAbelianMaxJ (T : Subgroup G) ≠ ⊥ := by
    intro he
    exact (D.doubleNatural_four_pure_thompson_moves_of_many h hmany B S w hw hp hfix hf).2
      (he ▸ bot_le)
  refine ⟨hx,PureFourXi.residual_le_component T L h.maximal_faithful.2.1.2.1
    D.sylow_normalizes_component,P,hlt,hPC,hPM,?_⟩
  dsimp only
  rw [PureFourXi.residual_sup_sylow]
  exact PureFourXi.escaping_overgroup T L P hne (le_sup_right.trans hN)
    D.sylow_normalizes_component hout

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
