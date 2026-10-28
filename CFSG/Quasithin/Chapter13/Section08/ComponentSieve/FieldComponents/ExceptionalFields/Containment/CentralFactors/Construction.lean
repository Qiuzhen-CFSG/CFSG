module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Lifting
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.MarkedInternalProduct
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PCoreImage

/-!
# Constructing the exceptional centralizer factor

In the field-four branch, the actual PSL₂(4) ≃ A₅ comparison makes the
conjugation action of a two-perfect subgroup inner: its permutation sign is
trivial. Centerlessness then splits K*D* as the product of K* and its actual
relative centralizer, with both coordinate markings. Projection from D*
proves that this centralizer is two-perfect.

The ambient candidate is O² of the preimage of C_{D*}(K*). Its residual,
T-action and star image are proved here. Borel geometry must still place the
relative centralizer inside D*, and the marked E₉ action must identify its
residual lift with L₀ or L₁,+. Those statements are not hypotheses hidden in
the construction and are not asserted by this module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.20, printed p.955; compare 13.7.5(7), printed p.938.
-/

open Subgroup
open CFSG.Quasithin.Chapter13.Section08

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.CentralFactors

private theorem inner_of_twoPerfect {G : Type*} [Group G]
    (K D : Subgroup G) [K.Normal]
    (eK : K ≃* alternatingGroup (Fin 5)) (hD : IsPPerfect 2 D)
    (d : D) : (MulAut.conjNormal d.val : MulAut K) ∈ MulAut.innerSubgroup K := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := alternatingGroup (Fin 5)
  have htwo : IsPGroup 2 (Equiv.Perm (Fin 5) ⧸ A) := by
    apply IsPGroup.of_card (n := 1)
    rw [← A.index_eq_card, alternatingGroup.index_eq_two]
    rfl
  have houter : IsPGroup 2 (MulAut.Outer A) := by
    apply htwo.of_surjective (MulAut.outerAction A)
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
    obtain ⟨σ, rfl⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      5 (by decide) (by decide)).surjective a
    exact ⟨QuotientGroup.mk' A σ, rfl⟩
  let f : D →* MulAut.Outer K := (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp
    ((MulAut.conjNormal : G →* MulAut K).comp D.subtype)
  have hf := hD.hom_eq_one_of_isPGroup
    (houter.of_equiv (MulAut.outerCongr eK).symm) f
  exact (QuotientGroup.eq_one_iff _).mp (congrArg (fun z : D →* MulAut.Outer K => z d) hf)


private theorem disjoint_centralizer_of_five {G : Type*} [Group G]
    (K : Subgroup G) (eK : K ≃* alternatingGroup (Fin 5)) :
    Disjoint K (centralizer (K : Set G)) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  have hz : eK ⟨x, hx.1⟩ ∈ center (alternatingGroup (Fin 5)) := by
    rw [mem_center_iff]
    intro a
    obtain ⟨k, rfl⟩ := eK.surjective a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((mem_centralizer_iff.mp hx.2) k k.property)
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hz
  exact congrArg Subtype.val (eK.injective (hz.trans eK.map_one.symm))

private theorem central_product {G : Type*} [Group G]
    (K D : Subgroup G) [K.Normal]
    (eK : K ≃* alternatingGroup (Fin 5)) (hD : IsPPerfect 2 D) :
    let C := (K ⊔ D) ⊓ centralizer (K : Set G)
    ∃ e : (K ⊔ D : Subgroup G) ≃* K × C,
      (K.subgroupOf (K ⊔ D)).map e.toMonoidHom = (⊤ : Subgroup K).prod ⊥ ∧
      (C.subgroupOf (K ⊔ D)).map e.toMonoidHom = (⊥ : Subgroup K).prod ⊤ ∧
      IsPPerfect 2 C := by
  intro C
  have hinner : D ≤ K ⊔ centralizer (K : Set G) := by
    rw [← MulAut.conjNormal_comap_innerSubgroup K]
    intro d hd
    exact inner_of_twoPerfect K D eK hD ⟨d, hd⟩
  have hsup : K ⊔ C = K ⊔ D := by
    apply le_antisymm (sup_le le_sup_left inf_le_left)
    refine sup_le le_sup_left ?_
    intro d hd
    obtain ⟨k, hk, c, hc, hkc⟩ := mem_sup_of_normal_left.mp (hinner hd)
    have hcD : c ∈ K ⊔ D := by
      have hc' : c = k⁻¹ * d := by rw [← hkc]; group
      rw [hc']
      exact (K ⊔ D).mul_mem ((show K ≤ K ⊔ D from le_sup_left) (K.inv_mem hk))
        ((show D ≤ K ⊔ D from le_sup_right) hd)
    rw [← hkc]
    exact (K ⊔ C).mul_mem ((show K ≤ K ⊔ C from le_sup_left) hk)
      ((show C ≤ K ⊔ C from le_sup_right) ⟨hcD, hc⟩)
  obtain ⟨e, heK, heC⟩ := Theory.GroupTheory.exists_marked_internalProductEquiv
    (K ⊔ D) K C hsup ((disjoint_centralizer_of_five K eK).mono_right inf_le_right)
      (le_centralizer_iff.mpr inf_le_right)
  refine ⟨e, heK, heC, ?_⟩
  let f : (K ⊔ D : Subgroup G) →* C := (MonoidHom.snd K C).comp e.toMonoidHom
  let d : D →* C := f.comp (inclusion (show D ≤ K ⊔ D from le_sup_right))
  have hfK (k : K) : f (inclusion (show K ≤ K ⊔ D from le_sup_left) k) = 1 := by
    have hm : e (inclusion (show K ≤ K ⊔ D from le_sup_left) k) ∈
        (⊤ : Subgroup K).prod ⊥ := by
      rw [← heK]
      exact mem_map.mpr ⟨_, k.property, rfl⟩
    exact hm.2
  apply hD.of_surjective d
  intro c
  let x := e.symm (1, c)
  obtain ⟨k, hk, y, hy, hky⟩ := mem_sup_of_normal_left.mp x.property
  refine ⟨⟨y, hy⟩, ?_⟩
  have hx : x = inclusion (show K ≤ K ⊔ D from le_sup_left) ⟨k, hk⟩ *
      inclusion (show D ≤ K ⊔ D from le_sup_right) ⟨y, hy⟩ := Subtype.ext hky.symm
  have he : f x = c := congrArg Prod.snd (e.apply_symm_apply (1, c))
  rw [hx, map_mul, hfK, one_mul] at he
  exact he

private theorem corrected_inverter {G : Type*} [Group G]
    (K X : Subgroup G) [K.Normal] (t : G)
    (ht : (MulAut.conjNormal t : MulAut K) ∈ MulAut.innerSubgroup K)
    (hX : X ≤ centralizer (K : Set G))
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) :
    ∃ c ∈ centralizer (K : Set G), ∀ x ∈ X, c * x * c⁻¹ = x⁻¹ := by
  obtain ⟨k, hk⟩ := ht
  have hk' : (MulAut.conjNormal k.val : MulAut K) = MulAut.conjNormal t :=
    MulAut.conjNormal_val.trans hk
  refine ⟨k.val⁻¹ * t, ?_, ?_⟩
  · rw [← MulAut.conjNormal_ker_eq_centralizer K]
    change MulAut.conjNormal (k.val⁻¹ * t) = 1
    rw [map_mul, map_inv, hk', inv_mul_cancel]
  · intro x hx
    calc
      (k.val⁻¹ * t) * x * (k.val⁻¹ * t)⁻¹ =
          k.val⁻¹ * (t * x * t⁻¹) * k.val := by simp [mul_assoc]
      _ = k.val⁻¹ * x⁻¹ * k.val := by rw [hinv x hx]
      _ = x⁻¹ := by
        have hc := mem_centralizer_iff.mp (hX (X.inv_mem hx)) k.val k.property
        rw [mul_assoc, ← hc, inv_mul_cancel_left]

/-- Construct all clauses of the external-X configuration when an inner
actor inverts X*. The inverter in the centralizer is constructed by correcting
the given actor by its implementing element of K*. -/
public theorem external_configuration_of_star_inversion {G : Type*} [Group G]
    (H K L₁ X T : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 5))
    (hH : H = K ⊔ L₁ ⊔ T) (hX : X ≤ L₁)
    (hpX : IsPPerfect 2 X) (hL₁X : L₁ ≤ normalizer (X : Set G))
    (hTX : T ≤ normalizer (X : Set G))
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (hXC : Source.starImage H X ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)))
    (hne : Source.starImage H X ≠ ⊥)
    (t : Source.Hstar H)
    (hinner : (MulAut.conjNormal t : MulAut (Source.starImage H K)) ∈
      MulAut.innerSubgroup (Source.starImage H K))
    (hinv : ∀ x ∈ Source.starImage H X, t * x * t⁻¹ = x⁻¹) :
    ¬ X ≤ K ∧ (X.subgroupOf H).Normal ∧
      ∃ c ∈ centralizer (Source.starImage H K : Set (Source.Hstar H)),
        ∀ x ∈ Source.starImage H X, c * x * c⁻¹ = x⁻¹ := by
  have hKH : K ≤ H := by rw [hH]; exact le_sup_left.trans le_sup_left
  have hL₁H : L₁ ≤ H := by rw [hH]; exact le_sup_right.trans le_sup_left
  have hXH := hX.trans hL₁H
  have hQ : Source.QH H ≤ T := by
    rw [← hS]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal S)
  have hKX := ComponentSieve.FieldComponents.ExceptionalFields.Containment.Lifting.normalizes_of_star_centralizing
    H K X hKH hXH hpX (hQ.trans hTX) (le_centralizer_iff.mp hXC)
  have hHX : H ≤ normalizer (X : Set G) := by
    rw [hH]
    exact sup_le (sup_le hKX hL₁X) hTX
  refine ⟨?_, normal_subgroupOf_of_le_normalizer hHX,
    corrected_inverter _ _ t hinner hXC hinv⟩
  intro hXK
  apply hne
  apply le_bot_iff.mp
  have hXKstar : Source.starImage H X ≤ Source.starImage H K :=
    map_mono (subgroupOf_mono H hXK)
  exact (le_inf hXKstar hXC).trans (disjoint_iff_inf_le.mp
    (disjoint_centralizer_of_five (Source.starImage H K) eK))

variable {G : Type*} [Group G]
/-- The actual centralizer in K*D*. -/
@[expose] public def starCentralizer (H K D : Subgroup G) : Subgroup (Source.Hstar H) :=
  (Source.starImage H K ⊔ Source.starImage H D) ⊓
    centralizer (Source.starImage H K : Set (Source.Hstar H))

/-- The centralizer preimage inside D ∩ H. Source applications supply D ≤ H. -/
@[expose] public def centralizerPreimage (H K D : Subgroup G) : Subgroup H :=
  D.subgroupOf H ⊓
    (centralizer (Source.starImage H K : Set (Source.Hstar H))).comap
      (QuotientGroup.mk' (pCore 2 H))

/-- The embedded two-residual of the centralizer preimage. -/
@[expose] public def centralFactor (H K D : Subgroup G) : Subgroup G :=
  ((pResidual 2 (centralizerPreimage H K D)).map (centralizerPreimage H K D).subtype).map H.subtype

private theorem preimage_image (H K D : Subgroup G) :
    (centralizerPreimage H K D).map (QuotientGroup.mk' (pCore 2 H)) =
      Source.starImage H D ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨mem_map.mpr ⟨y, hy.1, rfl⟩, hy.2⟩
  · rintro ⟨⟨y, hy, rfl⟩, hc⟩
    exact mem_map.mpr ⟨y, ⟨hy, hc⟩, rfl⟩

/-- The candidate is a subgroup of the source D. -/
public theorem centralFactor_le (H K D : Subgroup G) : centralFactor H K D ≤ D := by
  rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
  exact z.property.1

/-- Taking the actual residual supplies two-perfectness. -/
public theorem centralFactor_isPPerfect [Finite G] (H K D : Subgroup G) : IsPPerfect 2 (centralFactor H K D) := by
  let R := (pResidual 2 (centralizerPreimage H K D)).map (centralizerPreimage H K D).subtype
  exact (isPPerfect_embedded_pResidual 2 (centralizerPreimage H K D)).of_surjective
    (H.subtype.subgroupMap R) (H.subtype.subgroupMap_surjective R)

/-- Residuals commute with the actual star map. -/
public theorem centralFactor_starImage [Finite G] (H K D : Subgroup G) :
    Source.starImage H (centralFactor H K D) =
      (pResidual 2 (Source.starImage H D ⊓
        centralizer (Source.starImage H K : Set (Source.Hstar H)) :
          Subgroup (Source.Hstar H))).map
        (Source.starImage H D ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H))).subtype := by
  unfold Source.starImage centralFactor
  rw [subgroupOf, comap_map_eq_self_of_injective H.subtype_injective,
    map_embedded_pResidual, preimage_image]
  rfl

/-- T-invariance is inherited from the centralizer and characteristic residual. -/
public theorem centralFactor_T_invariant (H K D T : Subgroup G) [(Source.starImage H K).Normal]
    (hDH : D ≤ H) (hTH : T ≤ H) (hTD : T ≤ normalizer (D : Set G)) :
    T ≤ normalizer (centralFactor H K D : Set G) := by
  have hTD' : T.subgroupOf H ≤ normalizer (D.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hDH]
    exact subgroupOf_mono H hTD
  have hTP : T.subgroupOf H ≤ normalizer (centralizerPreimage H K D : Set H) :=
    (le_inf hTD' le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  have hTR := hTP.trans (normalizer_le_normalizer_characteristic_image
    (centralizerPreimage H K D) (pResidual 2 (centralizerPreimage H K D)))
  rw [← map_subgroupOf_eq_of_le hTH]
  exact (map_mono hTR).trans (le_normalizer_map H.subtype)

/-- A two-perfect source subgroup has two-perfect star image. -/
public theorem star_isPPerfect (H D : Subgroup G) (hDH : D ≤ H) (hD : IsPPerfect 2 D) :
    IsPPerfect 2 (Source.starImage H D) := by
  have hp := hD.of_surjective (subgroupOfEquivOfLe hDH).symm.toMonoidHom
    (subgroupOfEquivOfLe hDH).symm.surjective
  exact hp.of_surjective ((QuotientGroup.mk' (pCore 2 H)).subgroupMap (D.subgroupOf H))
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _)

/-- T normalizes the constructed relative centralizer. -/
public theorem starCentralizer_T_invariant (H K D T : Subgroup G) [(Source.starImage H K).Normal]
    (hDH : D ≤ H) (hTD : T ≤ normalizer (D : Set G)) :
    Source.starImage H T ≤ normalizer (starCentralizer H K D : Set (Source.Hstar H)) := by
  have hTD' : T.subgroupOf H ≤ normalizer (D.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hDH]
    exact subgroupOf_mono H hTD
  have hTDs : Source.starImage H T ≤ normalizer
      (Source.starImage H D : Set (Source.Hstar H)) :=
    (map_mono hTD').trans (le_normalizer_map _)
  have hTJ : Source.starImage H T ≤ normalizer
      ((Source.starImage H K ⊔ Source.starImage H D : Subgroup (Source.Hstar H)) : Set (Source.Hstar H)) :=
    (le_inf le_normalizer_of_normal hTDs).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact (le_inf hTJ le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf

/-- The actual field-four comparison supplies the inner action. -/
public theorem linear_two_four_inner_action
    (H K D : Subgroup G) [(Source.starImage H K).Normal]
    (hDH : D ≤ H) (hD : IsPPerfect 2 D)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : Source.starImage H K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (d : Source.starImage H D) :
    (MulAut.conjNormal d.val : MulAut (Source.starImage H K)) ∈
      MulAut.innerSubgroup (Source.starImage H K) := by
  obtain ⟨e₅⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  exact inner_of_twoPerfect _ _ (eK.trans e₅) (star_isPPerfect H D hDH hD) d

/-- The centralizer factor and both product coordinates are constructed. -/
public theorem linear_two_four_centralizer_product
    (H K D : Subgroup G) [(Source.starImage H K).Normal]
    (hDH : D ≤ H) (hD : IsPPerfect 2 D)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : Source.starImage H K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    ∃ e : (Source.starImage H K ⊔ Source.starImage H D : Subgroup (Source.Hstar H)) ≃*
        Source.starImage H K × starCentralizer H K D,
      ((Source.starImage H K).subgroupOf (Source.starImage H K ⊔ Source.starImage H D)).map
          e.toMonoidHom = (⊤ : Subgroup (Source.starImage H K)).prod ⊥ ∧
      ((starCentralizer H K D).subgroupOf (Source.starImage H K ⊔ Source.starImage H D)).map
          e.toMonoidHom = (⊥ : Subgroup (Source.starImage H K)).prod ⊤ ∧
      IsPPerfect 2 (starCentralizer H K D) := by
  obtain ⟨e₅⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  exact central_product _ _ (eK.trans e₅) (star_isPPerfect H D hDH hD)

/-- Once Borel geometry places the centralizer inside D*, the residual lift
has precisely that image. -/
public theorem centralFactor_starImage_eq [Finite G] (H K D : Subgroup G)
    (hplace : starCentralizer H K D ≤ Source.starImage H D)
    (hperfect : IsPPerfect 2 (starCentralizer H K D)) :
    Source.starImage H (centralFactor H K D) = starCentralizer H K D := by
  have hc : Source.starImage H D ⊓
      centralizer (Source.starImage H K : Set (Source.Hstar H)) = starCentralizer H K D :=
    le_antisymm (inf_le_inf_right _ le_sup_right) (le_inf hplace inf_le_right)
  rw [centralFactor_starImage, hc, (pResidual_eq_top_iff _ _).mpr hperfect,
    ← MonoidHom.range_eq_map, range_subtype]

private theorem perfect_le_of_le_join (D K Q : Subgroup G)
    (hD : IsPPerfect 2 D) (hK : IsPPerfect 2 K) (hQ : IsPGroup 2 Q)
    (hQK : Q ≤ normalizer (K : Set G)) (hDle : D ≤ K ⊔ Q) : D ≤ K := by
  have hres := embedded_pResidual_mono 2 hDle
  rw [(pResidual_eq_top_iff 2 D).mpr hD,
    ← MonoidHom.range_eq_map, range_subtype,
    embedded_pResidual_join_pGroup K Q hK hQ hQK] at hres
  exact hres

/-- For the two-perfect local subgroups, containment in the literal star
quotient lifts to containment before quotienting. -/
public theorem le_of_star_le (H K D : Subgroup G) [(K.subgroupOf H).Normal]
    (hKH : K ≤ H) (hDH : D ≤ H) (hK : IsPPerfect 2 K) (hD : IsPPerfect 2 D)
    (hstar : Source.starImage H D ≤ Source.starImage H K) : D ≤ K := by
  have hpD := hD.of_surjective (subgroupOfEquivOfLe hDH).symm.toMonoidHom
    (subgroupOfEquivOfLe hDH).symm.surjective
  have hpK := hK.of_surjective (subgroupOfEquivOfLe hKH).symm.toMonoidHom
    (subgroupOfEquivOfLe hKH).symm.surjective
  have hle : D.subgroupOf H ≤ K.subgroupOf H ⊔ pCore 2 H := by
    have h := (map_le_iff_le_comap).mp hstar
    rwa [Source.starImage, comap_map_eq, QuotientGroup.ker_mk'] at h
  have h := perfect_le_of_le_join _ _ _ hpD hpK pCore_isPGroup le_normalizer_of_normal hle
  intro d hd
  exact h (show (⟨d, hDH hd⟩ : H) ∈ D.subgroupOf H from hd)

/-- The two-core error in the source inversion is killed by the literal
star quotient once X is normal in H. -/
public theorem star_inverts_of_core_error (H X : Subgroup G) (hXH : X ≤ H)
    (hHX : H ≤ normalizer (X : Set G)) (t : H)
    (hinv : ∀ x ∈ X, t.val * x * t.val⁻¹ * x ∈ X.pCoreIn 2) :
    ∀ x ∈ Source.starImage H X,
      QuotientGroup.mk' (pCore 2 H) t * x *
        (QuotientGroup.mk' (pCore 2 H) t)⁻¹ = x⁻¹ := by
  have hcore : X.pCoreIn 2 ≤ Source.QH H := pCoreIn_mono_of_normalizes hXH hHX
  rintro x ⟨y, hy, rfl⟩
  apply eq_inv_iff_mul_eq_one.mpr
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  obtain ⟨z, hz, he⟩ := hcore (hinv y.val hy)
  have he' : z = t * y * t⁻¹ * y := Subtype.ext he
  exact he' ▸ hz

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.CentralFactors
