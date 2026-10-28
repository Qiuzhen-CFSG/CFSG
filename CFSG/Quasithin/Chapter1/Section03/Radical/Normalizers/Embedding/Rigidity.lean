module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Local
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Marked
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Rigidity.Images

/-!
# Rigidity of X in the containing C-component

For the component K supplied by `Embedding.exists_normal_component`,
containment of X in the solvable radical identifies X with Ξ_p(K).
Indeed its quotient image is precisely Ω₁(O_p(K/O₂(K))). Since T is Sylow
and normalizes K, O₂(K) lies in T and normalizes X. Two-perfectness then
recovers X as the two-residual of the full omega preimage.

Consequently radical containment forces normality, and normality forces
characteristicity because X is solvable. If K is normal in N, the latter
gives N ≤ N_G(X) = M, contradicting the escaping normalizer. Finally,
X is normal in Y = N_L(R)^∞, so Y ≤ K is strict.

The source theorem's earlier local maximality and LT uniqueness are used
upstream to identify M = N_G(L) = N_G(X). The final theorem takes this
normalizer equality and the residual inclusion X ≤ Y explicitly, along
with the universal complete A.3.6 statement. It discharges the quotient
SQTK premise from the simple QTKE setup. No CenterFrattini equality is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed p.513, using A.3.6 and 1.2.1(4).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Rigidity
open Section02
variable {G : Type*} [Group G] [Finite G]

private theorem omega_map_equiv {A B : Type*} [Group A] [Group B]
    (p k : ℕ) (e : A ≃* B) :
    (omega A (p := p) k).map e.toMonoidHom = omega B (p := p) k := by
  rw [omega, omega, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using congrArg e hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    simpa using congrArg e.symm hx

private theorem omega_core_map_equiv {A B : Type*} [Group A] [Group B]
    (p : ℕ) (e : A ≃* B) :
    (((omega (pCore p A) (p := p) 1).map (pCore p A).subtype).map e.toMonoidHom) =
      (omega (pCore p B) (p := p) 1).map (pCore p B).subtype := by
  have hp : (pCore p A).map (e : A →* B) = pCore p B := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using pCore_map_iso p e
  let ep : pCore p A ≃* pCore p B :=
    (e.subgroupMap (pCore p A)).trans (MulEquiv.subgroupCongr hp)
  have he := congrArg (map (pCore p B).subtype) (omega_map_equiv p 1 ep)
  have hc : (pCore p B).subtype.comp ep.toMonoidHom =
      e.toMonoidHom.comp (pCore p A).subtype := by
    ext x
    change ((ep x : pCore p B) : B) = e x
    dsimp only [ep]
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    exact e.coe_subgroupMap_apply (pCore p A) x
  simpa only [map_map, hc] using he

/-- The intrinsic omega image recovers the actual characteristic radical. -/
theorem eq_XiP_of_le_solvableRadical
    {E : Type*} [Group E] [Finite E] {A : Subgroup E}
    {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (T : Sylow 2 G) {X K : Subgroup G}
    (hX : XiMember T X) (hq : XiOddQuotient p (XiQuotient X))
    (hXK : X ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : XiQuotient K ≃* A) (hc : A36Conclusion A)
    (hR : X ≤ (solvableRadical K).map K.subtype) : X = XiP p K := by
  apply eq_XiP_of_image_eq_omega p T hX hXK hTK
  apply map_injective (f := e.toMonoidHom) e.injective
  have he := radical_image_eq_omega hp3 hX hq hXK hTK e hc hR
  rw [MonoidHom.comp_assoc, MonoidHom.range_comp,
    MonoidHom.range_comp, inclusion_range] at he
  exact he.trans (omega_core_map_equiv p e).symm

/-- Normality of a Xi member in this component implies characteristicity,
by solvability and the full odd-core structure, rather than by assumption. -/
theorem characteristic_of_normal
    {E : Type*} [Group E] [Finite E] {A : Subgroup E}
    {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (T : Sylow 2 G) {X K : Subgroup G}
    (hX : XiMember T X) (hq : XiOddQuotient p (XiQuotient X))
    (hXK : X ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : XiQuotient K ≃* A) (hc : A36Conclusion A)
    (hn : (X.subgroupOf K).Normal) : (X.subgroupOf K).Characteristic := by
  have hs : Group.IsSolvable (X.subgroupOf K) := by
    let := hX.isSolvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hXK).toMonoidHom) (subgroupOfEquivOfLe hXK).injective
  have hr := map_mono (f := K.subtype) (le_solvableRadical (X.subgroupOf K) hn hs)
  rw [map_subgroupOf_eq_of_le hXK] at hr
  rw [eq_XiP_of_le_solvableRadical hp3 T hX hq hXK hTK e hc hr]
  infer_instance

/-- Radical containment forces normality via the identification with Ξ_p(K). -/
theorem normal_of_le_solvableRadical
    {E : Type*} [Group E] [Finite E] {A : Subgroup E}
    {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (T : Sylow 2 G) {X K : Subgroup G}
    (hX : XiMember T X) (hq : XiOddQuotient p (XiQuotient X))
    (hXK : X ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : XiQuotient K ≃* A) (hc : A36Conclusion A)
    (hR : X ≤ (solvableRadical K).map K.subtype) : (X.subgroupOf K).Normal := by
  rw [eq_XiP_of_le_solvableRadical hp3 T hX hq hXK hTK e hc hR]
  infer_instance

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Rigidity

open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The three rigidity conclusions for the component constructed in `Local`.
The only earlier classification input is the complete universal A.3.6 contract. -/
theorem escaping_component_rigidity
    {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA36 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → A36Conclusion B)
    {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (L : Subgroup G) (T : Sylow 2 G)
    (hX : XiMember T (XiP p L)) (hq : XiOddQuotient p (XiQuotient (XiP p L)))
    (C : Subgroup (radicalCore p L T)) [C.Characteristic] (hC : C ≠ ⊥)
    (K : Subgroup G)
    (hK : K ∈ cComponentsIn (normalizer (C.map (radicalCore p L T).subtype : Set G)))
    (hn : (K.subgroupOf
      (normalizer (C.map (radicalCore p L T).subtype : Set G))).Normal)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hXY : XiP p L ≤ normalizerResidual L (radicalCore p L T))
    (hYK : normalizerResidual L (radicalCore p L T) ≤ K)
    (hM : normalizer (L : Set G) = normalizer (XiP p L : Set G))
    (hescape : ¬ normalizer (C.map (radicalCore p L T).subtype : Set G) ≤
      normalizer (L : Set G)) :
    ¬ ((XiP p L).subgroupOf K).Normal ∧
      ¬ XiP p L ≤ (solvableRadical K).map K.subtype ∧
      normalizerResidual L (radicalCore p L T) < K := by
  let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
  let e := componentQuotientEquiv hK.1 hK.2
  have hc := proposition_1_2_1_four_earlier_conclusion hA36
    (characteristic_normalizer_quotient_sqtk hG p L T C hC) hK.2
  have hXK := hXY.trans hYK
  have hnot : ¬ ((XiP p L).subgroupOf K).Normal := by
    intro hnormal
    have hchar := Rigidity.characteristic_of_normal hp3 T hX hq hXK hTK e hc hnormal
    let := hchar
    have hNX : N ≤ normalizer (XiP p L : Set G) := by
      have hNK := (normal_subgroupOf_iff_le_normalizer hK.1).mp hn
      have hh := normalizer_le_normalizer_characteristic_image K ((XiP p L).subgroupOf K)
      rw [map_subgroupOf_eq_of_le hXK] at hh
      exact hNK.trans hh
    exact hescape (hM.symm ▸ hNX)
  refine ⟨hnot, ?_, lt_of_le_of_ne hYK ?_⟩
  · intro hr
    exact hnot (Rigidity.normal_of_le_solvableRadical hp3 T hX hq hXK hTK e hc hr)
  · intro he
    apply hnot
    rw [← he]
    exact normal_subgroupOf_of_le_normalizer
      ((normalizerResidual_le L _).trans (XiP_invariant p L.le_normalizer))

/-- Apply the rigidity argument to the component returned by the published
construction, retaining its uniqueness, relative normality and marked embedding.
The maximal local-family witness is the genuine `LStar` used in 1.3.8. -/
theorem exists_rigid_component
    {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA36 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → A36Conclusion B)
    (hA312 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ (S : Sylow 2 A) (B : Subgroup A),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (hA38 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ B : Subgroup A, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set A)).index = 2 ∧ NonnormalCComponentModel B)
    {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (L : Subgroup G) (T : Sylow 2 G)
    (hL : L ∈ LStar G T) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hX : XiMember T (XiP p L)) (hq : XiOddQuotient p (XiQuotient (XiP p L)))
    (hY : ((normalizerResidual L (radicalCore p L T)).subgroupOf
      ((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G))).IsCComponent)
    (hXY : XiP p L ≤ normalizerResidual L (radicalCore p L T))
    (C : Subgroup (radicalCore p L T)) [C.Characteristic] (hC : C ≠ ⊥)
    (hM : normalizer (L : Set G) = normalizer (XiP p L : Set G))
    (hescape : ¬ normalizer (C.map (radicalCore p L T).subtype : Set G) ≤
      normalizer (L : Set G)) :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    let Y := normalizerResidual L (radicalCore p L T)
    ∃ K : Subgroup G, K ∈ cComponentsIn N ∧ Y ≤ K ∧
      (∀ D : Subgroup G, D ∈ cComponentsIn N → Y ≤ D → D = K) ∧
      (K.subgroupOf N).Normal ∧ (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      A312Embedding ((Y.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)))
        ((K.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) ∧
      ¬ ((XiP p L).subgroupOf K).Normal ∧
      ¬ XiP p L ≤ (solvableRadical K).map K.subtype ∧ Y < K := by
  obtain ⟨K, hK, hYK, hu, hn, hTK, he⟩ :=
    exists_normal_component hG hA312 hA38 p L T hL.1 hTL hY C hC
  exact ⟨K, hK, hYK, hu, hn, hTK, he,
    escaping_component_rigidity hG hA36 hp3 L T hX hq C hC K hK hn hTK
      hXY hYK hM hescape⟩

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding
