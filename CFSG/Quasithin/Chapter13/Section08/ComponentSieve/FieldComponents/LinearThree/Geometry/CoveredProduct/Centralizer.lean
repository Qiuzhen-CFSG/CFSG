module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.SourceActions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.Decomposition
public import Theory.GroupTheory.InvertedCubicTwoExtension.Marked
public import Theory.GroupTheory.PGroup.CharacteristicKernel
public import Theory.GroupTheory.PCoreSurjective

/-!
# The marked S₃ centralizer of the covered component

Let Q = H/O₂(H), K* be the actual binary linear-three component, and
X* the image of the source residual L₁,+. The derived source geometry
makes X* a normal cubic subgroup centralizing K*. Multiplication identifies
K* × C_Q(K*) with Q, so projection sends the source generation H = KL₁T
and L₁ = XL₀, with L₀ ≤ K, to a two-group supplement of X* in C_Q(K*).
Thus C_Q(K*)/X* is a two-group. Relative component normality makes its
centralizer normal in Q, and O₂(Q) = 1 forces that centralizer's two-core
to be trivial.

Cubic-extension recognition now gives an actual S₃ equivalence. It is
chosen to map X* to A₃ and the corrected source inverter to (1 2).
All three groups, the relative normality, the source Sylow subgroup and
the retained inverter are the actual source objects. This conditional
prerequisite consumes the geometry already constructed by
`source_component_geometry`; it assumes no centralizer order or equivalence.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), covered paragraph, printed p.957.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
open ResidualPlacement
variable {G : Type*} [Group G]

/-- The corrected source inverter lies in the actual component centralizer. -/
theorem source_inverter_mem_centralizer (H K L T V₁ V₃ : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (geo : SourceComponentGeometry H K L T V₁ V₃ eK) :
    QuotientGroup.mk' (pCore 2 H) ⟨geo.inverter.val, geo.inverter_mem⟩ ∈
      centralizer (Source.starImage H K : Set (Source.Hstar H)) := by
  intro x hx
  exact (mul_inv_eq_iff_eq_mul.mp (geo.inverter_component_action ⟨x,hx⟩)).symm

/-- Relative component normality and O₂(H/O₂(H)) = 1 give a two-reduced
actual component centralizer. No order or recognition hypothesis is used. -/
theorem source_centralizer_twoCore [Finite G] (H K : Subgroup G)
    [(K.subgroupOf H).Normal] :
    pCore 2 (centralizer (Source.starImage H K : Set (Source.Hstar H))) = ⊥ := by
  let : (Source.starImage H K).Normal := (inferInstance : (K.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  let C := centralizer (Source.starImage H K : Set (Source.Hstar H))
  have hQ : pCore 2 (Source.Hstar H) = ⊥ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    have he := congrArg (map q)
      (q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk)
    rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at he
    exact he.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))
  have hle : (pCore 2 C).map C.subtype ≤ pCore 2 (Source.Hstar H) :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map C.subtype⟩
  apply bot_unique
  intro c hc
  apply Subtype.ext
  exact mem_bot.mp (hQ ▸ hle (mem_map.mpr ⟨c,hc,rfl⟩))

/-- Identify the actual centralizer with S₃, marking both the source cubic
subgroup and the exact corrected inverter supplied by the derived geometry. -/
theorem source_centralizer_equiv [Finite G] (H K L T V₁ V₃ : Subgroup G)
    [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (one L T V₁ ⊔ T))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (geo : SourceComponentGeometry H K L T V₁ V₃ eK) :
    let C := centralizer (Source.starImage H K : Set (Source.Hstar H))
    let s := QuotientGroup.mk' (pCore 2 H) ⟨geo.inverter.val,geo.inverter_mem⟩
    ∃ (hs : s ∈ C) (eC : C ≃* Equiv.Perm (Fin 3)),
      ((Source.starImage H (plus L T V₁)).subgroupOf C).map eC.toMonoidHom =
        alternatingGroup (Fin 3) ∧
      eC ⟨s,hs⟩ = Equiv.swap (1 : Fin 3) 2 := by
  let Ks := Source.starImage H K
  let Xs := Source.starImage H (plus L T V₁)
  let C := centralizer (Ks : Set (Source.Hstar H))
  let X := Xs.subgroupOf C
  let : Xs.Normal := geo.plus_normal
  have hXC : Xs ≤ C := le_centralizer_iff.mp geo.plus_centralized
  let E := componentCentralizerEquiv H K eK geo.inner_action
  let π : Source.Hstar H →* C := (MonoidHom.snd Ks C).comp E.symm.toMonoidHom
  have hπK (k : Ks) : π k.val = 1 := by
    have hk : E (k,1) = k.val := by change k.val * 1 = k.val; exact mul_one _
    rw [← hk]
    change (E.symm (E (k,1))).2 = 1
    rw [E.symm_apply_apply]
  have hπC (c : C) : π c.val = c := by
    have hc : E (1,c) = c.val := by change 1 * c.val = c.val; exact one_mul _
    rw [← hc]
    change (E.symm (E (1,c))).2 = c
    rw [E.symm_apply_apply]
  have hπsurj : Function.Surjective π := fun c => ⟨c.val,hπC c⟩
  have hπKs : Ks.map π = ⊥ := (Subgroup.map_eq_bot_iff Ks).mpr (fun k hk => hπK ⟨k,hk⟩)
  have hπXs : Xs.map π = X := by
    ext c
    constructor
    · rintro ⟨x,hx,rfl⟩
      change (π x).val ∈ Xs
      rw [hπC ⟨x,hXC hx⟩]
      exact hx
    · intro hc
      exact ⟨c.val,hc,hπC c⟩
  have hKH : K ≤ H := by rw [hgen]; exact le_sup_left
  have hDH : one L T V₁ ≤ H := by rw [hgen]; exact le_sup_left.trans le_sup_right
  have hTH : T ≤ H := by rw [hgen]; exact le_sup_right.trans le_sup_right
  have hXH : plus L T V₁ ≤ H :=
    (show plus L T V₁ ≤ one L T V₁ by rw [hfactor]; exact le_sup_left).trans hDH
  have hstarGen : Ks ⊔ (Xs ⊔ Source.starImage H T) = ⊤ := by
    have hH : H = K ⊔ (plus L T V₁ ⊔ T) := by
      rw [hgen, hfactor]
      apply le_antisymm
      · exact sup_le le_sup_left (sup_le
          (sup_le (le_sup_left.trans le_sup_right) (geo.zero_le.trans le_sup_left))
          (le_sup_right.trans le_sup_right))
      · exact sup_le le_sup_left (sup_le
          ((le_sup_left.trans le_sup_left).trans le_sup_right)
          (le_sup_right.trans le_sup_right))
    have he : Source.starImage H H = ⊤ := by
      simp [Source.starImage, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [← he]
    conv_rhs => arg 2; rw [hH]
    rw [star_sup H _ _ hKH (sup_le hXH hTH), star_sup H _ _ hXH hTH]
  have hsup : (Source.starImage H T).map π ⊔ X = ⊤ := by
    have he := congrArg (map π) hstarGen
    simpa only [Subgroup.map_sup, hπKs, hπXs, bot_sup_eq, map_top_of_surjective _ hπsurj,
      sup_comm] using he
  have hT : IsPGroup 2 T := hS ▸ S.isPGroup'.map H.subtype
  have hTs : IsPGroup 2 (Source.starImage H T) := hT.comap_subtype.map _
  have hquot : IsPGroup 2 (C ⧸ X) :=
    quotient_isPGroup_of_sup_eq_top _ X (hTs.map π) hsup
  have hcard : Nat.card X = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hXC).toEquiv).trans geo.plus_card
  let s : Source.Hstar H := QuotientGroup.mk' (pCore 2 H) ⟨geo.inverter.val,geo.inverter_mem⟩
  have hs : s ∈ C := source_inverter_mem_centralizer H K L T V₁ V₃ eK geo
  have hinv : ∀ x ∈ X, (⟨s,hs⟩ : C) * x * (⟨s,hs⟩ : C)⁻¹ = x⁻¹ := by
    intro x hx
    apply Subtype.ext
    exact geo.inverter_plus_action x.val hx
  refine ⟨hs, ?_⟩
  exact InvertedCubicTwoExtension.exists_equiv_preserving_cubic_and_inverter X hcard hquot
    (source_centralizer_twoCore H K) ⟨s,hs⟩ hinv
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
