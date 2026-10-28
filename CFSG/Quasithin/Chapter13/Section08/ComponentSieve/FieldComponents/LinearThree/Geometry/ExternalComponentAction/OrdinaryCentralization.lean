module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.CoreImage
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.OrdinaryCentralization.LocalDeduction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.Defs

/-!
# Ordinary-A₆ external centralization

For X=L₁ with X=[X,T] and |X/O₂(X)|=3, the local calculation proves
X≤K or [X,K]≤O₂(K). It uses the source Sylow subgroup inside H, relative
normality of K, and the actual identification K*=PSL₃(2). `CoreImage`
identifies K* with K/O₂(K); mapping the intrinsic calculation back to G
keeps O₂(K) in its correct ambient carrier. Subnormal core monotonicity
then gives [L₁∩H,K∩H]≤O₂(H) internally.

The final conditional theorem retains the ordinary A₆ equivalence, the
literal marked parabolic and its residual, H=KL₁T, the source Hz and SQTK
conditions, relative C-component membership and normality, K≰M, and L₁≰K.
The rank-one and K* model inputs are explicit, for the separate rank owner.
The stronger intrinsic proof does not need all these standing hypotheses.

The order-three marked quotient is the earlier ordinary-case calculation
in the setup of 13.2.1, also used explicitly in the proof of 13.7.4(1)
on printed p.938. The full commutator X=[X,T] is the input recalled on
p.956. These remain explicit earlier inputs, not consequences of an
unmarked A₆ equivalence alone. Solvability follows here from the order-three
quotient, and T-normalization follows from the full commutator equality.
The earlier *group* seed equality [V₃,L₁]=V₃, used in the proof of 13.7.5(2)
on p.938, is retained with the source setup. It is not inferred merely
from irreducibility on V₃/V₁. The parent supplies its seed transport and
module generation and retains final source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), printed p.956. No specialized centralization, dichotomy,
or solvable generating overgroups are assumed.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.OrdinaryCentralization
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The source dichotomy, proved inside H with its actual Sylow subgroup.
The quotient-to-star comparison uses the intrinsic two-core kernel. -/
theorem commutator_dichotomy (H K X T : Subgroup G)
    [(K.subgroupOf H).Normal]
    (hKH : K ≤ H) (hXH : X ≤ H) (hT : Chapter1.IsSylowIn 2 T H)
    (hfull : ⁅X, T⁆ = X) (hcard : Nat.card (X ⧸ pCore 2 X) = 3)
    (e : Source.starImage H K ≃* Matrix.PSL3Two.PSL) :
    X ≤ K ∨ ⁅X, K⁆ ≤ (pCore 2 K).map K.subtype := by
  classical
  by_cases hout : X ≤ K
  · exact Or.inl hout
  right
  obtain ⟨S, hS⟩ := hT
  let N := K.subgroupOf H
  let Y := X.subgroupOf H
  let eN := subgroupOfEquivOfLe hKH
  let eX := subgroupOfEquivOfLe hXH
  have hn : N.IsSubnormal := (inferInstance : N.Normal).isSubnormal
  let eQ : (N ⧸ pCore 2 N) ≃* Matrix.PSL3Two.PSL :=
    (QuotientGroup.congr _ _ eN (pCore_map_iso 2 eN)).trans
      ((quotientStarEquiv H K hKH hn).trans e)
  have hfull' : ⁅Y, (S : Subgroup H)⁆ = Y := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hXH, hS, hfull]
  have hcard' : Nat.card (Y ⧸ pCore 2 Y) = 3 := by
    calc
      _ = Nat.card (X ⧸ pCore 2 X) := Nat.card_congr
        (QuotientGroup.congr _ _ eX (pCore_map_iso 2 eX)).toEquiv
      _ = 3 := hcard
  have hout' : ¬ Y ≤ N := by
    intro h
    apply hout
    intro x hx
    exact h (show (⟨x, hXH hx⟩ : H) ∈ Y from hx)
  have hc := commutator_le_core_of_outside N Y S hfull' hcard' hout' eQ
  have hcore : (N.pCoreIn 2).map H.subtype = (pCore 2 K).map K.subtype := by
    rw [pCoreIn, map_map, ← pCore_map_iso 2 eN, map_map]
    rfl
  have hm := map_mono (f := H.subtype) hc
  rw [map_commutator, map_subgroupOf_eq_of_le hXH,
    map_subgroupOf_eq_of_le hKH, hcore] at hm
  exact hm

/-- The ambient bound gives the internal bound required by the star action.
Only subnormality relative to H is used for the core comparison. -/
theorem internal_commutator_le_core (H K X : Subgroup G)
    (hKH : K ≤ H) (hXH : X ≤ H) (hKn : (K.subgroupOf H).IsSubnormal)
    (hc : ⁅X, K⁆ ≤ (pCore 2 K).map K.subtype) :
    ⁅X.subgroupOf H, K.subgroupOf H⁆ ≤ pCore 2 H := by
  have hcore := pCoreAmbient_mono_of_isSubnormalIn K H 2 hKH hKn
  have hm : (⁅X.subgroupOf H, K.subgroupOf H⁆).map H.subtype ≤
      (pCore 2 H).map H.subtype := by
    rw [map_commutator, map_subgroupOf_eq_of_le hXH, map_subgroupOf_eq_of_le hKH]
    exact hc.trans hcore
  exact (map_le_map_iff_of_injective H.subtype_injective).mp hm

/-- The earlier ordinary marked quotient of order three makes L₁ solvable. -/
theorem solvable_of_ordinary_marked_order (X : Subgroup G)
    (hcard : Nat.card (X ⧸ pCore 2 X) = 3) : Group.IsSolvable X := by
  let : IsCyclic (X ⧸ pCore 2 X) := isCyclic_of_prime_card hcard
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 X)).mpr ⟨inferInstance, inferInstance⟩

/-- The ordinary branch retains the source setup and the earlier marked
subgroup facts. The commutator bound, solvability and T-normalization are
proved; the earlier seed identity is retained as an input for the caller's
module argument. -/
theorem ordinary_external_centralization
    (κ : GroupClass.{u}) (H K L L₁ T G₁ M V₁ V₃ : Subgroup G)
    (_hQTKE : IsSimpleQTKE κ G)
    (hH : H ∈ Source.Hz L₁ T G₁ M) (_hSQTK : IsSQTK κ H)
    (hT : Chapter1.IsSylowIn 2 T H) (hgen : K ⊔ L₁ ⊔ T = H)
    (hK : (K.subgroupOf H).IsCComponent) (hKn : (K.subgroupOf H).Normal)
    (_hKM : ¬ K ≤ M) (hout : ¬ L₁ ≤ K)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (_hmarked : L₁ =
      (pResidual 2 ((L ⊔ T) ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
        ((L ⊔ T) ⊓ normalizer (V₁ : Set G) : Subgroup G).subtype)
    (_hflag : T ≤ normalizer (V₁ : Set G))
    (horder : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hfull : ⁅L₁, T⁆ = L₁) (_hseed : ⁅V₃, L₁⁆ = V₃)
    (_hrank : primeRank 3 K = 1)
    (eK : Source.starImage H K ≃* Matrix.PSL3Two.PSL) :
    ⁅L₁, K⁆ ≤ (pCore 2 K).map K.subtype ∧
      ⁅L₁.subgroupOf H, K.subgroupOf H⁆ ≤ pCore 2 H ∧
      Group.IsSolvable L₁ ∧ T ≤ normalizer (L₁ : Set G) := by
  let := hKn
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq hgen
  have hLH : L₁ ≤ H := le_sup_left.trans hH.1.2
  have hc := (commutator_dichotomy H K L₁ T hKH hLH hT hfull (horder ⟨eL⟩) eK).resolve_left hout
  exact ⟨hc, internal_commutator_le_core H K L₁ hKH hLH hK.subnormal hc,
    solvable_of_ordinary_marked_order L₁ (horder ⟨eL⟩),
    le_normalizer_iff_commutator_le_left.mpr hfull.le⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.OrdinaryCentralization
