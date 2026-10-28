module
public import Theory.SpecificGroups.Rudvalis.Model.PointCoreBound
public import Theory.Representation.G2BinaryPointSmallImage
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisAmbientPoint
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisFullAction

/-!
# The original module meets the ambient Rudvalis point core in a hyperplane

Restrict the literal S₅ quotient of the point centralizer to the original
E₆₄ image. The full natural point-parabolic action preserves its kernel.
The invariant-subspace argument gives kernel order 32 or 64. The native
point-core certificate excludes the latter, so the intersection is exactly
an E₃₂, with the original inclusion and central quotient marking retained.

The final theorem applies this to the actual escaping odd-actor component,
including its original relative Sylow placement and whole module. Selection
of the order-twelve point-stabilizer image, the flag/quaternion intersection,
J₄ exclusion and final odd-normalizer control remain with qt-d-13316-source.
Structural1222 retains its final discharge with qt-theorem-d.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open Atlas.G2.Natural.BinaryNormalizer
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The literal ambient two-core cuts the original E₆₄ module in a subgroup of order 32. -/
theorem unitary_original_pushingUp_rudvalis_module_core_intersection (s : Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let E := ((W.subgroupOf H).subgroupOf K).map f
    ∀ z : E, z ≠ 1 →
      let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
      Nat.card (E ⊓ D.pCoreIn 2 : Subgroup Rudvalis.Model) = 32 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let E := ((W.subgroupOf H).subgroupOf K).map f
  let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
  obtain ⟨hCE,a,d,ha,hker,_,he⟩ :=
    unitary_original_pushingUp_rudvalis_full_action s hcover hJH hc K hK e c hVW
  let hEelem : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective d.symm.toMonoidHom d.symm.surjective
  let : IsMulCommutative E := hEelem.toIsMulCommutative
  let : Module (ZMod 2) (Additive E) := IsElementaryAbelian.isVectorSpace 2
  let ed : Additive E ≃ₗ[ZMod 2] Additive V :=
    { d.toAdditive with map_smul' := ZMod.map_smul d.toAdditive }
  let θ := ed.trans s.coordinates
  let α : C →* MulAut E := E.normalizerMonoidHom.comp (inclusion hCE)
  dsimp only
  intro z hz
  let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
  let P := D.subgroupOf C
  have hED : E ≤ D := by
    intro u hu
    apply mem_centralizer_singleton_iff.mpr
    exact setLike_mul_comm hu z.property
  let j : E →* D := inclusion hED
  obtain ⟨q,_,hqk,_,_,_⟩ :=
    unitary_original_pushingUp_rudvalis_ambient_point_quotient s hcover hJH hc K hK e c hVW z hz
  let k := q.comp j
  have hk : k.ker = (D.pCoreIn 2).subgroupOf E := by
    ext u
    change q (j u) = 1 ↔ (u : Rudvalis.Model) ∈ D.pCoreIn 2
    change j u ∈ q.ker ↔ _
    rw [hqk]
    constructor
    · intro hu
      exact ⟨j u,hu,rfl⟩
    · rintro ⟨v,hv,heq⟩
      exact (show v = j u from Subtype.ext heq) ▸ hv
  have hmap : k.ker.map E.subtype = E ⊓ D.pCoreIn 2 := by
    rw [hk,subgroupOf_map_subtype,inf_comm]
  have hv : θ (Additive.ofMul z) ≠ 0 := by
    intro hh
    apply hz
    apply Additive.ofMul.injective
    apply θ.injective
    change θ (Additive.ofMul z) = θ 0
    rw [map_zero]
    exact hh
  have hP (x : C) : x ∈ P ↔ Atlas.G2.Natural.action (ZMod 2) (a x)
      (θ (Additive.ofMul z)) = θ (Additive.ofMul z) := by
    change x ∈ P ↔ Atlas.G2.Natural.action (ZMod 2) (a x)
      (s.coordinates (Additive.ofMul (d z))) = s.coordinates (Additive.ofMul (d z))
    rw [←he x z,s.coordinates.injective.eq_iff,Additive.ofMul.injective.eq_iff,d.injective.eq_iff]
    change (x : Rudvalis.Model) ∈ centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model) ↔ _
    rw [mem_centralizer_singleton_iff]
    rw [Subtype.ext_iff]
    change (x : Rudvalis.Model)*(z : Rudvalis.Model) = (z : Rudvalis.Model)*(x : Rudvalis.Model) ↔
      (x : Rudvalis.Model)*(z : Rudvalis.Model)*(x : Rudvalis.Model)⁻¹ = (z : Rudvalis.Model)
    rw [mul_inv_eq_iff_eq_mul]
  have hkn (x : P) (u : E) (hu : u ∈ k.ker) : α x u ∈ k.ker := by
    let xd : D := ⟨x.val.val,x.property⟩
    have hj : j (α x u) = xd * j u * xd⁻¹ := rfl
    change q (j (α x u)) = 1
    rw [hj,map_mul,map_mul,map_inv]
    have hku : q (j u) = 1 := hu
    rw [hku,mul_one,mul_inv_cancel]
  obtain ⟨hsize,_⟩ := Atlas.G2.Natural.BinaryPointFlag.fivePoint_image_card_le_two_of_point_action
    a ha P (θ (Additive.ofMul z)) hv hP α θ he k hkn
  have hcard : Nat.card (E ⊓ D.pCoreIn 2 : Subgroup Rudvalis.Model) = Nat.card k.ker := by
    rw [←hmap,card_map_of_injective E.subtype_injective]
  rcases hsize with hs | hs
  · exact hcard.trans hs
  · exfalso
    have hE : Nat.card E = 64 := by
      rw [Nat.card_congr d.toEquiv]
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
      rw [Nat.card_zmod,s.coordinates.finrank_eq,Atlas.G2.Natural.finrank_space] at hh
      exact hh
    have hi : E ⊓ D.pCoreIn 2 = E := eq_of_le_of_card_ge inf_le_left (by rw [hcard,hs,hE])
    have hclass : IsConj (z : Rudvalis.Model) (Rudvalis.b ^ 2) :=
      ((unitary_original_pushingUp_rudvalis_module_and_points
        s hcover hJH hc K hK e c hVW).2.2 z hz).2.1
    exact Rudvalis.PointCoreBound.elementary_not_le_point_core z hclass E hE (inf_eq_left.mp hi)

/-- The literal original odd-actor application, retaining the relative Sylow placement. -/
theorem unitary_original_oddActorResidual_module_core_intersection (s : Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
      (c : sectionCentralizerIn (normalizer (L : Set G)) L),
      PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ normalizer (L : Set G) < H ∧
      let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let W := fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (L : Set G))
        Y (J.pCoreIn 2) W ∧
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
        (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
      V.map (MulAut.conj (c : G)).toMonoidHom ≤ W ∧
      ∃ K : Subgroup H, IsComponent H K ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
          ∃ e : K ⧸ center K ≃* Rudvalis.Model,
            W = V.map (MulAut.conj (c : G)).toMonoidHom ∧
            let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
            let E := ((W.subgroupOf H).subgroupOf K).map f
            ∀ z : E, z ≠ 1 →
              let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
              Nat.card (E ⊓ D.pCoreIn 2 : Subgroup Rudvalis.Model) = 32) := by
  obtain ⟨J,H,S,hpush,hH,hJH,hlt,hc,_,_,⟨K,hK,hout,n,hn,⟨e⟩⟩,c,hcS,hcV⟩ :=
    unitary_original_oddActorResidual_escaping_component s A hAN hcomm hodd hAV hnot
  refine ⟨J,H,S,c,hpush,hH,hJH,hlt,hc,hcS,hcV,K,hK,hout,?_⟩
  rcases hn with rfl | rfl
  · exact Or.inl ⟨e⟩
  · apply Or.inr
    have hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G) := by
      have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
      obtain ⟨hcover,_,_,_⟩ := chosen_oddActorResidual_cover h12.toHypothesis1221 s.chosen
        A hAN hcomm hodd hAV
      have hi : oddActorResidual L A ≤ J :=
        ((le_inf le_rfl ((oddActorResidual_le L A).trans inf_le_left)).trans hpush.2).trans
          inf_le_left
      exact hcover.subset.trans (Set.mul_subset_mul hi Set.Subset.rfl)
    exact ⟨e,unitary_original_pushingUp_rudvalis_full_module s hcover hJH hc K hK e c hcV,
      unitary_original_pushingUp_rudvalis_module_core_intersection s hcover hJH hc K hK e c hcV⟩


end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
