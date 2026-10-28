module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisFullAction
public import Theory.Representation.G2BinaryPointQuotient

/-!
# The original Rudvalis point centralizer and its dihedral quotient

The full natural action maps the literal point centralizer onto the binary
G₂ point parabolic. The kernel is exactly the original E₆₄ image. Pulling
back the marked C₄² radical gives a normal subgroup of order 1024, with
quotient D₁₂. The final theorem supplies these maps in the actual escaping
odd-actor component with its original module, relative Sylow and quotient.

The ambient involution-centralizer two-core intersection is the kernel of
a separate quotient map. This parabolic quotient kills the whole E₆₄,
whereas the source ambient quotient must retain a module involution.
Constructing that image, the quaternion fixed subgroup, and its intersection
of order four still requires source geometry. Those obligations, the J₄ exclusion
and terminal odd-normalizer control remain with qt-d-13316-source. The
earlier Structural1222 input retains final discharge with qt-theorem-d.
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

/-- The literal source point centralizer maps onto the native point
parabolic, with E₆₄ kernel, and onto D₁₂ with kernel of order 1024. -/
theorem unitary_original_pushingUp_rudvalis_point_parabolic (s : Context T L V)
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
    let U := (W.subgroupOf H).subgroupOf K
    let E := U.map f
    let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
    ∀ z : E, z ≠ 1 →
      let P := (centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf C
      ∃ b : P →* Atlas.G2.BinaryCore.secondParabolic,
        Function.Surjective b ∧ b.ker = (E.subgroupOf C).subgroupOf P ∧
        let r := Atlas.G2.BinaryParabolicPair.FullSquare.quotientEquiv.toMonoidHom.comp
          (Atlas.G2.BinaryParabolicPair.FullSquare.project.comp b)
        Function.Surjective r ∧ Nat.card r.ker = 1024 ∧
          r.ker = Atlas.G2.BinaryParabolicPair.FullSquare.radical.comap b := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let U := (W.subgroupOf H).subgroupOf K
  let E := U.map f
  let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
  obtain ⟨hCE,a,d,ha,hker,_,he⟩ :=
    unitary_original_pushingUp_rudvalis_full_action s hcover hJH hc K hK e c hVW
  dsimp only
  intro z hz
  let P := (centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf C
  have hv : s.coordinates (Additive.ofMul (d z)) ≠ 0 := by
    intro hh
    apply hz
    apply d.injective
    apply Additive.ofMul.injective
    apply s.coordinates.injective
    change s.coordinates (Additive.ofMul (d z)) = s.coordinates (Additive.ofMul (d 1))
    rw [map_one]
    change s.coordinates (Additive.ofMul (d z)) = s.coordinates 0
    rw [map_zero]
    exact hh
  have hP (x : C) : x ∈ P ↔ Atlas.G2.Natural.action (ZMod 2) (a x)
      (s.coordinates (Additive.ofMul (d z))) = s.coordinates (Additive.ofMul (d z)) := by
    rw [←he x z,s.coordinates.injective.eq_iff,Additive.ofMul.injective.eq_iff,d.injective.eq_iff]
    change (x : Rudvalis.Model) ∈ centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model) ↔ _
    rw [mem_centralizer_singleton_iff]
    rw [Subtype.ext_iff]
    change (x : Rudvalis.Model)*(z : Rudvalis.Model) = (z : Rudvalis.Model)*(x : Rudvalis.Model) ↔
      (x : Rudvalis.Model)*(z : Rudvalis.Model)*(x : Rudvalis.Model)⁻¹ = (z : Rudvalis.Model)
    rw [mul_inv_eq_iff_eq_mul]
  have hcard : Nat.card P = 12288 :=
    (unitary_original_pushingUp_rudvalis_exact_sizes s hcover hJH hc K hK e c hVW).2.2 z hz
  obtain ⟨g,b,hb,hbk,_,hr,hR,hpre⟩ :=
    Atlas.G2.Natural.BinaryPointFlag.exists_point_dihedral_quotient a ha P
      (s.coordinates (Additive.ofMul (d z))) hv hP hcard
  exact ⟨b,hb,hbk.trans (congrArg (fun X : Subgroup C => X.subgroupOf P) hker),hr,hR,hpre⟩

/-- The same point-parabolic and dihedral quotients in the actual escaping
odd-actor component, retaining the original relative Sylow placement. -/
theorem unitary_original_oddActorResidual_point_parabolic (s : Context T L V)
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
            let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
            ∀ z : E, z ≠ 1 →
              let P := (centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf C
              ∃ b : P →* Atlas.G2.BinaryCore.secondParabolic,
                Function.Surjective b ∧ b.ker = (E.subgroupOf C).subgroupOf P ∧
                let r := Atlas.G2.BinaryParabolicPair.FullSquare.quotientEquiv.toMonoidHom.comp
                  (Atlas.G2.BinaryParabolicPair.FullSquare.project.comp b)
                Function.Surjective r ∧ Nat.card r.ker = 1024 ∧
                  r.ker = Atlas.G2.BinaryParabolicPair.FullSquare.radical.comap b) := by
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
      unitary_original_pushingUp_rudvalis_point_parabolic s hcover hJH hc K hK e c hcV⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
