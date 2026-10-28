module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.Marking.Nonzero
public import Theory.Representation.FirstCohomologyDuality.SimpleCover

/-!
# The core centralizer vanishes in the natural projection

The earlier faithful plus-kernel equality makes C_UH(Q_H)/V₁ a proper
invariant subspace of the original cover. Natural transitivity makes its
image either zero or the whole quotient. In the latter case commutator
generation forces the subspace to be the whole cover, a contradiction.
Source: Aschbacher–Smith 13.7.4(1), 13.8.27, printed pp.936,963.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open Representation.OneCohomology
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open AlternatingAndLinear.FourStructure.CriticalTransfer CriticalGeometry Atlas.G2

variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {L T H V V₃ V₁ K : Subgroup G}
  {ρ : Representation (ZMod 2) (Source.Hstar H) W}

omit [Finite G] [FiniteDimensional (ZMod 2) W] in
/-- The literal core centralizer has zero image under the original projection. -/
theorem source_core_centralizer_projection_eq_bot
    (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (e : Source.starImage H K ≃* commutator (Model (ZMod 2)))
    (f : Source.Hstar H →* Model (ZMod 2))
    (p : W →ₗ[ZMod 2] Natural.Space (ZMod 2)) (hp : Function.Surjective p)
    (he : ∀ a v, p (ρ a v) = Natural.action (ZMod 2) (f a) (p v))
    (hfK : ∀ a : Source.starImage H K, f a = (e a : Model (ZMod 2)))
    (hk : p.ker ≤ fixedSpace ρ (Source.starImage H K))
    (hgen : Coinvariants.ker (ρ.comp (Source.starImage H K).subtype) = ⊤)
    (hpluskernel : commutatorPreimage H (Source.UH H V₃)
      (Source.UH H V₃ ⊓ centralizer (Source.QH H : Set G)) = Source.QH H)
    (hA : Source.starImage H (c.Ugamma V₃) ≠ ⊥) :
    (s.image (Source.UH H V₃ ⊓ centralizer (Source.QH H : Set G))).map p = ⊥ := by
  let U := Source.UH H V₃
  let U₀ := U ⊓ centralizer (Source.QH H : Set G)
  let S := s.image U₀
  have hNQ : H ≤ normalizer (Source.QH H : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : H ≤ normalizer (U₀ : Set G) :=
    (le_inf s.normalizes (hNQ.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hZI : V₁ ≤ U₀ := le_inf s.line_le
    ((le_centralizer_iff.mp s.centralizes).trans (centralizer_le (pCoreIn_le 2 H)))
  have hproper : S ≠ ⊤ := by
    intro ht
    have hU₀ : U₀ = U := le_antisymm inf_le_left (by
      intro u hu
      apply (s.quotient_mem_image_iff U₀ hZI ⟨u,hu⟩).mp
      change (s.quotient ⟨u,hu⟩).toAdd ∈ S
      rw [ht]
      exact Submodule.mem_top)
    have hHQ : H ≤ Source.QH H := by
      rw [← hpluskernel]
      apply le_commutatorPreimage le_rfl
      change ⁅H, U⁆ ≤ U₀
      rw [hU₀]
      exact le_normalizer_iff_commutator_le_right.mp s.normalizes
    apply hA
    apply bot_unique
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨b,hb,heq⟩ := hHQ a.property
    have hab : b = a := Subtype.ext heq
    subst b
    exact (QuotientGroup.eq_one_iff a).mpr hb
  let α : Representation (ZMod 2) (commutator (Model (ZMod 2))) W :=
    (ρ.comp (Source.starImage H K).subtype).comp e.symm.toMonoidHom
  let P : Representation.IntertwiningMap α (Natural.derivedAction (ZMod 2)) :=
    p.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      change p (ρ (e.symm g) v) = Natural.action (ZMod 2) g (p v)
      rw [he,hfK,e.apply_symm_apply])
  have hP : IsCover P := ⟨hp, (fun _ hv g => hk hv (e.symm g)),
    (CentralCoverOriginalAction.commutator_comp_equiv _ e.symm).trans hgen⟩
  have hS (g : commutator (Model (ZMod 2))) (v : W) (hv : v ∈ S) : α g v ∈ S := by
    obtain ⟨k,hk',heq⟩ := (e.symm g).property
    obtain ⟨u,hu,rfl⟩ := hv
    change ρ (e.symm g) (s.quotient u).toAdd ∈ S
    rw [← heq, s.conjugates]
    exact ⟨_, (mem_normalizer_iff.mp (hN k.property) u).mp hu, rfl⟩
  have him (g : commutator (Model (ZMod 2))) (v : Natural.Space (ZMod 2))
      (hv : v ∈ S.map p) : Natural.derivedAction (ZMod 2) g v ∈ S.map p := by
    obtain ⟨w,hw,rfl⟩ := hv
    exact ⟨α g w,hS g w hw,LinearMap.congr_fun (P.isIntertwining' g) w⟩
  by_contra hn
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  have htop : S.map p = ⊤ := by
    apply top_unique
    intro w _
    by_cases hw : w = 0
    · subst w; exact Submodule.zero_mem _
    · obtain ⟨g,rfl⟩ := Natural.derivedAction_transitive (ZMod 2) v w hv0 hw
      exact him g v hv
  exact hproper (invariant_eq_top_of_cover_image_eq_top P hP S hS htop)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
