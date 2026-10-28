module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.Sections
public import Theory.Representation.BinarySylowTransvection

/-!
# The binary natural linear rows of 13.5.21

The action equivalence in a B.4.2 binary-linear row transports the marked
Sylow-central element to a transvection. We retain both the vector/form
description on the original module and its displacement rank. On the literal
chief section of U_H/V₁ this contradicts the irreducible moved plane.

The component membership and Sylow marking are inputs from the independent
group sieve. The marked-plane producer takes the source containment L₁ ≤ K
explicitly; this module does not establish that containment or assume a
filtered classification list.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.5.21,
printed p.924 (PDF p.941), the paragraph excluding the natural linear rows.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels

variable {E W : Type*} [Group E] [Finite E] [AddCommGroup W] [Module (ZMod 2) W]

/-- A row's intertwiner preserves the marked transvection on the original
space, not only its abstract group class. -/
theorem binaryNatural_transvection (ρ : Representation (ZMod 2) E W)
    {n : ℕ} (hn : 1 < n) (e : ActionEquiv ρ (linearNatural BinaryField.two n))
    (T : Sylow 2 E) (v : E) (hv : v ≠ 1)
    (hc : ∀ x, x ∈ T → x * v = v * x) :
    (∃ w : W, ∃ f : W →ₗ[ZMod 2] ZMod 2,
      w ≠ 0 ∧ f ≠ 0 ∧ f w = 0 ∧ ∀ x, ρ v x = x + f x • w) ∧
      Module.finrank (ZMod 2) (LinearMap.range (ρ v - 1)) = 1 := by
  change ActionEquiv ρ (specialLinearNatural (k := ZMod 2) n) at e
  let P := T.mapSurjective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.surjective
  have ht := specialLinear_isTransvection_of_central_sylow hn P (e.groupEquiv v)
    (fun h => hv (e.groupEquiv.injective (h.trans e.groupEquiv.map_one.symm)))
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      change e.groupEquiv y * e.groupEquiv v = e.groupEquiv v * e.groupEquiv y
      simpa only [map_mul] using congrArg e.groupEquiv (hc y hy))
  have hr := ht.displacement_rank
  constructor
  · obtain ⟨w, f, hw, hf, hfw, ht⟩ := ht
    refine ⟨e.linearEquiv.symm w, f.comp e.linearEquiv.toLinearMap, ?_, ?_, ?_, ?_⟩
    · exact fun hh => hw (e.linearEquiv.symm.injective (hh.trans (map_zero _).symm))
    · intro hh
      apply hf
      apply LinearMap.ext
      intro x
      have he := LinearMap.congr_fun hh (e.linearEquiv.symm x)
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, LinearMap.zero_apply] using he
    · simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using hfw
    · intro x
      apply e.linearEquiv.injective
      rw [e.intertwines, map_add, map_smul, e.linearEquiv.apply_symm_apply]
      change slEquivLinear n (e.groupEquiv v) (e.linearEquiv x) =
        e.linearEquiv x + f (e.linearEquiv x) • w
      rw [ht]
      rfl
  · have he := RankTwo.finrank_movedSpace_transport ρ (specialLinearNatural (k := ZMod 2) n)
      e.groupEquiv e.linearEquiv e.intertwines v
    exact he.trans hr

variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (K : Subgroup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
open Section08.Source

/-- The natural SL₄/SL₅ row on the actual component action is impossible on
any noncentral source section. The supplied plane is instantiated with the
original containment L₁ ≤ K. All actor and quotient maps are literal. -/
theorem noncentral_section_not_binaryNatural (s : Selected D K)
    (hcard : Nat.card (starImage D.H D.V) = 2)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K)))
    (v : component D K)
    (hv : zpowers ((v : actor D K) : Hstar D.H) = starImage D.H D.V)
    (T : Sylow 2 (component D K))
    (hc : ∀ x, x ∈ T → x * v = v * x)
    (hLK : D.L₁ ≤ K)
    (plane : D.L₁ ≤ K → MovedPlane (representation D K h) (localActor D K) (v : actor D K))
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    {n : ℕ} (hd : n = 4 ∨ n = 5) :
    ¬ Nonempty (ActionEquiv
      ((chiefRepresentation D K h U N).comp (component D K).subtype)
      (linearNatural BinaryField.two n)) := by
  rintro ⟨e⟩
  have hm := noncentral_section_moved D K h s hcard heven (v : actor D K) hv U N hn
  have hv1 : v ≠ 1 := by
    intro he
    obtain ⟨w, hw⟩ := hm
    exact hw (by simp only [he, OneMemClass.coe_one, map_one, Module.End.one_apply])
  have hr := (binaryNatural_transvection _ (by rcases hd with rfl | rfl <;> decide)
    e T v hv1 hc).2
  have hp := (plane hLK).section_rank U N hm
  change Module.finrank (ZMod 2)
    (LinearMap.range (chiefRepresentation D K h U N (v : actor D K) - 1)) = 1 at hr
  exact (by decide : (2 : ℕ) ≠ 1) (hp.symm.trans hr)

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels
