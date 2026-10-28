module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields.Linear.Fields
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.NaturalRows
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Linear markings on the original chief action

The binary linear-three row contradicts the original nontrivial two-residual
in condition (ii). For the natural linear rows, compatible faithful-image
maps pull component membership back to K*V*. Sylow restriction to the
original subnormal K* retains centrality of the actual marked generator.
Applying the existing chief-section theorem then excludes the natural
four- and five-dimensional binary rows on the original module quotient.

Faithful-image maps and their two compatibility identities remain explicit
producer inputs. Innerness and the Sylow marking are proved here.
Source: Aschbacher–Smith, 13.5.21, printed pp.923–924.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields
open Configuration ChapterB.QuasisimpleSource
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]

/-- The literal B.4.2 linear-three action is excluded after field reduction
by applying the existing residual obstruction to the original Y and V̂. -/
theorem source_not_linearThree_action
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY)
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) (F : BinaryField) :
    ¬ Nonempty (ActionEquiv (ρ.comp L.subtype) (linearNatural F 3)) := by
  rintro ⟨action⟩
  obtain ⟨_, ⟨m⟩, ⟨binary⟩⟩ := source_binary_linearThree s h Y hY c ρ L comparison F action
  let e := chiefLinearQuotientEquiv s h L comparison binary.groupEquiv
  have hc : L1hat s h ≤ centralizer (Vhat s h : Set (Xhat s h)) :=
    c.condition_ii_O23.trans (map_subtype_le _)
  exact LocalModels.source_not_linearThree_of_condition_ii s h Y hY c.proved_prefix.Y_ne_bot
    c.proved_prefix.khat_fitting.symm c.proved_prefix.actor_card m.generator m.generates hc ⟨e⟩

/-- A marking in the original component of K*V*, ready for the chief-section
natural-action calculation. -/
structure OriginalComponentMarking where
  generator : component D K
  generates : zpowers ((generator : actor D K) : Hstar D.H) = starImage D.H D.V
  order : orderOf generator = 2
  sylow : Sylow 2 (component D K)
  central : ∀ x ∈ sylow, x * generator = generator * x

/-- Compatible faithful-image maps pull the marked subgroup into the original
component. Sylow centrality comes from the original V* and T*, not from an
assumed marking on an abstract model. -/
theorem ComponentMarking.original (m : ComponentMarking s h)
    (hcard : Nat.card (starImage D.H D.V) = 2)
    (q : actor D K →* Xhat s h) (hq : Function.Injective q)
    (hK : (component D K).map q = Khat s h)
    (hV : ((starImage D.H D.V).subgroupOf (actor D K)).map q = Vhat s h) :
    Nonempty (OriginalComponentMarking (D := D) (K := K)) := by
  have hVK : starImage D.H D.V ≤ starImage D.H K := by
    intro v hv
    let a : actor D K := ⟨v, (show starImage D.H D.V ≤ actor D K from le_sup_right) hv⟩
    have ha : q a ∈ Vhat s h := hV ▸ mem_map_of_mem q hv
    have hm : Vhat s h ≤ Khat s h := by
      rw [← m.generates]
      exact zpowers_le.mpr m.generator.property
    have hqK : q a ∈ (component D K).map q := hK.symm ▸ hm ha
    obtain ⟨b, hb, he⟩ := hqK
    have he' : b = a := hq he
    have haK : a ∈ component D K := he' ▸ hb
    exact haK
  have hcyc : IsCyclic (starImage D.H D.V) := isCyclic_of_prime_card hcard
  obtain ⟨v, hv⟩ := (starImage D.H D.V).isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have hvV : v ∈ starImage D.H D.V := hv ▸ mem_zpowers v
  let vK : starImage D.H K := ⟨v, hVK hvV⟩
  let e : component D K ≃* starImage D.H K := subgroupOfEquivOfLe le_sup_left
  let w := e.symm vK
  obtain ⟨P, hP⟩ := (starSylow D h).exists_subgroupOf_eq_of_subnormal
    (starImage D.H K) s.star_component.1
  let Q := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hc : ∀ x ∈ Q, x * w = w * x := by
    rintro x ⟨y, hy, rfl⟩
    apply e.injective
    simp only [map_mul, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    change y * vK = vK * y
    apply Subtype.ext
    apply mem_centralizer_iff.mp (star_actor_centralizes_sylow D h hcard hvV)
    change y ∈ (P : Subgroup (starImage D.H K)) at hy
    rwa [hP] at hy
  have ho : orderOf v = 2 := by rw [← Nat.card_zpowers, hv, hcard]
  have how : orderOf w = 2 := (e.orderOf_eq w).symm.trans
    ((orderOf_injective (starImage D.H K).subtype Subtype.coe_injective vK).symm.trans ho)
  exact ⟨⟨w, hv, how, Q, hc⟩⟩

variable [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- Source application to the literal chief section: the B.4.2 binary-linear
row supplies the model, and the compatible faithful-image maps supply its
comparison with X̂. No component membership or Sylow marking is assumed. -/
theorem source_noncentral_section_not_binaryLinear
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY)
    (hcard : Nat.card (starImage D.H D.V) = 2)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K)))
    (q : actor D K →* Xhat s h) (hq : Function.Injective q)
    (hK : (component D K).map q = Khat s h)
    (hV : ((starImage D.H D.V).subgroupOf (actor D K)).map q = Vhat s h)
    (comparison : Khat s h ≃* ((component D K) ⧸ center (component D K)))
    (hLK : D.L₁ ≤ K)
    (plane : D.L₁ ≤ K → ∀ v : actor D K,
      zpowers (v : Hstar D.H) = starImage D.H D.V →
        Representation.BinaryOffender.MovedPlane (representation D K h) (localActor D K) v)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    {d : ℕ} (hd : d = 4 ∨ d = 5) :
    ¬ Nonempty (ActionEquiv
      ((chiefRepresentation D K h U N).comp (component D K).subtype)
      (linearNatural BinaryField.two d)) := by
  rintro ⟨action⟩
  let e := chiefLinearQuotientEquiv s h (component D K) comparison action.groupEquiv
  obtain ⟨m⟩ := source_binaryHigher_marking s h Y c.proved_prefix hd e
  obtain ⟨original⟩ := m.original s h hcard q hq hK hV
  exact LocalModels.noncentral_section_not_binaryNatural D K h s hcard heven
    original.generator original.generates original.sylow original.central hLK
    (fun hl => plane hl original.generator original.generates) U N hn hd ⟨action⟩

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields
