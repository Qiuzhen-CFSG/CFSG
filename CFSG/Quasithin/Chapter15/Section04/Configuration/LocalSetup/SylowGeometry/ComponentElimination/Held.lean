module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.Earlier115
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.SpecificGroups.Held.LocalPairs.SylowPointwise
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry

/-!
# The ordinary Held branch of the contrary Sylow configuration

The central four-group acts faithfully on an ordinary component by the
commutator clause of the complete 1.1.5. Perfectness preserves faithfulness
on its central quotient. If that quotient is Held, the actual quotient Sylow
is fixed pointwise. The proved Held automorphism realization makes these
automorphisms inner, and the Held Sylow center has order two, contradicting
the order of the four-group.

The source application identifies the center with the two-core using the
actual odd-core elimination. It requires neither a multiplier calculation
nor a splitting assertion for the Held cover. This discharges the ordinary
branch of the additional Held alternative in the adequate intrinsic route;
the characteristic-two branch and intrinsic embedding remain separate.
Source: Aschbacher--Smith, 1.1.5 and the proof of 15.4.20, pp.501--503,
1163--1164, with Held retained in the intrinsic local reduction.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
open OrdinaryReduction
universe u

/-- Passing through the actual central quotient bounds a faithful two-group
of pointwise Sylow fixers on any perfect central Held cover. -/
theorem held_cover_action_card_le_two
    {L A : Type*} [Group L] [Finite L] [Group.IsPerfect L] [Group A]
    (e : L ⧸ center L ≃* Held.He) (P : Sylow 2 L)
    (α : A →* MulAut L) (hα : Function.Injective α) (hA : IsPGroup 2 A)
    (hfix : ∀ a : A, ∀ x ∈ (P : Subgroup L), α a x = x) : Nat.card A ≤ 2 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  let Q : Sylow 2 Held.He := P.mapSurjective (f := q)
    (e.surjective.comp (QuotientGroup.mk'_surjective (center L)))
  let β := (MulAut.centralQuotientAction e).comp α
  have hβ : Function.Injective β :=
    (MulAut.centralQuotientAction_injective e).comp hα
  have hf (a : A) (y : Held.He) (hy : y ∈ (Q : Subgroup Held.He)) : β a y = y := by
    obtain ⟨x, hx, rfl⟩ := hy
    change MulAut.centralQuotientAction e (α a)
      (e (QuotientGroup.mk' (center L) x)) = e (QuotientGroup.mk' (center L) x)
    rw [MulAut.centralQuotientAction_apply, hfix a x hx]
  have hi (a : A) : ∃ k : Held.He, MulAut.conj k = β a :=
    Held.LocalPairs.SylowPointwise.isInner_of_fixes_sylow
      Held.Realization.normalizer_surjective Q (β a) (hf a)
  have hb := faithful_inner_action_card_le_sylow_center Q Held.LocalPairs.center_eq_bot
    β hβ hA hi (fun a y => hf a y y.property)
  rwa [Held.LocalPairs.SylowGeometry.inner_center_card Q] at hb

variable {G : Type u} [Group G] [Finite G]

/-- The actual central four-group cannot act faithfully on a normal perfect
component with Held central quotient. All actions are ambient conjugation. -/
theorem no_held_component_central_four
    {H L U Z : Subgroup G} [Group.IsPerfect L]
    (hLH : L ≤ H) (hHL : H ≤ normalizer (L : Set G))
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U)
    (hZU : Z ≤ U) (hZC : Z ≤ centralizer (U : Set G))
    (hcard : Nat.card Z = 4) (hfaith : Z ⊓ centralizer (L : Set G) = ⊥)
    (e : L ⧸ center L ≃* Held.He) : False := by
  have hUH : U ≤ H := hP ▸ map_subtype_le (P : Subgroup H)
  let α : Z →* MulAut L := L.normalizerMonoidHom.comp
    (inclusion (hZU.trans (hUH.trans hHL)))
  have hinj : Function.Injective α := by
    apply (MonoidHom.ker_eq_bot_iff α).mp
    apply eq_bot_iff.mpr
    intro z hz
    have hfix (l : L) : (z : G) * (l : G) * (z : G)⁻¹ = (l : G) :=
      congrArg Subtype.val (DFunLike.congr_fun (MonoidHom.mem_ker.mp hz) l)
    have hc : (z : G) ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
      (mul_inv_eq_iff_eq_mul.mp (hfix ⟨l, hl⟩)).symm
    exact Subtype.ext (mem_bot.mp (hfaith ▸
      (show (z : G) ∈ Z ⊓ centralizer (L : Set G) from ⟨z.property, hc⟩)))
  obtain ⟨Q, hQ⟩ := sylow_intersection_image_of_relative_normal hLH hHL P hP
  have hf (z : Z) (q : L) (hq : q ∈ (Q : Subgroup L)) : α z q = q := by
    apply Subtype.ext
    have hqU : (q : G) ∈ U :=
      (hQ ▸ (show (q : G) ∈ (Q : Subgroup L).map L.subtype from ⟨q, hq, rfl⟩)).1
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp (hZC z.property) _ hqU).symm)
  have hpZ : IsPGroup 2 Z := (P.isPGroup'.map H.subtype).to_le (hP ▸ hZU)
  have hb := held_cover_action_card_le_two e Q α hinj hpZ hf
  omega

/-- Full 1.1.5 supplies faithfulness, and its first two clauses remove the
odd core. Thus a single retained Held C-component cannot be ordinary in the
literal contrary source context. Only the genuine earlier A/B/C remains. -/
theorem source_held_characteristicTwo
    {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (hABC : ∀ (A : Type u) [Group A] [Finite A], ChapterA.Section02.TheoremsABC κ A)
    {d : Source.Geometry G} {i j : Bool} {H K U : Subgroup G}
    (s : SourceContext d i j H K U) (hK : (K.subgroupOf H).IsCComponent)
    (e : Chapter1.XiQuotient K ≃* Held.He) :
    generalizedFitting K = pCore 2 K := by
  by_contra hF
  have hKH : K ≤ H := s.closure ▸ EmbeddingReduction.normalClosureIn_le_overgroup _ _
  have hc := source_binary_component hG SourceRecognition.Source.earlier115OneTwo s hK hF
  let : IsQuasisimple (K.subgroupOf H) := hc.2
  let eK := subgroupOfEquivOfLe hKH
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := eK.toMonoidHom) eK.surjective
  have hz := Chapter15.Section03.component_center_eq_twoCore hc
    (source_oddCore_eq_bot hG SourceRecognition.Source.earlier115OneTwo s)
  let eQ := QuotientGroup.congr (pCore 2 (K.subgroupOf H)) (pCore 2 K) eK
    (pCore_map_iso 2 eK)
  let eC := (QuotientGroup.quotientMulEquivOfEq hz).trans (eQ.trans e)
  have heZ : (center K).map eK.symm.toMonoidHom = center (K.subgroupOf H) := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.centerCongr eK.symm ⟨y, hy⟩).property
    · intro x hx
      exact ⟨eK x, (Subgroup.centerCongr eK ⟨x, hx⟩).property,
        eK.symm_apply_apply x⟩
  let eZ : K ⧸ center K ≃* Held.He :=
    (QuotientGroup.congr _ _ eK.symm heZ).trans eC
  have hfaith := (component_actions_of_earlier115 hG
    (SourceRecognition.Source.earlier115Three hABC) s.local115 hKH hc).2.2.1
  have hHK : H ≤ normalizer (K : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer hKH).mp
    rw [s.closure]
    exact EmbeddingReduction.normalClosureIn_normal _ _
  have hZU : d.Z ≤ U := by
    apply le_trans (show d.Z ≤ ChapterB.baumann (d.T : Subgroup G) from ?_)
      s.placed.baumann_le
    intro z hz
    rw [s.omega] at hz
    have hzT := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
    refine ⟨hzT.1, mem_centralizer_iff.mpr ?_⟩
    intro w hw
    have hJT : Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G) ≤
        (d.T : Subgroup G) := sSup_le fun _ hA => hA.1
    exact hzT.2.2 w (hJT ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hw).1)
  have hZC : d.Z ≤ centralizer (U : Set G) := by
    intro z hz
    rw [s.omega] at hz
    exact mem_centralizer_iff.mpr fun u hu =>
      ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 u (s.placed.upper.le hu)
  exact no_held_component_central_four hKH hHK s.placed.sylow s.placed.sylow_image
    hZU hZC s.four hfaith eZ

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
