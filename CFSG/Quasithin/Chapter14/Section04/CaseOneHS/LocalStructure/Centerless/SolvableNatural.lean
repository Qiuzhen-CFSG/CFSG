module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableActionQuotient
public import Theory.Representation.ConjugatePointNatural

/-!
# H.5.5 on the original Goldschmidt point orbit

One quotient isomorphism simultaneously marks I₂T as the line parabolic
and KT as the point parabolic. KT fixes the original point V₁, while its
I₂T-orbit is exactly V₂ of order four. The reduced orbit Ue is elementary,
and its literal centralizer kernel permits descent of conjugation through
the marked quotient. H.5.5 supplies equivariant natural coordinates and
proves |Ue| = 8.

The final application constructs this order-eight orbit from the original
solvable model and nontrivial Z(I₂), retaining the same shifted actor and
its central action. The opposite dimension inequality and exhaustive
centerlessness assembly are still required.
Source: Aschbacher--Smith 14.3.31, printed p.1003, and H.5.5, p.386.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- H.5.5 on the literal point orbit, with both original local vertices marked. -/
theorem source_amalgam_natural (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (K : Subgroup G) (hKH : K ≤ F.H)
    (hr : IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)))
    (hg : ChapterF.IsGoldschmidtTriple
      (((K ⊔ (T : Subgroup G)).subgroupOf (amalgamGroup F L K)).map (QuotientGroup.mk' (amalgamKernel F L K)))
      (((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf (amalgamGroup F L K)).map (QuotientGroup.mk' (amalgamKernel F L K))))
    (model : Nonempty (AmalgamQuotient F L K ≃* Matrix.PSL3Two.PSL)) :
    let E := amalgamGroup F L K
    let W := amalgamModule F L K
    ∃ π : E →* Matrix.PSL3Two.SL, Function.Surjective π ∧
      π.ker = amalgamKernel F L K ∧
      ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E).map π = Matrix.PSL3Two.lineParabolicSL ∧
      ((K ⊔ (T : Subgroup G)).subgroupOf E).map π = Matrix.PSL3Two.pointParabolicSL ∧
      ∃ c : W ≃* Multiplicative BinaryLinearThree.Vector,
        (∀ (a : E) (w : W),
          (c (W.normalizerMonoidHom (inclusion (le_normalizer_conjugateSpanBy _ _) a) w)).toAdd =
            BinaryLinearThree.W (π a) (c w).toAdd) ∧ Nat.card W = 8 := by
  let := chosen.elementary
  let E := amalgamGroup F L K
  let W := amalgamModule F L K
  let A := K ⊔ (T : Subgroup G)
  let B := F.I₂ L ⊔ (T : Subgroup G)
  let D := AmalgamQuotient F L K
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  let q₀ := QuotientGroup.mk' (pCore 2 D)
  have hcore : pCore 2 D = ⊥ := hr.quotient_pCore_eq_bot
  have hq₀ : Function.Injective q₀ := q₀.ker_eq_bot_iff.mp (by rw [QuotientGroup.ker_mk',hcore])
  let j : D ≃* D ⧸ pCore 2 D := MulEquiv.ofBijective q₀ ⟨hq₀,QuotientGroup.mk'_surjective _⟩
  obtain ⟨_,m,_,_,hline,hpoint⟩ := mark_goldschmidt_quotient
    ((B.subgroupOf E).map q) ((A.subgroupOf E).map q) hg.symm (j.symm.trans model.some)
  let π : E →* Matrix.PSL3Two.SL := m.toMonoidHom.comp (q₀.comp q)
  have hπ : Function.Surjective π := m.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hker : π.ker = amalgamKernel F L K := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.injective,
      MonoidHom.ker_comp_of_injective _ _ hq₀,QuotientGroup.ker_mk']
  have hline' : (B.subgroupOf E).map π = Matrix.PSL3Two.lineParabolicSL := by
    simpa only [map_map] using hline
  have hpoint' : (A.subgroupOf E).map π = Matrix.PSL3Two.pointParabolicSL := by
    simpa only [map_map] using hpoint
  have hWE : W ≤ E := conjugateSpanBy_le_self
    ((F.le_seed 1).trans (chosen.le_sylow.trans (sylow_le_amalgamGroup F L K)))
  let := hr.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_surjective
    (subgroupOfEquivOfLe hWE).toMonoidHom (subgroupOfEquivOfLe hWE).surjective
  obtain ⟨z,hz,hzpoint⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hBC : A ≤ centralizer (F.Vi 1 : Set G) :=
    (sup_le hKH (F.invariant 1)).trans (normalizer_le_centralizer_of_card_two _
      (by simpa using F.card 1 (by decide)))
  have hBP : B = F.P L := (source_parabolic_eq_I₂_sylow d earlier hq chosen structural alternatives F hne).symm
  have hplane : conjugateSpanBy (F.Vi 1) B = F.Vi 2 := by
    rw [hBP]
    apply le_antisymm (conjugateSpanBy_le (F.monotone (by decide))
      (F.P_le_G₂ (by decide) L chosen.normalizes))
    obtain ⟨g,hgP,hgH⟩ := source_conjugator d earlier hq chosen structural F
    rw [←F.binary_plane_point_span (by decide) L chosen.normalizes g hgP hgH]
    exact sup_le (le_conjugateSpanBy _ _)
      (conjugate_le_of_normalizes (le_conjugateSpanBy _ _) g (le_normalizer_conjugateSpanBy _ _ hgP))
  obtain ⟨c,hc⟩ := Representation.ConjugatePointNatural.exists_natural_coordinates
    E W (F.Vi 1) B A (le_normalizer_conjugateSpanBy _ _) (le_conjugateSpanBy _ _)
    z hzpoint hz π hπ (by
      rw [hker]
      intro x hx w hw
      exact congrArg Subtype.val (hx ⟨w,hWE hw⟩ hw))
    le_sup_right hline' hpoint' hBC rfl (by rw [hplane]; simpa using F.card 2 (by decide))
  refine ⟨π,hπ,hker,hline',hpoint',c,hc,?_⟩
  rw [Nat.card_congr c.toEquiv]
  simp [BinaryLinearThree.Vector]

/-- The original solvable contrary branch has a point orbit of order eight,
with its original shifted actor, characteristic-two quotient and center action. -/
theorem source_solvable_orbit_card_eight (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : Chapter14.Section04.LargerDimension.LocalAction.Components.EarlierFaithfulClassification
      G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      K ≤ F.H ∧ F.H ≤ normalizer (K : Set G) ∧ K ≤ centralizer (F.ZU : Set G) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) ∧
      E ≤ centralizer ({e} : Set G) ∧
      IsPReduced 2 ((amalgamModule F L K).subgroupOf E) ∧
      amalgamKernel F L K = pPrimeCore 3 E ∧
      Nonempty (AmalgamQuotient F L K ≃* Matrix.PSL3Two.PSL) ∧
      Nat.card (amalgamModule F L K) = 8 := by
  obtain ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hE,hr,hker,hm,hg,_⟩ :=
    source_solvable_action_recognition d earlier hq chosen structural alternatives
      classification F hne hZ model hI
  obtain ⟨_,_,_,_,_,_,_,hc⟩ := source_amalgam_natural d earlier hq chosen structural alternatives
    F hne _ hKH hr hg hm
  exact ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hE,hr,hker,hm,hc⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
