module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.SplitAndCentral.Central.FixedPlane
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.ComponentOffender.BestProjection.CentralTwist.Generation

/-!
# The central-extension calculation for MS93 (3.3)

Retain the actual natural quotient U/(C ∩ U), whose kernel has order two.
The transported marked quotient gives |U| = 16. Full commutation and the
three conjugate involutions generating SL₃(2) show that each nontrivial
involution moves at least two dimensions of U.

At a critical pair choose z in Z_a outside Q_a'. Its displacement space
on U_a' lies in D = [X_a,X_a'] and has dimension at least two. In this
branch X = Z, so the permitted actors Q_t ∩ C([Z_a,Z_a']) fix that space.
They have two-power order. The fixed-plane calculation puts all their U
displacements in D. The actual fixed part C centralizes the full endpoint
stabilizer, so X = C U gives [Z_a',Y] ≤ D. Passing to the literal quotient
proves the requested displacement statement with D ⊔ [X_a ∩ Q_a',Y].

All ranks, fixed spaces and action formulas used here are derived from
the source inputs. In particular the central extension is never split.
The ambient calculation only needs adjacency; the quotient export retains
the actual penultimate-vertex path hypothesis for the source interface.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), notation (3.0), p.859; (3.2)(iv), p.863; (3.3), pp.866–868.
-/

public section
open Representation Representation.BinaryOffender
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation.Central
open scoped IsMulCommutative commutatorElement
open SourceThree
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The central-extension calculation in the ambient group. -/
theorem bound (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (h : CentralExtension source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a' t)
    (Y : Subgroup (FreeAmalgam R))
    (hY : Y ≤ SourceThree.centralizingActors R a a' t) :
    ⁅Z R a', Y⁆ ≤ ⁅X R a, X R a'⁆ := by
  classical
  let := geometry.U_elementary hb (alpha R) rfl
  let := X_elementary R a
  let := X_elementary R a'
  let := finite_Z R (alpha R)
  let := finite_X R a'
  let : Finite (U R (alpha R)) :=
    Finite.of_injective (inclusion (U_le_Z (R := R) (alpha R))) (inclusion_injective _)
  let ρ := Offenders.linearize (uAction source)
  have ha' := critical_endpoint_color R a ha _ hc
  obtain ⟨frame⟩ := exists_frame a' ha'
  obtain ⟨⟨model⟩, hsum, hk⟩ := centralExtension_at source h a' frame
  have hcard : Nat.card (U R (alpha R)) = 16 :=
    (Nat.card_congr frame.movingEquiv.toEquiv).trans (model.card_one hk)
  have hdim : Module.finrank (ZMod 2) (Additive (U R (alpha R))) = 4 := by
    have hs := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive (U R (alpha R)))
    rw [Nat.card_zmod] at hs
    change Nat.card (U R (alpha R)) = _ at hs
    rw [hcard] at hs
    have he : 2 ^ Module.finrank (ZMod 2) (Additive (U R (alpha R))) = 2 ^ 4 := hs.symm
    exact (Nat.pow_right_injective (by decide : 1 < 2)) he
  have hm : ∀ g : SL, g ^ 2 = 1 → g ≠ 1 → 2 ≤ fixedCodim ρ (zpowers g) := by
    intro g hg hne
    have hgen := ComponentOffender.BestProjection.CentralTwist.finrank_le_three_mul_twist_codim
      ρ (MonoidHom.id SL) 1 (by simp) (fun _ => Commute.one_left _)
      (by simpa using uAction_full source geometry hb) g hg hne
    simp only [MonoidHom.id_apply, mul_one, hdim] at hgen
    omega
  have hact (g : stabilizer R a') (u : U R (alpha R)) :
      frame.conjugation (uAction source (frame.projection source g) u : FreeAmalgam R) =
        (g : FreeAmalgam R) * frame.conjugation (u : FreeAmalgam R) *
          (g : FreeAmalgam R)⁻¹ := by
    obtain ⟨m, rfl⟩ := frame.localEquiv.surjective g
    rw [frame.projection_localEquiv, uAction, layerAction_apply, map_mul, map_mul,
      map_inv, ← frame.localEquiv_val]
  let D := ⁅X R a, X R a'⁆
  have hZX : Z R a ≤ X R a := geometry.omega_bound a ha (by
    rw [geometry.distance_constant a ha]; exact hb)
  obtain ⟨z, hz, hzQ⟩ := Set.not_subset.mp hc.2
  have hzX := hZX hz
  have hzS := critical_X_le_stabilizer source geometry hb a ha a' hc hzX
  let g : SL := frame.projection source ⟨z, hzS⟩
  have hg2 : g ^ 2 = 1 := by
    rw [← map_pow]
    have hz2 : (⟨z, hzS⟩ : stabilizer R a') ^ 2 = 1 :=
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) z hzX)
    rw [hz2, map_one]
  have hgne : g ≠ 1 := by
    intro he
    have hh : (⟨z, hzS⟩ : stabilizer R a') ∈ (frame.projection source).ker := he
    rw [frame.projection_kernel] at hh
    exact hzQ hh
  let W := LinearMap.range (ρ g - LinearMap.id)
  have hW : 2 ≤ Module.finrank (ZMod 2) W := by
    simpa only [fixedCodim_zpowers_eq_displacement_rank] using hm g hg2 hgne
  have hWD (w : W) : frame.conjugation (w.val.toMul : FreeAmalgam R) ∈ D := by
    obtain ⟨v, hv⟩ := w.property
    rw [← hv]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, toMul_sub, div_eq_mul_inv,
      Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    change frame.conjugation (uAction source g v.toMul : FreeAmalgam R) *
      (frame.conjugation (v.toMul : FreeAmalgam R))⁻¹ ∈ D
    rw [hact]
    exact commutator_mem_commutator hzX ((U_le_Z a').trans
      (centralExtension_X_eq_Z source geometry hb h a' ha').ge
      (by rw [← frame.map_U]; exact mem_map_of_mem _ v.toMul.property))
  have hYS : Y ≤ stabilizer R a' := fun y hy =>
    (hY hy).1.2 a' (adjacent_symm R hat)
  have hUD : ⁅U R a', Y⁆ ≤ D := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro y hy u hu
    let yS : stabilizer R a' := ⟨y, hYS hy⟩
    let ybar := frame.projection source yS
    have hp : ∃ n : ℕ, ybar ^ (2 ^ n) = 1 := by
      obtain ⟨n, hn⟩ := (kernel_isPGroup source t).exists_pow_pow_eq_one ⟨y, (hY hy).1⟩
      have hh : yS ^ (2 ^ n) = 1 := Subtype.ext (congrArg (fun q : Q R t => (q : FreeAmalgam R)) hn)
      exact ⟨n, by rw [← map_pow, hh, map_one]⟩
    have hfix : W ≤ fixedSpace ρ (zpowers ybar) := by
      intro w hw
      rw [mem_fixedSpace_zpowers_iff]
      apply Additive.toMul.injective
      apply Subtype.ext
      apply frame.conjugation.injective
      change frame.conjugation (uAction source ybar w.toMul : FreeAmalgam R) =
        frame.conjugation (w.toMul : FreeAmalgam R)
      rw [hact]
      have hcD : y ∈ centralizer (D : Set (FreeAmalgam R)) := by
        have hh := (hY hy).2
        rwa [centralExtension_commutator_eq source geometry hb h a a' ha ha'] at hh
      have hh := hcD _ (hWD ⟨w, hw⟩)
      change frame.conjugation (w.toMul : FreeAmalgam R) * y =
        y * frame.conjugation (w.toMul : FreeAmalgam R) at hh
      change y * frame.conjugation (w.toMul : FreeAmalgam R) * y⁻¹ = _
      rw [← hh, mul_inv_cancel_right]
    let v := Additive.ofMul (frame.movingEquiv.symm ⟨u, hu⟩)
    have hmem : ρ ybar v - v ∈ W :=
      displacement_le_fixed_plane ρ hdim hm W hW ybar hp hfix ⟨v, rfl⟩
    have hh := hWD ⟨ρ ybar v - v, hmem⟩
    simp only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      map_mul, map_inv] at hh
    change frame.conjugation (uAction source ybar v.toMul : FreeAmalgam R) *
      (frame.conjugation (v.toMul : FreeAmalgam R))⁻¹ ∈ D at hh
    rw [hact] at hh
    have hv : frame.conjugation (v.toMul : FreeAmalgam R) = u :=
      frame.movingEquiv_symm_val ⟨u, hu⟩
    simpa only [hv, commutatorElement_def] using hh
  have hDX : D ≤ X R a' :=
    (critical_commutator_le_intersection source geometry hb a ha a' hc).trans inf_le_right
  have hXD : X R a' ≤ normalizer (D : Set (FreeAmalgam R)) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx d hd
    exact congrArg Subtype.val (mul_comm (⟨d, hDX hd⟩ : X R a') ⟨x, hx⟩)
  have hfixed : fixedAt R a' ≤ centralizer (Y : Set (FreeAmalgam R)) := by
    intro c hc y hy
    exact ((source.X_fixed_eq_stabilizer_fixed a' ha').le hc).2 y (hYS hy)
  have hUX : U R a' ≤ X R a' := (U_le_Z a').trans
    (centralExtension_X_eq_Z source geometry hb h a' ha').ge
  have hpre : X R a' ≤ commutatorPreimage (X R a') Y D := by
    conv_lhs => rw [hsum]
    exact sup_le
      (le_commutatorPreimage (show fixedAt R a' ≤ X R a' from inf_le_left)
        ((commutator_eq_bot_iff_le_centralizer.mpr hfixed).le.trans bot_le))
      (le_commutatorPreimage hUX hUD)
  rw [← centralExtension_X_eq_Z source geometry hb h a' ha']
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le (X R a') Y D hXD)

/-- The exact source-(3.3) quotient displacement, for literal conjugation
and the actual penultimate vertex, with no additional model premises. -/
theorem quotient_displacement (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R) (hmodel : CentralExtension source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a' t)
    (_hpath : (cosetGraph R).dist a t + 1 = (cosetGraph R).dist a a')
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ centralizingActors R a a' t) :
    letI := critical_Z_quotient_normal a a'
    ∀ action : centralizingActors R a a' t →*
        MulAut (X R a' ⧸ (⁅Z R a, Z R a'⁆).subgroupOf (X R a')),
      (∀ actor : centralizingActors R a a' t, ∀ point : X R a',
        action actor
          (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')) point) =
        QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a'))
          ⟨(actor : FreeAmalgam R) * (point : FreeAmalgam R) *
              (actor : FreeAmalgam R)⁻¹,
            (mem_normalizer_iff.mp
              (centralizingActors_normalize_X a a' t hat actor.property) point).mp
                point.property⟩) →
      ∀ actor : centralizingActors R a a' t, (actor : FreeAmalgam R) ∈ Y →
          ∀ point : X R a', (point : FreeAmalgam R) ∈ Z R a' →
          (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')) point)⁻¹ *
            action actor
              (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')) point) ∈
            ((⁅X R a, X R a'⁆ ⊔ ⁅X R a ⊓ Q R a', Y⁆).subgroupOf (X R a')).map
              (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a'))) := by
  let := SourceThree.critical_Z_quotient_normal a a'
  intro action hformula
  exact (bound_iff_quotient_displacement source geometry hb a ha a' hc t hat Y hY
    action hformula).mp ((bound source geometry hb hmodel a ha a' hc t hat Y hY).trans
      le_sup_left)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation.Central
