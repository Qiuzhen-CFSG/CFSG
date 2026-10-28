module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.SplitAndCentral.Split.Coordinates

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.SplitAndCentral.Split.Linear

/-!
# The doubled-natural source-(3.3) calculation

For the actual critical pair, the marked opposite image is an elementary
four-group with fixed codimension at most two on the two natural copies.
Its moved space lies in the coordinates of D = [X_a,X_a']. An actor
centralizing D therefore fixes that space pointwise; the finite plane-fixer
calculation puts every moving displacement back in D. The fixed summand
centralizes the whole local stabilizer, extending the bound from U to X.

Conjugation transports the calculation to every critical endpoint. Since
X = Z in this branch, the source actors centralize D, and the ambient bound
gives the exact displacement in X_a'/[Z_a,Z_a'] required by the unchanged
quotient criterion. The specified path and the original two-copy marking
are retained; no displacement or model-recognition premise is assumed.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.2)(iii), p.863, and (3.3), pp.866–868.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation.Split
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem uAction_base_apply (source : LocalSource L R)
    (s : stabilizer R (alpha R)) (u : U R (alpha R)) :
    (uAction source (baseProjection source s) u : FreeAmalgam R) =
      s * u * (s : FreeAmalgam R)⁻¹ := by
  obtain ⟨m, rfl⟩ := (baseEquiv (R := R)).surjective s
  rw [baseProjection_baseEquiv, uAction, layerAction_apply, baseEquiv_val]

private theorem base_moving_bound (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hmodel : SplitDouble source)
    (a : Vertex R)
    (hc : CriticalPair R (alpha R) a (geometry.exists_critical (alpha R) rfl))
    (Y : Subgroup (FreeAmalgam R)) (hYS : Y ≤ stabilizer R (alpha R))
    (hYC : Y ≤ centralizer ((⁅X R a, X R (alpha R)⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R))) :
    ⁅U R (alpha R), Y⁆ ≤ ⁅X R a, X R (alpha R)⁆ := by
  let := geometry.U_elementary hb (alpha R) rfl
  obtain ⟨model⟩ := hmodel.1
  let e := movingCoordinates source geometry hb model
  let ρ := AbelianCore.DoubleCopy.natural
  let E := markedImage source model (X R a)
  let D := ⁅X R a, X R (alpha R)⁆
  let H := AddSubgroup.toZModSubmodule 2
    (Subgroup.toAddSubgroup (D.subgroupOf (U R (alpha R))))
  let W := H.map e.toLinearMap
  have hUX : U R (alpha R) ≤ X R (alpha R) := by
    rw [splitDouble_X_eq_Z source geometry hb hmodel (alpha R) rfl]
    exact U_le_Z _
  have hact (g : SL) (v : Additive (U R (alpha R))) :
      e ((Offenders.linearize (uAction source)) g v) = ρ (model.marking g) (e v) :=
    movingCoordinates_equivariant source geometry hb model g v
  have hm : subspaceCommutator ρ ⊤ E ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, _, rfl⟩
    obtain ⟨j, hj, rfl⟩ := hg
    obtain ⟨s, hs, rfl⟩ := hj
    obtain ⟨u, rfl⟩ := e.surjective v
    erw [← hact (baseProjection source s) u, ← map_sub]
    refine ⟨_, ?_, rfl⟩
    simp only [sub_eq_add_neg]
    change (uAction source (baseProjection source s) u.toMul : FreeAmalgam R) *
      (u.toMul : FreeAmalgam R)⁻¹ ∈ D
    rw [uAction_base_apply]
    exact commutator_mem_commutator hs (hUX u.toMul.property)
  obtain ⟨hcard, hE, hcodim⟩ :=
    critical_markedImage_data source geometry hb hmodel model a hc
  rw [commutator_comm]
  apply commutator_le.mpr
  intro y hy u hu
  let s : stabilizer R (alpha R) := ⟨y, hYS hy⟩
  let v : Additive (U R (alpha R)) := Additive.ofMul ⟨u, hu⟩
  have hfix : ∀ w ∈ subspaceCommutator ρ ⊤ E,
      ρ (model.marking (baseProjection source s)) w = w := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hm hw
    erw [← hact (baseProjection source s) z]
    apply congrArg e
    apply Additive.toMul.injective
    apply Subtype.ext
    change (uAction source (baseProjection source s) z.toMul : FreeAmalgam R) = z.toMul
    rw [uAction_base_apply]
    have hzD : (z.toMul : FreeAmalgam R) ∈ D := hz
    have he := hYC hy (z.toMul : FreeAmalgam R) hzD
    change (z.toMul : FreeAmalgam R) * y = y * z.toMul at he
    rw [← he, mul_assoc, mul_inv_cancel, mul_one]
  have hd := hm (Linear.displacement_mem_of_fixes_moved E hE hcard hcodim
    (model.marking (baseProjection source s)) hfix (e v))
  erw [← hact (baseProjection source s) v, ← map_sub] at hd
  obtain ⟨z, hz, he⟩ := hd
  have he' := e.injective he
  rw [he'] at hz
  simp only [sub_eq_add_neg] at hz
  change (uAction source (baseProjection source s) v.toMul : FreeAmalgam R) *
    (v.toMul : FreeAmalgam R)⁻¹ ∈ D at hz
  rw [uAction_base_apply] at hz
  exact hz

private theorem base_bound (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hmodel : SplitDouble source)
    (a : Vertex R)
    (hc : CriticalPair R (alpha R) a (geometry.exists_critical (alpha R) rfl))
    (Y : Subgroup (FreeAmalgam R)) (hYS : Y ≤ stabilizer R (alpha R))
    (hYC : Y ≤ centralizer ((⁅X R a, X R (alpha R)⁆ :
      Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R))) :
    ⁅X R (alpha R), Y⁆ ≤ ⁅X R a, X R (alpha R)⁆ := by
  let := X_elementary R (alpha R)
  have ha := critical_endpoint_color R (alpha R) rfl _ hc
  have hrev := source.critical_reverse geometry (alpha R) rfl a ha hc
  have hAS := critical_X_le_stabilizer source geometry hb a ha (alpha R) hrev
  let D := ⁅X R a, X R (alpha R)⁆
  have hDX : D ≤ X R (alpha R) :=
    le_normalizer_iff_commutator_le_right.mp (hAS.trans (X_normalized R (alpha R)))
  have hnD : X R (alpha R) ≤ normalizer (D : Set (FreeAmalgam R)) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx d hd
    exact congrArg Subtype.val (mul_comm (⟨d, hDX hd⟩ : X R (alpha R)) ⟨x, hx⟩)
  have hfixed : fixedPart R ≤ centralizer (Y : Set (FreeAmalgam R)) := by
    intro c hc y hy
    exact ((source.X_fixed_eq_stabilizer_fixed (alpha R) rfl).le hc).2 y (hYS hy)
  have hUX : U R (alpha R) ≤ X R (alpha R) := by
    rw [hmodel.2.1]
    exact le_sup_right
  have hpre : X R (alpha R) ≤ commutatorPreimage (X R (alpha R)) Y D := by
    conv_lhs => rw [hmodel.2.1]
    exact sup_le
      (le_commutatorPreimage (show fixedPart R ≤ X R (alpha R) from inf_le_left)
        ((commutator_eq_bot_iff_le_centralizer.mpr hfixed).le.trans bot_le))
      (le_commutatorPreimage hUX
        (base_moving_bound source geometry hb hmodel a hc Y hYS hYC))
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le (X R (alpha R)) Y D hnD)

/-- In the doubled branch, any local actor centralizing the critical
commutator has its entire endpoint displacement inside that commutator. -/
theorem bound (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hmodel : SplitDouble source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (Y : Subgroup (FreeAmalgam R)) (hYS : Y ≤ stabilizer R a')
    (hYC : Y ≤ centralizer ((⁅X R a, X R a'⁆ :
      Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R))) :
    ⁅X R a', Y⁆ ≤ ⁅X R a, X R a'⁆ := by
  have ha' := critical_endpoint_color R a ha _ hc
  obtain ⟨frame⟩ := exists_frame a' ha'
  let f := frame.element⁻¹
  let ψ := MulAut.conj f⁻¹
  have hf : act R f a' = alpha R := by
    rw [← frame.vertex]
    simp only [f, ← act_mul, mul_inv_cancel, act_one]
  have hfa : color R (act R f a) = false := by simpa only [action_preserves_color] using ha
  have hfa' : color R (act R f a') = false := by rw [hf]; rfl
  have hc' := (criticalPair_act_iff R f a a' (geometry.exists_critical a ha)
    (geometry.exists_critical (act R f a) hfa)).mpr hc
  have hrev := source.critical_reverse geometry (act R f a) hfa
    (act R f a') hfa' hc'
  have hS : Y.map ψ.toMonoidHom ≤ stabilizer R (act R f a') := by
    rw [stabilizer_act]
    exact map_mono hYS
  have hC : Y.map ψ.toMonoidHom ≤
      centralizer ((⁅X R (act R f a), X R (act R f a')⁆ :
        Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
    rw [X_act, X_act, ← map_commutator]
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, commutator_eq_bot_iff_le_centralizer.mpr hYC, Subgroup.map_bot]
  have hbnd : ⁅X R (act R f a'), Y.map ψ.toMonoidHom⁆ ≤
      ⁅X R (act R f a), X R (act R f a')⁆ := by
    simp only [hf] at hrev hS hC ⊢
    exact base_bound source geometry hb hmodel (act R f a) hrev _ hS hC
  rw [X_act, X_act, ← map_commutator, ← map_commutator] at hbnd
  exact (map_le_map_iff_of_injective ψ.injective).mp hbnd

/-- The literal source-(3.3) quotient calculation for the actual centralizing
edge actors, with the exact relative quotient and right-hand side of the
parent criterion. The only action premise is its literal conjugation formula. -/
theorem quotient_displacement (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R) (hmodel : SplitDouble source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a' t)
    (_hpath : (cosetGraph R).dist a t + 1 = (cosetGraph R).dist a a')
    (Y : Subgroup (FreeAmalgam R))
    (hY : Y ≤ SourceThree.centralizingActors R a a' t) :
    letI := SourceThree.critical_Z_quotient_normal a a'
    ∀ action : SourceThree.centralizingActors R a a' t →*
        MulAut (X R a' ⧸ (⁅Z R a, Z R a'⁆).subgroupOf (X R a')),
      (∀ actor : SourceThree.centralizingActors R a a' t, ∀ point : X R a',
        action actor
          (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')) point) =
        QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a'))
          ⟨(actor : FreeAmalgam R) * (point : FreeAmalgam R) *
              (actor : FreeAmalgam R)⁻¹,
            (mem_normalizer_iff.mp
              (SourceThree.centralizingActors_normalize_X a a' t hat actor.property) point).mp
                point.property⟩) →
      ∀ actor : SourceThree.centralizingActors R a a' t, (actor : FreeAmalgam R) ∈ Y →
        ∀ point : X R a', (point : FreeAmalgam R) ∈ Z R a' →
        (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')) point)⁻¹ *
          action actor
            (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')) point) ∈
          ((⁅X R a, X R a'⁆ ⊔ ⁅X R a ⊓ Q R a', Y⁆).subgroupOf (X R a')).map
            (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a'))) := by
  let := SourceThree.critical_Z_quotient_normal a a'
  intro action hformula
  apply (bound_iff_quotient_displacement source geometry hb a ha a' hc t hat Y hY
    action hformula).mp
  have ha' := critical_endpoint_color R a ha _ hc
  have hYS : Y ≤ stabilizer R a' := by
    intro y hy
    exact (hY hy).1.2 a' (adjacent_symm R hat)
  have hYC : Y ≤ centralizer ((⁅X R a, X R a'⁆ :
      Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
    rw [← splitDouble_commutator_eq source geometry hb hmodel a a' ha ha']
    exact hY.trans inf_le_right
  rw [← splitDouble_X_eq_Z source geometry hb hmodel a' ha']
  exact (bound source geometry hb hmodel a ha a' hc Y hYS hYC).trans le_sup_left

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation.Split
