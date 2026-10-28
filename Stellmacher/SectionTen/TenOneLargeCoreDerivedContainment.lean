module
public import Stellmacher.SectionTen.TenOneLargeCoreCentralizerSupplement
public import Stellmacher.SectionTen.TenOneLargeResidualCoreCentralizer
public import Stellmacher.SectionTen.TenOneLargeFirstFrobenius
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The endpoint two-cores are abelian modulo their modules

In the actual large Section Ten context, the full terminal two-core has
its derived subgroup in the terminal module. A short companion gives the
same containment for the first two-core. Both statements retain only the
original context, middle vertex, offset and no-transvection hypothesis;
the later bound on the core modulo its residual core is not an input.

Put U=O₂(E_terminal), V=V_terminal, Q=Q_terminal and C=C_Q(V).
Source (18) gives [U,Q]≤V. Since C centralizes V, the three-subgroups lemma
makes C' centralize U. The proved source-(19) five-residual model supplies
the genuine source-(20) equality C_Q(U)=Z, so C'≤Z≤V. The actual supplement
Q=C U and two commutator-preimage joins yield Q'≤V. These joins use only
Q-normality of V, not global normality in the ambient group.

The first companion conjugates Q_first and V_first simultaneously to the
terminal subgroups using the middle stabilizer. It applies the terminal
result in the original configuration, preserving the original path and
no-transvection premise. Source: consequences of Stellmacher (10.1)(18)–(20),
Journal of Algebra 190 (1997), printed pp.64–65.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_terminal_core_derived_le_module
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    DerivedAmbient (QAt ctx.Γ ctx.criticalPath.a') ≤
      VAt ctx.Γ ctx.criticalPath.a' := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let U := twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  let C := Q ⊓ centralizer (V : Set G)
  have hgen : Q=C⊔U := (ten_one_large_core_centralizer_supplement ctx middle hpath hno).1
  have hCQ : C≤Q := inf_le_left
  have hUQ : U≤Q := le_sup_right.trans hgen.ge
  obtain ⟨_hN,_hUV,hUQcomm⟩ := ten_one_large_residual_quotient_elementary ctx middle hpath hno
  change ⁅U,Q⁆≤V at hUQcomm
  have hUCV : ⁅U,C⁆≤V := (commutator_mono le_rfl hCQ).trans hUQcomm
  have hCV : ⁅C,V⁆=⊥ := commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hVC : ⁅V,C⁆=⊥ := by rw [commutator_comm]; exact hCV
  have hrot : ⁅⁅U,C⁆,C⁆=⊥ := bot_unique ((commutator_mono hUCV le_rfl).trans hVC.le)
  have hCCU : ⁅⁅C,C⁆,U⁆=⊥ := commutator_commutator_eq_bot_of_rotate
    (by simpa only [commutator_comm C U] using hrot) hrot
  have hfixed : Q⊓centralizer (U : Set G)=Z :=
    ten_one_large_residual_core_centralizer ctx middle hpath hno
      (ten_one_large_first_residual_five ctx middle hpath hno)
  have hZV : Z≤V :=
    (ten_one_large_terminal_core_fixed_line ctx middle hpath hno).ge.trans inf_le_left
  have hCCV : ⁅C,C⁆≤V :=
    ((le_inf ((commutator_le_self C).trans hCQ)
      (commutator_eq_bot_iff_le_centralizer.mp hCCU)).trans_eq hfixed).trans hZV
  have hQP : Q≤P := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.a'≤ctx.Γ.stabilizer ctx.criticalPath.a'
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQV : Q≤normalizer (V : Set G) := hQP.trans (stabilizer_le_normalizer_v ctx.Γ _)
  have hQC : ⁅Q,C⁆≤V := by
    have hpre : Q≤commutatorPreimage Q C V := hgen.le.trans (sup_le
      (le_commutatorPreimage hCQ hCCV) (le_commutatorPreimage hUQ hUCV))
    exact (commutator_mono hpre le_rfl).trans (commutator_commutatorPreimage_le Q C V hQV)
  have hQQ : ⁅Q,Q⁆≤V := by
    have hCQV : ⁅C,Q⁆≤V := by rw [commutator_comm]; exact hQC
    have hpre : Q≤commutatorPreimage Q Q V := hgen.le.trans (sup_le
      (le_commutatorPreimage hCQ hCQV) (le_commutatorPreimage hUQ hUQcomm))
    exact (commutator_mono hpre le_rfl).trans (commutator_commutatorPreimage_le Q Q V hQV)
  rw [show DerivedAmbient Q=⁅Q,Q⁆ from map_subtype_commutator Q]
  exact hQQ

public theorem ten_one_large_first_core_derived_le_module
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    DerivedAmbient (QAt ctx.Γ ctx.criticalPath.firstStep) ≤
      VAt ctx.Γ ctx.criticalPath.firstStep := by
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity middle
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal)
  let equiv := MulAut.conj (mover : G)⁻¹
  have hVmap : (VAt ctx.Γ ctx.criticalPath.firstStep).map equiv.toMonoidHom =
      VAt ctx.Γ ctx.criticalPath.a' := by
    change (v ctx.Γ ctx.criticalPath.firstStep).map _ = v ctx.Γ ctx.criticalPath.a'
    rw [←v_act,hmove]
  have hQmap : (QAt ctx.Γ ctx.criticalPath.firstStep).map equiv.toMonoidHom =
      QAt ctx.Γ ctx.criticalPath.a' := by
    change (q ctx.Γ ctx.criticalPath.firstStep).map _ = q ctx.Γ ctx.criticalPath.a'
    rw [←q_act,hmove]
  rw [show DerivedAmbient (QAt ctx.Γ ctx.criticalPath.firstStep)=
    ⁅QAt ctx.Γ ctx.criticalPath.firstStep,QAt ctx.Γ ctx.criticalPath.firstStep⁆ from
      map_subtype_commutator _]
  apply (map_le_map_iff_of_injective (f:=equiv.toMonoidHom) equiv.injective).mp
  rw [map_commutator,hQmap,hVmap]
  have h := ten_one_large_terminal_core_derived_le_module ctx middle hpath hno
  rw [show DerivedAmbient (QAt ctx.Γ ctx.criticalPath.a')=
    ⁅QAt ctx.Γ ctx.criticalPath.a',QAt ctx.Γ ctx.criticalPath.a'⁆ from
      map_subtype_commutator _] at h
  exact h

end Stellmacher.SectionTen
