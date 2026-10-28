module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Context
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Commutator.Action
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.FiveMutualActions
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.Source
/-!
# The A₅ source mixed-commutator clause

Both literal conjugates of V carry the original deleted five-point module.
Commutators of their rank-three subgroups into V₁ force the two actors to
be even. Their actual kernels are the opposite centralizers; the strict
B.3.2 inequalities therefore show that the full conjugate modules commute.
This proves F.9.1(e) from the original source flag, without a commutator or
recognition assumption on the surrounding configuration.

Source: Aschbacher–Smith, 13.5.7, printed pp.917–918.
-/

@[expose] public section
open Subgroup BinaryPermutation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Commutator
open Section06.CentralizerReduction A5Module
open ChapterB.Offenders.Odd.FiveMutualActions
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

omit [Finite G] in
private theorem conjugate_inverse (W : Subgroup G) (g : G) :
    (W.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = W := by
  rw [map_map]
  have h : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
    ext x
    change g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x
    group
  rw [h,map_id]

/-- In the A5 source, the mixed-commutator hypotheses already force the
entire two chosen conjugate modules to commute. -/
theorem source_conjugates_commute (d : Context T L V V₁ V₂ V₃)
    (g : G) (hg : g ∈ centralizer (V₁ : Set G))
    (hVV : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom)
    (h₁ : ⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V₁)
    (h₂ : ⁅V₃.map (MulAut.conj g).toMonoidHom,V⁆ ≤ V₁) :
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let : IsElementaryAbelian 2 V := d.elementary
  let U := V.map (MulAut.conj g).toMonoidHom
  let R := V.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.map _
  have hUN : U ≤ normalizer (V : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hVV.trans inf_le_left)
  have hRV : ⁅R,V⁆ ≤ V := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hVV.trans inf_le_right)
    rwa [map_commutator,conjugate_inverse] at hh
  have hRN : R ≤ normalizer (V : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (by rwa [commutator_comm])
  have hpoint : V₁.map (MulAut.conj g⁻¹).toMonoidHom = V₁ :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (V₁ : Set G)).inv_mem
      (Subgroup.centralizer_le_normalizer _ hg))
  have hR₃ : ⁅V₃,R⁆ ≤ V₁ := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h₂
    rwa [map_commutator,conjugate_inverse,hpoint] at hh
  have hUeven := actor_even d.flag V₃ U d.third_le d.third_card d.third_invariant hUN h₁
  have hReven := actor_even d.flag V₃ R d.third_le d.third_card d.third_invariant hRN hR₃
  let first : ModuleAction V U :=
    { moduleMap := d.flag.module.map
      injective := d.flag.module.injective
      range_eq := d.flag.module.range_eq
      actor := actor d.flag U hUN
      equivariant := fun a x => d.flag.normalizer_equivariant (inclusion hUN a) x }
  let back : V →* R :=
    ((MulAut.conj g⁻¹).toMonoidHom.comp V.subtype).codRestrict R
      (fun v => mem_map_of_mem _ v.property)
  let psi : V →* Equiv.Perm (Fin 5) := (actor d.flag R hRN).comp back
  let second : ModuleAction U V :=
    { moduleMap := (MulAut.conj g).toMonoidHom.comp d.flag.module.map
      injective := (MulAut.conj g).injective.comp d.flag.module.injective
      range_eq := by rw [MonoidHom.range_comp,d.flag.module.range_eq]
      actor := psi
      equivariant := by
        intro v x
        have hh := d.flag.normalizer_equivariant (inclusion hRN (back v)) x
        change (g⁻¹ * v.val * (g⁻¹)⁻¹) * d.flag.module.map (Multiplicative.ofAdd x) *
          (g⁻¹ * v.val * (g⁻¹)⁻¹)⁻¹ =
          d.flag.module.map (Multiplicative.ofAdd (coreRepresentation (Fin 5) (psi v) x)) at hh
        simp only [inv_inv] at hh
        change v.val * (g * d.flag.module.map (Multiplicative.ofAdd x) * g⁻¹) * v.val⁻¹ =
          g * d.flag.module.map (Multiplicative.ofAdd (coreRepresentation (Fin 5) (psi v) x)) * g⁻¹
        rw [← hh]
        group }
  have hsecond : second.actor.range ≤ alternatingGroup (Fin 5) := by
    rintro p ⟨v,rfl⟩
    exact hReven ⟨back v,rfl⟩
  exact first.commute_of_even second hUeven hsecond

/-- The exact commutator-lifting field of F9.1 on the original H. -/
theorem source_commutator_lifting (d : Context T L V V₁ V₂ V₃)
    (H : Subgroup G) (hH : H ≤ centralizer (V₁ : Set G)) :
    ∀ g ∈ H,
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom →
      ⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V₁ →
      ⁅V₃.map (MulAut.conj g).toMonoidHom,V⁆ ≤ V₁ →
      ⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
        ⁅V₃.map (MulAut.conj g).toMonoidHom,V⁆ = ⊥ := by
  intro g hg hVV h₁ h₂
  have hh := source_conjugates_commute d g (hH hg) hVV h₁ h₂
  refine ⟨bot_unique ((commutator_mono d.third_le le_rfl).trans_eq hh), ?_⟩
  apply bot_unique
  apply (commutator_mono (map_mono d.third_le) le_rfl).trans_eq
  rwa [commutator_comm]
/-- The same source conclusion in the literal centralizer of a generator
of V₁, as used by the final A₅ setup. -/
theorem source_centralizer_conjugates_commute (d : Context T L V V₁ V₂ V₃)
    (z : G) (hz : V₁ = zpowers z) (g : G) (hg : g ∈ Gv z)
    (hVV : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom)
    (h₁ : ⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V₁)
    (h₂ : ⁅V₃.map (MulAut.conj g).toMonoidHom,V⁆ ≤ V₁) :
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hc : Gv z ≤ centralizer (V₁ : Set G) := by
    rw [hz, le_centralizer_iff, zpowers_le]
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  exact source_conjugates_commute d g (hc hg) hVV h₁ h₂

end CFSG.Quasithin.Chapter13.Section05.A5Source.Commutator
