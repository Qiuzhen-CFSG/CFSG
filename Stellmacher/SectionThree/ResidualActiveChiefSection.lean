module

public import Stellmacher.SectionsOneToFourDefs
public import Stellmacher.SectionThree.ResidualTwoLayerKernel
public import Theory.GroupAction.MinimalNormal
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupAction.SubgroupQuotientIrreducible

/-!
# A chief section retaining a nontrivial residual action

A finite group's two-residual acting nontrivially on a normal elementary
abelian two-subgroup also acts nontrivially on an actual irreducible section
of that subgroup. Choose a minimal invariant subgroup with active residual
action, then a maximal proper invariant denominator. The quotient action is
literal conjugation; the general quotient correspondence proves its
irreducibility. The residual two-layer kernel theorem excludes trivial
residual action on this quotient.

This supplies the chief constituent in Stellmacher (8.4), printed p.40.
The maximal-denominator quotient correspondence is shared at the lower
`Theory.GroupAction.SubgroupQuotientIrreducible` layer for the later intrinsic
chief quotient in (10.1)(15). The public section and action are unchanged.
-/

open scoped Pointwise commutatorElement IsMulCommutative

namespace Stellmacher.SectionThree

private theorem select_residual_active_pair
    {H : Type*} [Group H] [Finite H] (P C : Subgroup H)
    (hPC : P ≤ Subgroup.normalizer (C : Set H))
    (hres : ⁅twoResidualAmbient P,C⁆ ≠ ⊥) :
    ∃ E D : Subgroup H, E ≤ C ∧ D < E ∧
      P ≤ Subgroup.normalizer (E : Set H) ∧
      P ≤ Subgroup.normalizer (D : Set H) ∧
      ⁅twoResidualAmbient P,E⁆ ≠ ⊥ ∧
      ⁅twoResidualAmbient P,D⁆ = ⊥ ∧
      (∀ L : Subgroup H, D ≤ L → L < E →
        P ≤ Subgroup.normalizer (L : Set H) → L = D) := by
  classical
  obtain ⟨E, hE, hEC, hmin⟩ := exists_minimal_subgroup_of_mem_le
    (fun L : Subgroup H => P ≤ Subgroup.normalizer (L : Set H) ∧
      ⁅twoResidualAmbient P,L⁆ ≠ ⊥) C ⟨hPC,hres⟩
  have hEbot : E ≠ ⊥ := by
    intro heq
    exact hE.2 (by simp [heq])
  obtain ⟨D, _, hD⟩ := Finite.exists_le_maximal
    (p := fun L : Subgroup H => L < E ∧ P ≤ Subgroup.normalizer (L : Set H))
    (a := ⊥) ⟨bot_lt_iff_ne_bot.mpr hEbot, by
      rw [Subgroup.le_normalizer_iff]
      simp⟩
  refine ⟨E,D,hEC,hD.prop.1,hE.1,hD.prop.2,hE.2,?_,?_⟩
  · by_contra hactive
    exact hD.prop.1.ne (hmin D ⟨hD.prop.2,hactive⟩ hD.prop.1.le)
  · intro L hDL hLE hPL
    exact le_antisymm (hD.2 ⟨hLE,hPL⟩ hDL) hDL

private theorem elementary_subgroup_quotient
    {H : Type*} [Group H] (C E D : Subgroup H)
    (hEC : E ≤ C) (hC : IsElementaryAbelian 2 C)
    (hN : (D.subgroupOf E).Normal) :
    let _ := hN
    IsElementaryAbelian 2 (E ⧸ D.subgroupOf E) := by
  let _ := hN
  let _ := hC
  let _ : IsMulCommutative E := .of_setLike_mul_comm fun _ ha _ hb =>
    setLike_mul_comm (hEC ha) (hEC hb)
  refine { toIsMulCommutative := inferInstance
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro w
  obtain ⟨e,rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf E) w
  have he : e ^ 2 = 1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian (e : H) (hEC e.property))
  rw [← map_pow, he, map_one]

private theorem residual_commutator_le_of_quotient_kernel
    {H : Type*} [Group H] (P E D : Subgroup H)
    (hPE : P ≤ Subgroup.normalizer (E : Set H))
    (hN : (D.subgroupOf E).Normal) :
    let _ := hN
    ∀ f : P →* MulAut (E ⧸ D.subgroupOf E),
      (∀ p : P, ∀ e : E,
        f p (QuotientGroup.mk' (D.subgroupOf E) e) =
          QuotientGroup.mk' (D.subgroupOf E)
            ⟨(p : H) * (e : H) * (p : H)⁻¹,
              (Subgroup.mem_normalizer_iff.mp (hPE p.property) e).mp e.property⟩) →
      twoResidualSubgroup P ≤ f.ker → ⁅twoResidualAmbient P,E⁆ ≤ D := by
  let _ := hN
  dsimp only
  intro f hf hker
  apply Subgroup.commutator_le.mpr
  intro r hr e he
  obtain ⟨p,hp,rfl⟩ := hr
  have hpfix : f p = 1 := MonoidHom.mem_ker.mp (hker hp)
  have heq := hf p ⟨e,he⟩
  rw [hpfix] at heq
  have hmem := QuotientGroup.eq_iff_div_mem.mp heq.symm
  change (p : H) * e * (p : H)⁻¹ / e ∈ D at hmem
  simpa only [Subgroup.subtype_apply, commutatorElement_def, div_eq_mul_inv] using hmem

public theorem exists_residual_active_chief_section
    {H : Type*} [Group H] [Finite H] (P C : Subgroup H)
    (hCP : C ≤ P) (hCN : (C.subgroupOf P).Normal)
    (hC : IsElementaryAbelian 2 C)
    (hres : ⁅twoResidualAmbient P,C⁆ ≠ ⊥) :
    ∃ E D : Subgroup H, ∃ _hEC : E ≤ C, ∃ _hDE : D ≤ E,
      ∃ hPE : P ≤ Subgroup.normalizer (E : Set H),
      ∃ _hPD : P ≤ Subgroup.normalizer (D : Set H),
      ∃ hN : (D.subgroupOf E).Normal,
      let _ := hN
      ∃ f : P →* MulAut (E ⧸ D.subgroupOf E),
        (∀ p : P, ∀ e : E,
          f p (QuotientGroup.mk' (D.subgroupOf E) e) =
            QuotientGroup.mk' (D.subgroupOf E)
              ⟨(p : H) * (e : H) * (p : H)⁻¹,
                (Subgroup.mem_normalizer_iff.mp (hPE p.property) e).mp e.property⟩) ∧
        IsElementaryAbelian 2 (E ⧸ D.subgroupOf E) ∧
        (∀ K : Subgroup (E ⧸ D.subgroupOf E),
          (∀ p : P, ∀ w, w ∈ K → f p w ∈ K) → K = ⊥ ∨ K = ⊤) ∧
        ¬twoResidualSubgroup P ≤ f.ker := by
  obtain ⟨E,D,hEC,hDE,hPE,hPD,hactive,hfix,hmax⟩ :=
    select_residual_active_pair P C
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hCP).mp hCN) hres
  have hN : (D.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDE.le).mpr
      ((hEC.trans hCP).trans hPD)
  let _ := hN
  obtain ⟨f,hf⟩ := Subgroup.exists_quotient_conjugation_action P E D hPE hPD hN
  refine ⟨E,D,hEC,hDE.le,hPE,hPD,hN,f,hf,
    elementary_subgroup_quotient C E D hEC hC hN,
    Subgroup.quotient_conjugation_irreducible_of_maximal P E D hDE.le hPE hN hmax f hf,?_⟩
  intro hker
  have hquot := residual_commutator_le_of_quotient_kernel P E D hPE hN f hf hker
  let _ := hC
  have hE : IsElementaryAbelian 2 E := {
    toIsMulCommutative := .of_setLike_mul_comm fun _ ha _ hb =>
      setLike_mul_comm (hEC ha) (hEC hb)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun e =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (e : H) (hEC e.property)) }
  exact hactive (residual_two_layer_kernel P E D hPE hDE.le hE hfix hquot)

end Stellmacher.SectionThree

